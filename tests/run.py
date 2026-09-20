#!/usr/bin/env python3
"""Run the offline test suite; use --extended for nested-interpreter comparisons."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import struct
import subprocess
import tempfile
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
EXAMPLES = ROOT / "examples"
SELFHOST = ROOT / "ProgramProofs/Uxnmin"
WORKER = ROOT / ".lake/build/bin/test-worker"
CLI = ROOT / ".lake/build/bin/uxn"
MASK = (1 << 64) - 1
GAMMA = 0x9e3779b97f4a7c15
# UXNDIFF1 is also written by Worker.lean and reference.c.
FIELDS = [("header", 8), ("bounded", 1), ("pc", 2), ("steps", 8),
          ("wptr", 1), ("rptr", 1), ("console vector", 2), ("ports", 256),
          ("ram", 65536), ("wstack", 256), ("rstack", 256)]


@dataclass
class Case:
    name: str
    rom: bytes
    data: bytes = b""
    args: tuple = ()
    fuel: int = 10000
    expected: tuple | None = None  # exit code, stdout, stderr of a completed run


@dataclass
class Result:
    code: int | None
    stdout: bytes
    stderr: bytes
    state: bytes = b""
    problem: str = ""


def same(actual, expected, label):
    if actual == expected:
        return
    if isinstance(actual, bytes) and isinstance(expected, bytes):
        offset = next((i for i, (a, b) in enumerate(zip(actual, expected)) if a != b),
                      min(len(actual), len(expected)))
        raise AssertionError(f"{label}: byte {offset}: {actual[offset:offset+8].hex()} != "
                             f"{expected[offset:offset+8].hex()} (lengths {len(actual)}/{len(expected)})")
    raise AssertionError(f"{label}: {actual!r} != {expected!r}")


def process(args, data=b"", cwd=None, timeout=120, check=False):
    try:
        completed = subprocess.run(args, input=data, capture_output=True, cwd=cwd, timeout=timeout)
        result = Result(completed.returncode, completed.stdout, completed.stderr)
    except subprocess.TimeoutExpired as error:
        result = Result(None, error.stdout or b"", error.stderr or b"",
                        problem=f"exceeded {timeout:g}s watchdog (inconclusive)")
    if check:
        same(result.problem, "", str(args))
        same(result.code, 0, f"{args}; stderr={result.stderr!r}; stdout={result.stdout!r}")
    return result


def fields(state):
    offset = 0
    result = {}
    for name, size in FIELDS:
        result[name] = state[offset:offset + size]
        offset += size
    return result


def guest(executable, directory, rom, data=b"", args=(), fuel=10000, timeout=120):
    state = directory / (executable.name + ".state")
    state.unlink(missing_ok=True)
    command = ([executable, "--run", rom, state, str(fuel), *args] if executable == WORKER else
               [executable, "--dump-state", state, "--fuel", str(fuel), "--", rom, *args])
    result = process(command, data, directory, timeout)
    result.state = state.read_bytes() if state.exists() else b""
    if result.code is not None and result.code < 0:
        result.problem = f"terminated by signal {-result.code}"
    if not result.problem and (len(result.state) != 66327 or
                              result.state[:8] != b"UXNDIFF1" or result.state[8] > 1):
        result.problem = "missing, truncated, or unsupported VM snapshot"
    return result


def mix(value):
    value = ((value ^ (value >> 30)) * 0xbf58476d1ce4e5b9) & MASK
    value = ((value ^ (value >> 27)) * 0x94d049bb133111eb) & MASK
    return value ^ (value >> 31)


def random_case(seed, index, fuel):
    # Preserve the original splitmix64-v2 byte stream and independent case indices.
    state = mix(seed ^ mix((index + GAMMA) & MASK))

    def draw():
        nonlocal state
        state = (state + GAMMA) & MASK
        return mix(state)

    size = ([0, 1, 2, 3, 255, 256, 4096, 0xff00][draw() % 8] if draw() % 2 == 0
            else draw() % 0xff01)
    return Case(f"random-{index}", bytes(draw() & 255 for _ in range(size)), fuel=fuel)


def regressions():
    echo = bytes.fromhex("a0 01 07 80 10 37 00 80 12 16 80 18 17 00")
    cases = [Case(name, bytes.fromhex(rom), fuel=fuel) for name, rom, fuel in [
        ("multiply-wrap", "a0 ff ff a0 ff ff 3a 00", 10000),
        ("relative-load-wrap", "80 12 80 00 11 80 80 a0 00 00 2c", 10000),
        ("relative-store-wrap", "80 13 80 00 11 a0 55 80 a0 00 00 2c", 10000),
        ("binary-output", "a0 00 18 17 a0 ff 18 17 a0 80 19 17 a0 00 19 17 00", 10000),
        ("device-short-wrap", "a0 12 34 80 ff 37 80 ff 36 00", 10000),
        ("short-output-callback", "a0 41 42 80 18 37 00", 10000),
        ("popped-stack-bytes", "a0 12 34 22 e0 56 78 62 00", 10000),
        ("zero-fuel", "80 42", 0), ("exact-brk-budget", "00", 1),
        ("bounded-loop", "40 ff fd", 100), ("bounded-output", "a0 ff 18 17 40 ff f9", 101),
        ("guest-exit", "a0 83 0f 17 80 55 00", 10000)]]
    return cases + [Case("binary-input", echo, bytes([0, 255, 128, 65]))] + [
        Case(f"console-budget-{fuel}", echo, b"Z", ("A", "B"), fuel) for fuel in [3, 4, 8, 9, 14, 24]]


def examples(manifest):
    programs = {p["name"]: p for p in manifest["programs"]}
    return [Case(c["name"], (EXAMPLES / programs[c["program"]]["rom"]).read_bytes(),
                 (EXAMPLES / c["stdin"]).read_bytes() if c["stdin"] else b"", tuple(c["args"]),
                 c["fuel"], (c["exit_code"], (EXAMPLES / c["stdout"]).read_bytes(),
                             (EXAMPLES / c["stderr"]).read_bytes())) for c in manifest["cases"]]


def assemble(reference, source):
    result = process([reference, EXAMPLES / "binaries/drifloon.rom"], source, check=True)
    if b"Assembled in " not in result.stderr:
        raise AssertionError(f"assembly did not complete: {result.stderr!r}")
    return result.stdout


def corpus(reference, manifest, cases, timeout):
    same(manifest["format_version"], 1, "example manifest version")
    for spec in manifest["programs"] + manifest["cases"]:
        for name in ("source", "rom", "stdin", "stdout", "stderr"):
            if name in spec:
                data = (EXAMPLES / spec[name]).read_bytes() if spec[name] else b""
                same(hashlib.sha256(data).hexdigest(), spec[name + "_sha256"], f"{spec['name']} {name} hash")
    for spec in json.loads((HERE / "upstream/manifest.json").read_text()):
        same(hashlib.sha256((HERE / "upstream" / spec["file"]).read_bytes()).hexdigest(),
             spec["sha256"], spec["file"] + " hash")
    for program in manifest["programs"]:
        same(assemble(reference, (EXAMPLES / program["source"]).read_bytes()),
             (EXAMPLES / program["rom"]).read_bytes(), "rebuild " + program["name"])
    provenance = json.loads((SELFHOST / "provenance.json").read_text())
    for name, suffix in [("source", "tal"), ("rom", "rom")]:
        same(hashlib.sha256((SELFHOST / f"uxnmin.{suffix}").read_bytes()).hexdigest(),
             provenance[name + "_sha256"], "self-hosted " + name + " hash")
    same(assemble(reference, (SELFHOST / "uxnmin.tal").read_bytes()),
         (SELFHOST / "uxnmin.rom").read_bytes(), "rebuild self-hosted uxnmin")
    # Complete C runs retain every golden check even when a Lean snapshot needs a lower budget.
    with tempfile.TemporaryDirectory(prefix="uxn-corpus-") as temp:
        rom = Path(temp) / "program.rom"
        for case in cases:
            rom.write_bytes(case.rom)
            # Keep complete CLI runs short; longer Lean runs have instruction
            # budgets in the differential campaign below.
            for executable in ((reference, CLI) if case.fuel <= 100000 else (reference,)):
                result = process([executable, rom, *case.args], case.data, temp, timeout)
                same(result.problem, "", case.name)
                golden(result, case.expected, f"{executable.name}: {case.name}")
    print(f"PASS corpus: {len(manifest['programs'])} example ROM rebuilds + self-hosted ROM, "
          f"{len(cases)} C / {sum(c.fuel <= 100000 for c in cases)} CLI expected outputs", flush=True)


def golden(result, expected, label):
    for name, actual, wanted in zip(("exit", "stdout", "stderr"),
                                    (result.code, result.stdout, result.stderr), expected):
        same(actual, wanted, label + " " + name)


def save_failure(case, results, error, config):
    (HERE / "failures").mkdir(exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix=f"{os.getpid()}-", dir=HERE / "failures"))
    metadata = dict(name=case.name, args=case.args, fuel=case.fuel,
                    seed=config.seed, generator="splitmix64-v2")
    if case.expected is not None:
        metadata["expected"] = [case.expected[0], case.expected[1].hex(), case.expected[2].hex()]
    (directory / "case.json").write_text(json.dumps(metadata, indent=2) + "\n")
    (directory / "program.rom").write_bytes(case.rom)
    (directory / "stdin.bin").write_bytes(case.data)
    for name, result in results.items():
        for field in ("state", "stdout", "stderr"):
            (directory / f"{name}.{field}").write_bytes(getattr(result, field))
    (directory / "failure.txt").write_text(str(error) + "\n" + "\n".join(
        f"{name}: exit={r.code}, problem={r.problem}" for name, r in results.items()) + "\n")
    for path in [HERE / "reference.c", HERE / "Worker.lean", HERE / "run.py",
                 *sorted((ROOT / "Uxn").rglob("*.lean")), ROOT / "lean-toolchain"]:
        target = directory / path.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    return shlex.join(["python3", str(HERE / "run.py"), "--replay", str(directory / "case.json"),
                       "--timeout-ms", str(config.timeout_ms)])


def compare(case, reference, config):
    with tempfile.TemporaryDirectory(prefix="uxn-case-") as temp:
        directory = Path(temp)
        rom = directory / "program.rom"
        rom.write_bytes(case.rom)
        results = {}
        try:
            for name, executable in [("lean", WORKER), ("reference", reference)]:
                results[name] = guest(executable, directory, rom, case.data, case.args,
                                      case.fuel, config.timeout_ms / 1000)
            for name, result in results.items():
                same(result.problem, "", name)
            lean, reference_result = results.values()
            golden(lean, (reference_result.code, reference_result.stdout, reference_result.stderr), "C comparison")
            reference_fields = fields(reference_result.state)
            for name, data in fields(lean.state).items():
                same(data, reference_fields[name], name)
            bounded = lean.state[8] == 1
            if not bounded and case.expected is not None:
                golden(lean, case.expected, "expected")
            return bounded
        except (AssertionError, OSError) as error:
            raise RuntimeError(f"FAIL {case.name}: {error}\nReplay: " +
                               save_failure(case, results, error, config)) from error


def campaign(fixed, reference, config):
    total = len(fixed) + config.count
    print(f"{len(fixed)} fixed + {config.count} random; seed={config.seed}, fuel cap={config.fuel}", flush=True)
    indices = iter(range(total))
    completed = bounded = 0

    def run_index(index):
        case = fixed[index] if index < len(fixed) else random_case(config.seed, index - len(fixed), config.fuel)
        return compare(case, reference, config)

    with ThreadPoolExecutor(max_workers=config.jobs) as pool:
        pending = set()
        while pending or completed < total:
            for _ in range(config.jobs - len(pending)):
                index = next(indices, None)
                if index is None:
                    break
                pending.add(pool.submit(run_index, index))
            done, pending = wait(pending, return_when=FIRST_COMPLETED)
            for result in done:
                bounded += result.result()
                completed += 1
            if completed % 100 == 0 and completed < total:
                print(f"Matched {completed}/{total}", flush=True)
    print(f"Matched {total}: {completed - bounded} completed, {bounded} bounded.", flush=True)


def symbols(reference, source, names):
    # Extract addresses separately; execute the ROM assembled from the original source.
    original = assemble(reference, source)
    annotated = assemble(reference, source + b"\n" + " ".join("=" + n for n in names).encode() + b" ff\n")
    same(annotated[:len(original)], original, "symbol extraction changed ROM")
    same(annotated[-2:], b"\xff\x00", "symbol table trailer")
    return original, dict(zip(names, struct.unpack(">" + "H" * len(names), annotated[-2 * len(names) - 2:-2])))


def unit_tests(base, timeout):
    directory = base / "unit"
    directory.mkdir()
    for name in ["empty-dir", "listing/folder"]:
        (directory / name).mkdir(parents=True)
    for name, data in {"a": b"abcdef", "b": b"XYZ", "empty": b"", "binary": bytes([0, 255, 128, 10, 13]),
                       "large": bytes(range(256)) * 256, "limit": bytes(65535), "hex": bytes(0xabc),
                       "listing/a.txt": b"hi", "listing/é": b"xyz", "listing/.dot": b"",
                       "listing/big": bytes(65536)}.items():
        (directory / name).write_bytes(data)
    (base / "outside").write_bytes(b"outside")
    (base / "unit-sibling").mkdir()
    (base / "unit-sibling/file").write_bytes(b"outside")
    (directory / "escape").symlink_to(base / "outside")
    (directory / "listing/broken").symlink_to("absent")
    with (directory / "sparse").open("wb") as file:
        file.truncate(1 << 32)
    print(process([WORKER, "--unit"], cwd=directory, timeout=timeout, check=True).stdout.decode().strip(), flush=True)


def cli_tests(base, timeout):
    directory = base / "cli"
    directory.mkdir()
    for args, stdout, stderr in [
            ([], f"usage: {CLI} file.rom [args..]\n".encode(), b""),
            (["missing.rom"], b"", f"{CLI}: missing.rom not found.\n".encode())]:
        result = process([CLI, *args], cwd=directory, timeout=timeout)
        same(result.problem, "", "CLI argument error")
        golden(result, ((len(stdout) + len(stderr)) & 0xff, stdout, stderr), "CLI argument error")
    rom = base / "echo.rom"
    rom.write_bytes(next(c.rom for c in regressions() if c.name == "binary-input"))
    for path in [rom, "../echo.rom"]:
        result = process([CLI, path, "A", ""], b"\x00\xffZ", directory, timeout)
        same(result.problem, "", "CLI path outside working directory")
        golden(result, (0, b"A\n\n\x00\xffZ\n", b""), "CLI loading, arguments and binary stdin")
    result = process([CLI, "."], cwd=directory, timeout=timeout)
    same(result.problem, "", "CLI read error")
    same(result.code != 0 and b"not found" not in result.stderr, True,
         "CLI read failures must not be reported as open failures")
    print("PASS CLI: usage, open/read errors, unrestricted ROM paths, arguments and binary stdin", flush=True)


def file_examples(base, reference, timeout):
    directory = base / "file"
    directory.mkdir()
    rom = directory / "program.rom"
    (directory / "test.txt").write_bytes(bytes.fromhex("12345678"))
    upstream = (HERE / "upstream/varvara.file.tal").read_bytes()

    def run(source):
        rom.write_bytes(assemble(reference, source))
        result = guest(WORKER, directory, rom, fuel=2000000, timeout=timeout)
        same(result.problem, "", "File example")
        same(result.state[8], 0, "File example exhausted instruction budget (inconclusive)")
        same(result.code, 0, "File example exit")
        same(result.stderr, b"", "File example stderr")
        return result

    for label in ["read", "read-of", "dir-spacer", "dir-partial"]:
        # Retain the upstream test functions, replacing only their startup and write fixtures.
        start = f"@on-reset ( -> )\n#800f DEO\n;dict/{label} file/test-{label} <test>\nBRK\n".encode()
        result = run(upstream[:upstream.index(b"@on-reset")] + start + upstream[upstream.index(b"@meta "):])
        same(result.stdout.endswith(b": pass\n") and b"fail" not in result.stdout, True, label)
    source = (HERE / "sources/read-spec.tal").read_bytes()
    _, labels = symbols(reference, source, ["buffer"])
    (directory / "in.txt").write_bytes(b"0123456789abcdefEXTRA")
    result = run(source)
    same(result.stdout, b"", "spec read stdout")
    same(fields(result.state)["ram"][labels["buffer"]:labels["buffer"] + 16], b"0123456789abcdef", "spec read buffer")
    for data, expected in [(bytes.fromhex("a00180800637"), b"\x01"), (b"abcdef", b"\x00")]:
        (directory / "meta.rom").write_bytes(data)
        same(run((HERE / "sources/metadata.tal").read_bytes()).stdout, expected, "metadata reader")
    print("PASS File ROMs: four upstream tests, specification read, two metadata cases", flush=True)


def nested_interpreter(directory, reference):
    binary, labels = symbols(reference, (SELFHOST / "uxnmin.tal").read_bytes(),
                             ["rom/mem", "wst/buf", "rst/buf", "pc/addr", "vm/on-console"])
    interpreter = directory / "uxnmin.rom"
    interpreter.write_bytes(binary)
    return interpreter, labels


def same_guest(direct, nested, labels, name):
    golden(nested, (direct.code, direct.stdout, direct.stderr), name)
    direct, nested = fields(direct.state), fields(nested.state)
    memory = nested["ram"]
    same(memory[labels["pc/addr"]:labels["pc/addr"] + 2], direct["pc"], name + " guest PC")
    for stack, pointer, symbol in [("wstack", "wptr", "wst/buf"), ("rstack", "rptr", "rst/buf")]:
        address = labels[symbol]
        same(memory[address:address + 257], direct[stack] + direct[pointer], name + " " + stack)
    # The nested interpreter's own code/stacks occupy the remainder of host RAM.
    address = labels["rom/mem"]
    same(memory[address:], direct["ram"][:65536 - address], name + " guest RAM")


def nested_console(base, reference, timeout):
    directory = base / "console"
    directory.mkdir()
    interpreter, labels = nested_interpreter(directory, reference)
    echo = "@on-console #12 DEI #18 DEO BRK"
    clear = "@on-console #12 DEI #18 DEO #0000 #10 DEO2 BRK"
    # Inactive guests must return with the pipe still open, leaving its bytes unread.
    # Active guests must retain argument/input/EOF delivery, including after vector clearing.
    cases = [
        ("brk", "BRK", (), False, False, 0, b""),
        ("brk-eof", "BRK", (), False, True, 0, b""),
        ("brk-arguments", "BRK", ("A", "B"), False, False, 0, b""),
        ("output-brk", "#5118 DEO BRK", (), False, False, 0, b"Q"),
        ("zero-vector", "#0000 #10 DEO2 BRK", (), False, False, 0, b""),
        ("clear-before-brk", ";on-console #10 DEO2 #0000 #10 DEO2 BRK " + echo,
         (), False, False, 0, b""),
        ("unlatched-vector", "#01 #10 DEO BRK", (), False, False, 0, b""),
        ("exit-code", "#830f DEO BRK", (), False, False, 3, b""),
        ("echo", ";on-console #10 DEO2 BRK " + echo, (), True, True, 0, b"abc\n"),
        ("arguments", ";on-console #10 DEO2 BRK " + echo,
         ("A", "B"), True, True, 0, b"A\nB\nabc\n"),
        ("cached-vector", ";on-console #10 DEO2 #00 #10 DEO BRK |0200 " + echo,
         (), True, True, 0, b"abc\n"),
        ("clear-in-argument", ";on-console #10 DEO2 BRK " + clear,
         ("A",), True, True, 0, b"A"),
        ("clear-in-input", ";on-console #10 DEO2 BRK " + clear,
         (), True, True, 0, b"a"),
    ]
    for name, source, args, active, eof, code, output in cases:
        rom = directory / "guest.rom"
        rom.write_bytes(assemble(reference, ("|0100 " + source).encode()))
        results = []
        for mode in ["reference", "direct", "nested"]:
            state = directory / f"{mode}.state"
            command = ([reference, "--dump-state", state, "--fuel", "2000000", "--", rom, *args]
                       if mode == "reference" else
                       [WORKER, "--run", interpreter if mode == "nested" else rom, state, "2000000",
                        *(["guest.rom"] if mode == "nested" else []), *args])
            read_fd, write_fd = os.pipe()
            with os.fdopen(read_fd, "rb", buffering=0) as reader, os.fdopen(write_fd, "wb", buffering=0) as writer:
                writer.write(b"abc")
                if eof:
                    writer.close()
                with subprocess.Popen(command, stdin=reader, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                      cwd=directory) as child:
                    try:
                        stdout, stderr = child.communicate(timeout=timeout)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        child.communicate()
                        raise AssertionError(f"{name} {mode}: did not return with stdin {'closed' if eof else 'open'}; "
                                             f"command: {shlex.join(map(str, command))}")
                writer.close()
                same(reader.read(), b"" if active else b"abc", name + " " + mode + " unread stdin")
            result = Result(child.returncode, stdout, stderr, state.read_bytes())
            same(len(result.state), 66327, name + " snapshot size")
            same(result.state[8], 0, name + " exhausted instruction budget (inconclusive)")
            golden(result, (code, output, b""), name + " " + mode)
            results.append(result)
        same(results[1].state, results[0].state, name + " direct C comparison")
        same_guest(results[1], results[2], labels, name)
        same(int.from_bytes(fields(results[2].state)["console vector"], "big"),
             labels["vm/on-console"] if active else 0, name + " outer console vector")
    print(f"PASS nested console: {len(cases)} startup, input-consumption, callback and exit cases", flush=True)


def nested_examples(base, reference, timeout):
    directory = base / "nested"
    directory.mkdir()
    interpreter, labels = nested_interpreter(directory, reference)
    programs = ["hello_world", "stack", "numbers", "functions", "variables", "if_else", "loops",
                "objects", "reverse_string"]
    for name, data in [(name, b"") for name in programs] + [("fibonacci", bytes([n])) for n in range(7)]:
        start = time.monotonic()
        rom = directory / "guest.rom"
        rom.write_bytes((EXAMPLES / f"binaries/{name}.rom").read_bytes())
        direct = guest(WORKER, directory, rom, data, fuel=2000000, timeout=timeout)
        nested = guest(WORKER, directory, interpreter, data, ["guest.rom"], 2000000, timeout)
        for result in (direct, nested):
            same(result.problem, "", name)
            same(result.state[8], 0, name + " exhausted instruction budget (inconclusive)")
        same_guest(direct, nested, labels, name)
        print(f"PASS nested {name}{tuple(data)} ({time.monotonic() - start:.2f}s)", flush=True)


def natural(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("count", nargs="?", type=natural, default=0, help="additional random cases")
    parser.add_argument("--seed", type=natural, default=int(time.time()))
    parser.add_argument("--fuel", type=natural, default=10000, help="differential instruction cap")
    parser.add_argument("--jobs", type=natural, default=1)
    parser.add_argument("--timeout-ms", type=natural, default=120000, help="per-process watchdog")
    parser.add_argument("--random-only", action="store_true", help="run only the random campaign")
    parser.add_argument("--replay", help="fixed case name or saved case.json (including old failures)")
    parser.add_argument("--extended", action="store_true", help="also run 16 slow nested-interpreter comparisons")
    parser.add_argument("--skip-proofs", action="store_true", help="test runtime behavior without building ProgramProofs")
    config = parser.parse_args()
    if config.jobs == 0 or config.seed > MASK or config.fuel > MASK:
        parser.error("jobs must be positive; seed and fuel must fit in 64 bits")
    if sum([config.random_only, bool(config.replay), config.extended]) > 1:
        parser.error("--random-only, --replay, and --extended are mutually exclusive")
    routine = not (config.random_only or config.replay)
    targets = ["test-worker"]
    if routine:
        targets += ["uxn", "ProgramProofs.Uxnmin.Correctness"]
        if not config.skip_proofs:
            targets.append("ProgramProofs")
    process(["lake", "build", *targets], cwd=ROOT, timeout=None, check=True)
    with tempfile.TemporaryDirectory(prefix="uxn-tests-") as temp:
        base = Path(temp)
        reference = base / "reference"
        process([*shlex.split(os.environ.get("CC", "cc")), "-std=c99", "-Wall", "-Wextra", "-O2",
                 HERE / "reference.c", "-o", reference], check=True)
        fixed = []
        if config.replay and Path(config.replay).is_file():
            path = Path(config.replay)
            spec = json.loads(path.read_text())
            expected = spec.get("expected")
            fixed = [Case(spec["name"], (path.parent / "program.rom").read_bytes(),
                          (path.parent / "stdin.bin").read_bytes(), tuple(spec["args"]), spec["fuel"],
                          (expected[0], bytes.fromhex(expected[1]), bytes.fromhex(expected[2])) if expected else None)]
            config.seed = spec["seed"]
            config.fuel = spec["fuel"]
        elif not config.random_only:
            manifest = json.loads((EXAMPLES / "manifest.json").read_text())
            fixed = examples(manifest)
            if routine:
                print("PASS build: " + ", ".join(targets), flush=True)
                if config.skip_proofs:
                    print("SKIP ProgramProofs build (--skip-proofs)", flush=True)
                corpus(reference, manifest, fixed, config.timeout_ms / 1000)
                same(compare(next(c for c in fixed if c.name == "opctest"), reference, config),
                     False, "canon opcode test exhausted instruction budget (inconclusive)")
                print("PASS canon opcode test: completed, output and full VM state match C", flush=True)
                unit_tests(base, config.timeout_ms / 1000)
                cli_tests(base, config.timeout_ms / 1000)
                file_examples(base, reference, config.timeout_ms / 1000)
                nested_console(base, reference, config.timeout_ms / 1000)
            fixed += regressions()
            for case in fixed:
                case.fuel = min(case.fuel, config.fuel)
            if config.replay:
                fixed = [c for c in fixed if c.name == config.replay]
                if not fixed:
                    parser.error(f"unknown case or replay file: {config.replay}")
        if config.replay:
            config.count = 0
        if any(len(c.rom) > 0xff00 or not 0 <= c.fuel <= MASK for c in fixed):
            parser.error("invalid ROM size or instruction budget")
        campaign(fixed, reference, config)
        if config.extended:
            nested_examples(base, reference, config.timeout_ms / 1000)


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError, RuntimeError) as error:
        raise SystemExit(str(error))
