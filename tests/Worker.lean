import Uxn.Host

open Uxn Uxn.Host

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def bytes (size : Nat) (get : Nat → UInt8) : ByteArray :=
  ⟨(Array.range size).map get⟩

private def ramBytes (mem : Memory) (address size : Nat) : ByteArray :=
  bytes size fun i => UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 (address + i)))

private def put (address : Nat) (data : ByteArray) : StateT Uxn.Host.State IO Unit :=
  modify fun s => { s with vm := ({ ramWrites := data.data.toList.zipIdx.map fun (b, i) =>
    (BitVec.ofNat 16 (address + i), b.toBitVec) } : Patch).apply s.vm }

private def request (r : Request) : StateT Uxn.Host.State IO r.Result := do
  let reply ← respond (← get).vm.mem r
  modify fun s => { s with vm := reply.patch.apply s.vm }
  return reply.reply

private def word (port : Byte) (value : Nat) : StateT Uxn.Host.State IO Unit :=
  request (.write16 port (BitVec.ofNat 8 value) (BitVec.ofNat 8 (value >>> 8)))

private def select (name : String) : StateT Uxn.Host.State IO Unit := do
  put 0x2000 (name.toUTF8.push 0)
  word Port.File.name 0x2000
  check ((← get).readWord Port.File.success == 0) "select clears success"

private def read (size : Nat) (address := 0x4000) : StateT Uxn.Host.State IO ByteArray := do
  word Port.File.length size
  word Port.File.read address
  let count := ((← get).readWord Port.File.success).toNat
  check (count ≤ min size (0x10000 - address)) "read count exceeds RAM/request"
  return ramBytes (← get).vm.mem address count

private def expect (actual expected : ByteArray) (message : String) : IO Unit :=
  check (actual == expected) message

private def fileTests : StateT Uxn.Host.State IO Unit := do
  expect (← read 3) .empty "read before selecting a name"
  select "a"
  expect (← read 0) .empty "zero-length read"
  expect (← read 2) "ab".toUTF8 "first chunk"
  expect (← read 3 0x5000) "cde".toUTF8 "new destination preserves cursor"
  request (.write8 Port.File.read 0x60)
  check ((← get).readWord Port.File.success == 3) "high-byte-only read write must not trigger a read"
  expect (← read 9) "f".toUTF8 "short final read"
  expect (← read 0) .empty "zero-length read at EOF"
  put 0x4000 "sentinel".toUTF8
  expect (← read 2) .empty "EOF after zero-length read"
  expect (ramBytes (← get).vm.mem 0x4000 8) "sentinel".toUTF8 "EOF changed RAM"
  expect (← read 2) "ab".toUTF8 "read after EOF reopens"
  expect (← read 4) "cdef".toUTF8 "reopened cursor"
  expect (← read 1) .empty "EOF after exact-length read"
  expect (← read 1) "a".toUTF8 "read after exact-length EOF reopens"
  word Port.File.length 2
  word Port.File.name 0x2000
  request (.write8 Port.File.length 1)
  word Port.File.read 0x4000
  check ((← get).readWord Port.File.success == 2) "name reset preserves length; high byte does not commit length"
  expect (ramBytes (← get).vm.mem 0x4000 2) "ab".toUTF8 "latched length read"
  request (.write8 Port.File.lengthLow 2)
  check ((← get).file.length == 0x0102) "low byte commits length"
  word Port.File.name 0x2000
  expect (← read 3) "abc".toUTF8 "same-name write rewinds"
  select "b"
  expect (← read 2) "XY".toUTF8 "different file"
  select "a"
  expect (← read 2) "ab".toUTF8 "returning to a name rewinds"
  -- A high-byte-only name write does not select a new file.
  put 0x2100 ("b".toUTF8.push 0)
  request (.write8 Port.File.name 0x21)
  expect (← read 2) "cd".toUTF8 "high-byte-only name write"
  request (.write8 Port.File.nameLow 0)
  expect (← read 2) "XY".toUTF8 "low-byte name write commits"
  -- Name selection is lazy and retains the RAM address, as in uxn2.
  select "a"
  put 0x2000 ("b".toUTF8.push 0)
  expect (← read 1) "X".toUTF8 "filename memory is read at open"
  put 0x2000 ("a".toUTF8.push 0)
  expect (← read 1) "Y".toUTF8 "open handle ignores later filename edits"
  expect (← read 2) "Z".toUTF8 "short read keeps handle until EOF"
  expect (← read 1) .empty "EOF with edited filename"
  expect (← read 2) "ab".toUTF8 "reopen reads current filename memory"
  select "missing"
  put 0x4000 "sentinel".toUTF8
  expect (← read 8) .empty "missing file"
  expect (ramBytes (← get).vm.mem 0x4000 8) "sentinel".toUTF8 "failure changed RAM"
  IO.FS.writeFile "missing" "now present"
  expect (← read 3) "now".toUTF8 "failed opens may be retried"
  select "empty"
  expect (← read 1) .empty "empty file"
  expect (← read 1) .empty "reopened empty file"
  put 0x2000 ("b".toUTF8.push 0)
  expect (← read 1) "X".toUTF8 "empty file EOF releases handle"
  select "binary"
  expect (← read 5) ⟨#[0, 255, 128, 10, 13]⟩ "binary file bytes"
  select "a"
  put 0 "Z".toUTF8
  put 0xfffe "!!".toUTF8
  expect (← read 10 0xffff) "a".toUTF8 "RAM-end clamp"
  expect (ramBytes (← get).vm.mem 0xfffe 1) "!".toUTF8 "byte before destination"
  expect (ramBytes (← get).vm.mem 0 1) "Z".toUTF8 "RAM read must not wrap"
  expect (← read 1) "b".toUTF8 "clamp must not consume excess file bytes"
  select "a"
  expect (← read 2 0) "ab".toUTF8 "zero-page destination"
  select "large"
  word Port.File.length 0xffff
  -- Inspect the full transfer before applying it: materializing every address
  -- through 65,535 nested Function.update closures would take quadratic time.
  let reply ← respond (← get).vm.mem (.write16 Port.File.read 1 0)
  check ((← get).readWord Port.File.success == 0xffff) "maximum read success"
  check (reply.patch.ramWrites == (List.range 0xffff).map fun i =>
    (BitVec.ofNat 16 (i + 1), BitVec.ofNat 8 i)) "maximum read address and data"
  expect (← read 2) ⟨#[255]⟩ "remaining byte after maximum read"
  expect (← read 2) .empty "large file EOF"
  -- An unterminated name cannot wrap into zero page looking for its terminator.
  put 0xffff "a".toUTF8
  word Port.File.name 0xffff
  expect (← read 1) .empty "unterminated name at RAM end"
  put 0xffff ⟨#[0]⟩
  word Port.File.name 0xffff
  expect (← read 1) .empty "empty name"
  put 0x2000 ⟨#[255, 0]⟩
  word Port.File.name 0x2000
  expect (← read 1) .empty "invalid UTF-8 name"
  -- File vectors are passive registers; other operations are not implemented.
  word 0xa0 0xdead
  select "a"
  expect (← read 1) "a".toUTF8 "file read invokes no vector"
  check ((← get).readWord 0xa0 == 0xdead) "file vector storage"
  request (.write8 0xa6 1)
  word 0xae 0x4000
  expect (← IO.FS.readBinFile "a") "abcdef".toUTF8 "unsupported writes/deletes changed file"

private def directoryTests : StateT Uxn.Host.State IO Unit := do
  select "listing"
  let listing ← read 0xffff
  let lines := (String.fromUTF8! listing).splitOn "\n" |>.filter (· != "")
  check (lines.length == 6) "directory listing entry count"
  for line in ["0002\ta.txt", "----\tfolder/", "????\tbig", "0003\té", "0000\t.dot", "!!!!\tbroken"] do
    check (lines.contains line) s!"directory missing {line}"
  for chunk in [1, 2, 3, 4, 5, 7, 8, 16] do
    select "listing"
    let mut actual := ByteArray.empty
    for _ in [:listing.size + 1] do
      let next ← read chunk
      if next.isEmpty then break
      actual := actual ++ next
    expect actual listing s!"directory chunk size {chunk}"
    expect (← read 10) (listing.extract 0 10) "read after directory EOF reopens"
  select "listing"
  expect (← read 0) .empty "zero directory read"
  expect (← read 5) (listing.extract 0 5) "zero directory read consumed bytes"
  IO.FS.writeFile "listing/new" "!"
  expect (← read 0xffff) (listing.extract 5 listing.size) "directory snapshot changed while open"
  expect (← read 0) .empty "zero-length directory read at EOF"
  expect (← read 1) .empty "directory EOF after zero-length read"
  let refreshed ← read 0xffff
  check ((String.fromUTF8! refreshed).contains "0001\tnew\n") "EOF did not refresh directory"
  select "empty-dir"
  expect (← read 1) .empty "empty directory"
  expect (← read 1) .empty "reopened empty directory"
  put 0x2000 ("a".toUTF8.push 0)
  expect (← read 1) "a".toUTF8 "empty directory EOF releases handle"
  select "listing"
  expect (← read 1 0xffff) (refreshed.extract 0 1) "directory RAM-end clamp"
  expect (← read 1) (refreshed.extract 1 2) "directory clamp consumed excess bytes"

private def statTests : IO Unit := do
  for (name, width, expected) in [
      ("a", 0, ""), ("a", 1, "6"), ("a", 4, "0006"),
      ("hex", 2, "??"), ("hex", 3, "abc"), ("hex", 4, "0abc"),
      ("large", 1, "?"), ("large", 4, "????"), ("large", 5, "10000"),
      ("limit", 4, "ffff"), ("sparse", 8, "????????"), ("sparse", 9, "100000000"),
      ("listing", 0, ""), ("listing", 3, "---"),
      ("absent", 0, ""), ("absent", 5, "!!!!!"), ("empty", 4, "0000")] do
    expect (← File.stat name width).val expected.toUTF8 s!"stat {name} width {width}"
  -- Length equality is available from the return type without executing a proof tactic over IO.
  let result ← File.stat "a" 0x10000
  have : result.val.size = 0x10000 := result.property
  check (result.val.size == 0x10000 && result.val[0xffff]'(by omega) == '6'.toUInt8) "wide stat field"

private def liveMemoryTest : IO Unit := do
  -- Construct the filename during execution, then use newly read RAM immediately.
  let rom : ByteArray := ⟨#[
    0x80, 97, 0xa0, 2, 0, 0x15,
    0xa0, 2, 0, 0x80, 0xa8, 0x37,
    0xa0, 0, 1, 0x80, 0xaa, 0x37,
    0xa0, 3, 0, 0x80, 0xac, 0x37,
    0xa0, 3, 0, 0x14, 0]⟩
  let host ← (initialState rom).run
  check (host.vm.mem.wstk.ptr == 1 && host.vm.mem.wstk.data 0 == 97 &&
    host.readWord Port.File.success == 1) "device request must use live memory and resume with its patch"

private def unitTests : IO Unit := do
  statTests
  discard <| fileTests.run (initialState .empty)
  discard <| directoryTests.run (initialState .empty)
  liveMemoryTest
  for name in ["../outside", "escape", "../unit-sibling/file"] do
    discard <| (do
      select name
      expect (← read 1) .empty s!"outside working directory: {name}").run (initialState .empty)
  IO.println "PASS File: stats, file/directory cursors, boundaries, errors, live RAM, path confinement"

-- UXNDIFF1: shared by C comparisons and the nested-interpreter tests.
private def bigEndian (value size : Nat) : ByteArray :=
  bytes size fun i => (value >>> (8 * (size - i - 1))).toUInt8

private def snapshot (fuel : Nat) (host : Uxn.Host.State) : ByteArray :=
  "UXNDIFF1".toUTF8 ++ bigEndian (host.fuel == some 0).toNat 1 ++ bigEndian host.vm.pc.toNat 2 ++
  bigEndian (fuel - host.fuel.getD fuel) 8 ++ bigEndian host.vm.mem.wstk.ptr.toNat 1 ++
  bigEndian host.vm.mem.rstk.ptr.toNat 1 ++ bigEndian host.consoleVector.toNat 2 ++
  bytes 0x100 (fun i => UInt8.ofBitVec (host.read (BitVec.ofNat 8 i))) ++
  ramBytes host.vm.mem 0 0x10000 ++
  bytes 0x100 (fun i => UInt8.ofBitVec (host.vm.mem.wstk.data (BitVec.ofNat 8 i))) ++
  bytes 0x100 (fun i => UInt8.ofBitVec (host.vm.mem.rstk.data (BitVec.ofNat 8 i)))

private def hostTests : IO Unit := do
  -- Four instructions: push a value and address, store, then BRK.
  let rom : ByteArray := ⟨#[0x80, 42, 0x80, 0x90, 0x11, 0]⟩
  let initial := initialState rom
  let some action := initial.next | throw (IO.userError "reset has no next step")
  let once ← action
  check (once.vm.pc == 0x102 && once.vm.mem.wstk.ptr == 1 &&
    once.vm.mem.wstk.data 0 == 42 && once.vm.mem.ram 0x90 == 0) "next executes one instruction"
  let paused ← initial.run (some 2)
  check (paused.fuel == some 0 && paused.next.isSome &&
    paused.vm.pc == 0x104 && paused.vm.mem.ram 0x90 == 0) "pause retains the next instruction"
  let finished ← initial.run (some 4)
  check (finished.fuel == some 0 && finished.next.isNone &&
    finished.vm.mem.ram 0x90 == 42) "exact-budget completion is distinguishable from a pause"
  expect (snapshot 0 (← paused.run)) (snapshot 0 (← (initialState rom).run))
    "resume after storing operands"
  check ((← (initialState rom).run (some 0)).next.isSome) "zero budget is not completion"
  expect (snapshot 4 (← finished.run (some 0))) (snapshot 4 finished)
    "completed states stay completed"

  -- The callback counts events and sets System/state on type 4. Two arguments
  -- generate A, B, newline, C, newline, then the final callback despite halt.
  -- No stdin read is needed, so restarting the host or losing a continuation
  -- changes either the event count, the final snapshot, or termination.
  let callbacks : ByteArray := ⟨#[
    0xa0, 0x01, 0x07, 0x80, 0x10, 0x37, 0,
    0x80, 0x80, 0x10, 0x01, 0x80, 0x80, 0x11,
    0x80, 0x17, 0x16, 0x80, 4, 0x08, 0x80, 0x0f, 0x17, 0]⟩
  let initial := initialState callbacks ["AB", "C"]
  let final ← initial.run
  check (final.vm.mem.ram 0x80 == 6 && final.read Port.System.state == 1 &&
    final.next.isNone) "arguments and the final halt callback"
  for budget in [0, 1, 3, 4, 5, 15, 16, 17, 28, 40, 64, 75, 76, 77] do
    expect (snapshot 0 (← (← initial.run (some budget)).run))
      (snapshot 0 final)
      s!"callback pause/resume at instruction {budget}"
  for (args, count) in [(["", "C"], 4), ([String.ofList ['A', Char.ofNat 0, 'B'], "C"], 5)] do
    check ((← (initialState callbacks args).run).vm.mem.ram 0x80 == count)
      "empty and NUL-terminated arguments"

  IO.FS.writeBinFile "host.rom" rom
  let loaded ← file "host.rom"
  check (loaded.vm.pc == 0x100 && loaded.vm.mem.ram 0x90 == 0) "loading does not execute reset"
  expect (snapshot 0 (← loaded.run)) (snapshot 0 (← (initialState rom).run))
    "file and image entry points"
  check ((← load (← IO.FS.Handle.mk "host.rom" .read) (limit := 0)).vm.mem.ram 0x100 == 0)
    "shared loader honors the read limit"
  expect (snapshot 4 (← (← file "host.rom").run (some 4))) (snapshot 4 finished)
    "loading does not spend instruction fuel"
  IO.FS.writeBinFile "host.rom" callbacks
  let loaded ← (← file "host.rom" ["AB", "C"]).run (some 0)
  check (loaded.vm.pc == 0x100 && loaded.read Port.Console.type == 1)
    "zero instruction budget still loads the ROM and its arguments"
  IO.FS.removeFile "host.rom"
  expect (snapshot 0 (← loaded.run)) (snapshot 0 final) "resuming does not reopen the ROM"
  match ← (file "host.rom").toBaseIO with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "loading failure was swallowed")
  IO.println "PASS Host: single steps, completion, budgets, callback pause/resume, argument boundaries, loading"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--unit"] => unitTests; hostTests; return 0
  | "--run" :: rom :: output :: fuel :: args =>
    let some fuel := fuel.toNat? | throw (IO.userError "invalid instruction budget")
    let host ← (initialState (← IO.FS.readBinFile rom) args).run (some fuel)
    IO.FS.writeBinFile output (snapshot fuel host)
    return host.exitCode
  | _ => throw (IO.userError "test worker: invoke python3 tests/run.py")
