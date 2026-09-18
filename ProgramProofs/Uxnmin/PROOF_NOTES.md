# uxnmin correctness proof

## Statement and scope

`ProgramProofs.Uxnmin.correct` states that after loading a file containing the guest program, a finite native execution reaches a state related to the direct guest execution by a ranked simulation. The filename bounds, file-read IO equation, confinement hypothesis, device-compatibility hypothesis, conclusion, and semantic definitions are unchanged.

The transition system is the one in the original theorem: `next` steps `Host.step` during a single reset evaluation and stops at BRK or an IO error. Its label is the IO world or error. The theorem does not cover the host's subsequent input-event loop. The two host records and two VM states need not be equal.

## Proof structure

1. **Run the actual loader.** `InitialBoundary.loaded_boundary` delivers every filename byte through `Host.run.consoleArgs`. Seven reset instructions install the callback; each filename byte takes twelve instructions; the final callback takes twenty-five instructions. Thus `32 + 12 * filename.utf8ByteSize` native steps pause at the interpreter loop at address `0x16d`. The actual file instruction uses the supplied open/read IO equation. The RAM patch is established byte for byte, including empty files.
2. **Represent complete machine state.** `Representation.Represents` relates guest RAM below `0xf7a7` to native RAM at `0x0859 + address`, all 256 bytes of both software stacks, their pointers, and the guest PC. Tracking inactive stack bytes is necessary because stack pointers wrap. `CodeImage` protects code except the interpreter's deliberate mutable immediates. `Boundary` adds device shadows, console-input literals, native return frames, and direct reachability.
3. **Derive access bounds from confinement.** `Confinement`, `LoadBounds`, `StoreBounds`, and `ImmediateBounds` vary an outside RAM byte and observe the resulting opcode, stack byte, PC, or written byte. Dependence on that byte contradicts confinement. The untaken JCI branch does not read its displacement, so it needs no operand-read bound.
4. **Check each instruction block.** Direct guest semantics and native handler execution are proved separately, then connected through the representation invariant. The blocks cover byte/word, working/return-stack, and normal/keep modes, with exact wrapping stack behavior. Memory handlers use the derived bounds. Device output matches the actual IO operation, including error results, with silent native steps before and after it. BRK runs the native cleanup through the outer BRK.
5. **Assemble finite stuttering.** `RankedSimulation.of_silent_chunks` extends the instruction-boundary relation to intermediate native states. Its rank is the least remaining length of a silent path to the matching step. Every direct step has an explicit matching native step, even when the guest instruction returns to the same state. This establishes progress without assuming guest termination.
6. **Exhaust all opcodes.** The main theorem splits the 32 low-bit opcode families and the eight special immediate encodings, including BRK. Instruction contracts restore `Boundary`, and terminal/error contracts establish that both successors are absent.

## Shared library reuse

The finite pure-execution relation in `Host/Execution.lean` was extracted from the existing Fibonacci proof, which now imports it. `Host/StackFrame.lean` factors the return-frame argument used by STH, JSR, and immediate subroutine calls. `Host/Permutation.lean` supplies the word-stack permutation steps reused by several handlers. `Host/Memory.initial_ram_eq` supplies the shared exact initialization formula. Existing HelloWorld, Fibonacci, and Sierpinski proof adapters were updated for the already-current host API and rebuilt.

## Proof status

`ProgramProofs.Uxnmin.correct` is fully kernel checked, including initialization and all 256 instruction encodings. Its statement and public semantic definitions are the original ones, presented together in `Correctness.lean`. `Proof.lean` contains the implementation, using the model in `Semantics.lean`; the final theorem application checks that the public definitions and that model agree by definitional equality. Its transitive axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no admitted obligations in its dependency graph.

`ProgramProofs.lean` imports the theorem and includes it in the existing standard-axiom guard. `lake build ProgramProofs` therefore checks both the proof and this guard alongside HelloWorld, Fibonacci, and Sierpinski.

Proofs were developed and checked in temporary files before promotion. No `native_decide` is used. The TAL source was reassembled with the repository's reference runner and Drifloon assembler; its 1110 bytes match both `uxnmin.rom` and the literal `Rom.lean` definition, and the recorded provenance hashes agree.
