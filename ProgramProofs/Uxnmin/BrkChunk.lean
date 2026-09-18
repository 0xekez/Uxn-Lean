import ProgramProofs.Uxnmin.BrkPrefix
import ProgramProofs.Uxnmin.TerminalCleanup

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host

/-- A guest BRK matches a nonempty native execution ending at the outer BRK. -/
theorem brk_chunk {guest outer : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = 0)
    (pointer : outer.mem.rstk.ptr = 4)
    (loaderFrame : outer.mem.rstk.data 0 ++ outer.mem.rstk.data 1 = 0x139#16)
    (runFrame : outer.mem.rstk.data 2 ++ outer.mem.rstk.data 3 = 0x154#16) :
    ∃ first finalVM finalHost,
      next (.ok (.next guest, guestHost) world) =
        some (.ok (.brk { guest with pc := guest.pc + 1 }, guestHost) world) ∧
      next (.ok (.next outer, outerHost) world) = some (.ok (.next first, outerHost) world) ∧
      Relation.ReflTransGen
        (fun x y => next x = some y ∧ label (.ok (.next guest, guestHost) world) = label x)
        (.ok (.next first, outerHost) world) (.ok (.brk finalVM, finalHost) world) := by
  obtain ⟨first, final, native, suffix, pc, working, represented, _, returning, frame⟩ :=
    brk_prefix boundary confined opcode
  have loaderFrame' : final.mem.rstk.data 0 ++ final.mem.rstk.data 1 = 0x139#16 := by
    rw [frame 0 (by rw [pointer]; decide), frame 1 (by rw [pointer]; decide), loaderFrame]
  have runFrame' : final.mem.rstk.data 2 ++ final.mem.rstk.data 3 = 0x154#16 := by
    rw [frame 2 (by rw [pointer]; decide), frame 3 (by rw [pointer]; decide), runFrame]
  obtain ⟨finalVM, finalHost, cleanup⟩ := terminal_cleanup final.mem.ram final.mem.wstk final.mem.rstk
    outerHost world represented.code working (returning.trans pointer) loaderFrame' runFrame'
  have shape : final = machine final.mem.ram 0x173 final.mem.wstk final.mem.rstk := by
    cases final
    simpa [machine] using pc
  rw [← shape] at cleanup
  refine ⟨first, finalVM, finalHost, ?_, ?_, (reaches_chunk suffix outerHost world).trans ?_⟩
  · simp [next, Uxn.Host.step, uxn_state, uxn_step, opcode]
    rfl
  · simp only [next, Uxn.Host.step, native]
    rfl
  · exact Relation.ReflTransGen.mono (fun _ _ step => ⟨step.1, step.2.symm⟩) _ _ cleanup

end ProgramProofs.Uxnmin
