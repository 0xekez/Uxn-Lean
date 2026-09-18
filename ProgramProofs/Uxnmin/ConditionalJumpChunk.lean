import ProgramProofs.Uxnmin.ConditionalJumpSimulation
import ProgramProofs.Uxnmin.Simulation

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn ProgramProofs.Host ProgramProofs.Uxnmin

/-- The JCN instruction's complete chunk contract in the actual IO transition
system. Host records may differ; both executions preserve their own record. -/
theorem conditional_jump_chunk {guest outer : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 13) :
    ∃ guest' first final,
      next (.ok (.next guest, guestHost) world) = some (.ok (.next guest', guestHost) world) ∧
      next (.ok (.next outer, outerHost) world) = some (.ok (.next first, outerHost) world) ∧
      Relation.ReflTransGen
        (fun x y => next x = some y ∧ label (.ok (.next guest', guestHost) world) = label x)
        (.ok (.next first, outerHost) world) (.ok (.next final, outerHost) world) ∧
      EvaluationBoundary guest' final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨guest', first, final, guestStep, nativeStep, suffix, related, memory, pointer, frame⟩ :=
    conditional_jump_simulation boundary confined opcode
  obtain ⟨direct, native, silent⟩ :=
    nondevice_chunk_of_step guestHost outerHost world guestStep nativeStep suffix
  exact ⟨guest', first, final, direct, native, silent, related, memory, pointer, frame⟩

end ProgramProofs.Uxnmin
