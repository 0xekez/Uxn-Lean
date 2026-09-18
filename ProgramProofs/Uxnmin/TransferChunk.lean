import ProgramProofs.Uxnmin.TransferSimulation
import ProgramProofs.Uxnmin.Simulation

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn ProgramProofs.Host ProgramProofs.Uxnmin

/-- The STH instruction's complete chunk contract in the actual IO transition
system. Host records may differ; both executions preserve their own record. -/
theorem transfer_chunk {guest outer : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 15) :
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
  obtain ⟨guest', final, guestStep, steps, related, different, memory, pointer, frame⟩ :=
    transfer_simulation boundary confined opcode
  obtain ⟨first, direct, native, suffix⟩ :=
    nondevice_chunk guestHost outerHost world guestStep steps different
  exact ⟨guest', first, final, direct, native, suffix, related, memory, pointer, frame⟩

end ProgramProofs.Uxnmin
