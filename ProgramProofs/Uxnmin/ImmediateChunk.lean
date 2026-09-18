import ProgramProofs.Uxnmin.ImmediateConditionalSimulation
import ProgramProofs.Uxnmin.ImmediateJumpSimulation
import ProgramProofs.Uxnmin.ImmediateSubroutineSimulation
import ProgramProofs.Uxnmin.LiteralSimulation
import ProgramProofs.Uxnmin.ImmediateObservation
import ProgramProofs.Uxnmin.Simulation

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn ProgramProofs.Host

/-- All immediate instructions preserve the boundary relation in actual host IO. -/
theorem immediate_chunk (kind : ImmediateKind) {guest outer : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = kind.opcode)
    (bounds : ∀ second, kind.reads guest second → (guest.pc + 1 + if second then 1 else 0).toNat < ramSize) :
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
  suffices simulated : ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary (immediateNext kind guest) final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) by
    obtain ⟨first, final, nativeStep, suffix, related, memory, pointer, frame⟩ := simulated
    obtain ⟨direct, native, silent⟩ :=
      nondevice_chunk_of_step guestHost outerHost world (guest_immediate kind guest opcode) nativeStep suffix
    exact ⟨immediateNext kind guest, first, final, direct, native, silent, related, memory, pointer, frame⟩
  cases kind with
  | jci =>
    apply immediate_conditional_simulation boundary confined opcode
    · intro taken
      simpa using bounds false taken
    · intro taken
      simpa [BitVec.add_assoc] using bounds true taken
  | jmi =>
    apply immediate_jump_simulation boundary confined opcode
    · simpa using bounds false trivial
    · simpa [BitVec.add_assoc] using bounds true trivial
  | jsi =>
    apply immediate_subroutine_simulation boundary confined opcode
    · simpa using bounds false trivial
    · simpa [BitVec.add_assoc] using bounds true trivial
  | lit short ret =>
    apply literal_simulation short ret boundary confined opcode
    · simpa using bounds false (by simp [ImmediateKind.reads])
    · intro mode
      simpa [BitVec.add_assoc] using bounds true (by simpa [ImmediateKind.reads] using mode)

end ProgramProofs.Uxnmin
