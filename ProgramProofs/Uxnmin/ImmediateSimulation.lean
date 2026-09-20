import ProgramProofs.Uxnmin.ImmediateConditionalSimulation
import ProgramProofs.Uxnmin.ImmediateJumpSimulation
import ProgramProofs.Uxnmin.ImmediateSubroutineSimulation
import ProgramProofs.Uxnmin.LiteralSimulation
import ProgramProofs.Uxnmin.ImmediateObservation

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem immediate_simulation (kind : ImmediateKind) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ProgramProofs.Uxnmin.ramSize)
    (opcode : guest.mem.ram guest.pc = kind.opcode)
    (bounds : ∀ second, kind.reads guest second →
      (guest.pc + 1 + if second then 1 else 0).toNat < ProgramProofs.Uxnmin.ramSize) :
    ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary (immediateNext kind guest) final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
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
