import ProgramProofs.Uxnmin.ComparisonAction

set_option maxHeartbeats 400000

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def comparisonNext (guest : Uxn.State) (operator : ComparisonOp)
    (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack { guest with pc := guest.pc + 1 } ret keep
    (operandSize short + operandSize short)) ret false
      ((operator.result (operand (guestStack guest ret) (guestStack guest ret).ptr short)
        (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short)).setWidth 16)

/-- Exact direct comparison behavior in all short, keep and selected-stack
modes, including pointer wraparound. -/
theorem guest_comparison (operator : ComparisonOp) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode) :
    Uxn.step guest = .done (.next (comparisonNext guest operator
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  rw [comparison_action operator guest opcode, comparison_stack_action]
  have same : operator.combine = operator.result := by
    funext first second
    cases operator <;> dsimp [ComparisonOp.combine, ComparisonOp.result]
    all_goals first | rfl |
      (by_cases equal : first = second
       · subst second; simp
       · have reverse : second ≠ first := Ne.symm equal
         simp [equal, reverse])
  rw [same]
  rfl

end ProgramProofs.Uxnmin
