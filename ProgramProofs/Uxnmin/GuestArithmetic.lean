import ProgramProofs.Uxnmin.ArithmeticAction

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def arithmeticNext (guest : Uxn.State) (operator : ArithmeticOp)
    (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack { guest with pc := guest.pc + 1 } ret keep
    (operandSize short + operandSize short)) ret short
      (operator.result (operand (guestStack guest ret) (guestStack guest ret).ptr short)
        (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short))

/-- Exact direct arithmetic behavior in all short, keep and selected-stack
modes, including pointer wraparound and division by zero. -/
theorem guest_arithmetic (operator : ArithmeticOp) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode) :
    Uxn.step guest = .done (.next (arithmeticNext guest operator
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  rw [arithmetic_action operator guest opcode, binary_action]
  have same : operator.combine = operator.result := by
    funext first second
    cases operator <;>
      simp [ArithmeticOp.combine, ArithmeticOp.result, BitVec.add_comm, BitVec.mul_comm,
        BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm]
  rw [same]
  rfl

end ProgramProofs.Uxnmin
