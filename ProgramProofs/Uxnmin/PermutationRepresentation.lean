import ProgramProofs.Uxnmin.PermutationHandler
import ProgramProofs.Uxnmin.OperandRepresentation

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The native permutation memory update represents the exact guest operation. -/
theorem represents_permutation {guest outer : Uxn.State}
    (rep : Represents { guest with pc := guest.pc + 1 } outer)
    (operator : StackOp) (ret short keep : Bool) :
    Represents (stackNext guest operator ret short keep)
      { outer with
        mem.ram := operator.memory outer.mem.ram (stackBase ret) (guestStack guest ret).ptr
          (if keep then 1 else 0) short } := by
  have value (pointer : Byte) : stackOperand outer.mem.ram (stackBase ret) pointer short =
      operand (guestStack guest ret) pointer short := by
    simpa using rep.operand ret short pointer
  cases operator with
  | nip =>
    have pushed := (rep.popStack ret keep (operandSize short + operandSize short)).storeOperand ret short
      (operand (guestStack guest ret) (guestStack guest ret).ptr short)
    cases ret <;> cases short <;> cases keep <;>
      simpa [stackNext, StackOp.memory, StackOp.poppedPointer, value, guestStack,
        ProgramProofs.Uxnmin.popStack, pushStack, storeStackOperand, operandSize,
        BitVec.sub_eq_add_neg, BitVec.add_assoc] using pushed
  | swp =>
    have pushed := ((rep.popStack ret keep (operandSize short + operandSize short)).storeOperand ret short
      (operand (guestStack guest ret) (guestStack guest ret).ptr short)).storeOperand ret short
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short)
    cases ret <;> cases short <;> cases keep <;>
      simpa [stackNext, StackOp.memory, StackOp.poppedPointer, value, guestStack,
        ProgramProofs.Uxnmin.popStack, pushStack, storeStackOperand, operandSize,
        Stack.push, Stack.pushWord, BitVec.sub_eq_add_neg, BitVec.add_assoc] using pushed
  | rot =>
    have pushed := (((rep.popStack ret keep (operandSize short + operandSize short + operandSize short)).storeOperand ret short
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short)).storeOperand ret short
      (operand (guestStack guest ret) (guestStack guest ret).ptr short)).storeOperand ret short
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short - operandSize short) short)
    cases ret <;> cases short <;> cases keep <;>
      simpa [stackNext, StackOp.memory, StackOp.poppedPointer, value, guestStack,
        ProgramProofs.Uxnmin.popStack, pushStack, storeStackOperand, operandSize,
        Stack.push, Stack.pushWord, BitVec.sub_eq_add_neg, BitVec.add_assoc] using pushed
  | dup =>
    have pushed := ((rep.popStack ret keep (operandSize short)).storeOperand ret short
      (operand (guestStack guest ret) (guestStack guest ret).ptr short)).storeOperand ret short
      (operand (guestStack guest ret) (guestStack guest ret).ptr short)
    cases ret <;> cases short <;> cases keep <;>
      simpa [stackNext, StackOp.memory, StackOp.poppedPointer, value, guestStack,
        ProgramProofs.Uxnmin.popStack, pushStack, storeStackOperand, operandSize,
        Stack.push, Stack.pushWord, BitVec.sub_eq_add_neg, BitVec.add_assoc] using pushed
  | ovr =>
    have pushed := (((rep.popStack ret keep (operandSize short + operandSize short)).storeOperand ret short
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short)).storeOperand ret short
      (operand (guestStack guest ret) (guestStack guest ret).ptr short)).storeOperand ret short
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short)
    cases ret <;> cases short <;> cases keep <;>
      simpa [stackNext, StackOp.memory, StackOp.poppedPointer, value, guestStack,
        ProgramProofs.Uxnmin.popStack, pushStack, storeStackOperand, operandSize,
        Stack.push, Stack.pushWord, BitVec.sub_eq_add_neg, BitVec.add_assoc] using pushed

end ProgramProofs.Uxnmin
