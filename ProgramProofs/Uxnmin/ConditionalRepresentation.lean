import ProgramProofs.Uxnmin.GuestConditionalJump
import ProgramProofs.Uxnmin.OperandRepresentation
import ProgramProofs.Uxnmin.RepresentationPC

namespace ProgramProofs.Uxnmin
open Uxn

def conditionalJumpMemory (memory : Word → Byte) (base pc : Word) (pointer : Byte)
    (short keep : Bool) : Word → Byte :=
  let popped := Function.update memory (base + (0x100#16 + (if keep then 1#8 else 0#8).setWidth 16))
    (pointer - operandSize short - 1#8)
  if memory (base + (pointer - operandSize short - 1#8).setWidth 16) = 0#8 then popped
  else Function.update (Function.update popped
    0x45 ((jumpTarget pc (stackOperand memory base pointer short) short >>> 8).setWidth 8))
    0x46 ((jumpTarget pc (stackOperand memory base pointer short) short).setWidth 8)

/-- The JCN memory contract represents its conditional PC and stack update. -/
theorem represents_conditional_jump {guest outer : Uxn.State}
    (rep : Represents { guest with pc := guest.pc + 1 } outer) (ret short keep : Bool) :
    Represents (conditionalJumpNext guest ret short keep)
      { outer with mem.ram := (conditionalJumpMemory outer.mem.ram (stackBase ret)
        (guest.pc + 1) (guestStack guest ret).ptr short keep) } := by
  have value := rep.operand ret short (guestStack guest ret).ptr
  have condition := rep.stackData ret ((guestStack guest ret).ptr - operandSize short - 1#8)
  simp only [guestStack_pc] at value condition
  have popped := rep.popStack ret keep (operandSize short + 1#8)
  by_cases zero : (guestStack guest ret).data ((guestStack guest ret).ptr - operandSize short - 1#8) = 0#8
  · have result := popped.transport (replacement :=
        { outer with mem.ram := (conditionalJumpMemory outer.mem.ram (stackBase ret)
          (guest.pc + 1) (guestStack guest ret).ptr short keep) }) (by
      simp only [conditionalJumpMemory]
      rw [condition, if_pos zero]
      simp only [guestStack_pc, BitVec.sub_sub, BitVec.ofNat_eq_ofNat])
    cases ret <;> cases keep <;>
      simpa only [conditionalJumpNext, zero, popStack, Bool.false_eq_true, if_false,
        if_true, BitVec.ofNat_eq_ofNat] using result
  · have result := (popped.setPC (jumpTarget (guest.pc + 1)
        (operand (guestStack guest ret) (guestStack guest ret).ptr short) short)).transport (replacement :=
        { outer with mem.ram := (conditionalJumpMemory outer.mem.ram (stackBase ret)
          (guest.pc + 1) (guestStack guest ret).ptr short keep) }) (by
      simp only [conditionalJumpMemory]
      rw [condition, if_neg zero, value]
      simp only [guestStack_pc, BitVec.sub_sub, BitVec.ofNat_eq_ofNat])
    simpa only [conditionalJumpNext, zero, if_false, BitVec.ofNat_eq_ofNat] using result

end ProgramProofs.Uxnmin
