import ProgramProofs.Uxnmin.PermutationRawNip
import ProgramProofs.Uxnmin.PermutationRawSwp
import ProgramProofs.Uxnmin.PermutationRawDup
import ProgramProofs.Uxnmin.PermutationRotAction
import ProgramProofs.Uxnmin.PermutationOvrAction

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

private theorem stack_action_raw (guest : Uxn.State) (operator : StackOp) (ret short keep : Bool) :
    (stackAction operator ⟨short, keep, ret⟩ guest).fst =
      .done (.next (rawNext guest operator ret short keep)) := by
  cases operator with
  | nip => exact stack_action_nip guest ret short keep
  | swp => exact stack_action_swp guest ret short keep
  | rot => exact stack_action_rot_modular guest ret short keep
  | dup => exact stack_action_dup guest ret short keep
  | ovr => exact stack_action_ovr_modular guest ret short keep

/-- All five stack permutations, including short, return and keep modes. -/
theorem guest_stack (operator : StackOp) (guest : Uxn.State)
    (base : guest.mem.ram guest.pc &&& 0x1f = operator.opcode) :
    Uxn.step guest = .done (.next (stackNext guest operator
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = operator.opcode) :
      Instruction.ofByte byte = .normal operator.operation ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte _ (by cases operator <;> decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;> subst byte <;> cases operator <;> rfl
  have action (operator : StackOp) (ret short keep : Bool) :
      (stackAction operator ⟨short, keep, ret⟩ { guest with pc := guest.pc + 1 }).fst =
        .done (.next (stackNext guest operator ret short keep)) := by
    have decrement_eq (pointer : Byte) (short : Bool) :
        decrement pointer short = pointer - operandSize short := by
      cases short <;> simp [decrement, operandSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    have operand_eq (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :
        rawOperand stack pointer short = operand stack pointer short := by
      cases short <;> simp [rawOperand, operand, ← join_bytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [stack_action_raw]
    congr 2
    simp only [rawNext, operand_eq, decrement_eq]
    cases operator <;> cases ret <;> cases short <;> cases keep <;>
      simp [stackNext, pushStack, guestStack, setStack, popStack, operandSize,
        BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have front : Uxn.step guest = (stackAction operator
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ { guest with pc := guest.pc + 1 }).fst := by
    dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
    rw [decoded _ base]
    cases operator <;> rfl
  rw [front]
  exact action _ _ _ _

end ProgramProofs.Uxnmin
