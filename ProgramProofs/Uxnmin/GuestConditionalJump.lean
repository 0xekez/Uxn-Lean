import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.GuestStack
import ProgramProofs.Uxnmin.PcSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def conditionalJumpNext (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  { popStack { guest with pc := guest.pc + 1 } ret keep (operandSize short + 1) with
    pc := if (guestStack guest ret).data ((guestStack guest ret).ptr - operandSize short - 1) = 0 then
      guest.pc + 1
    else jumpTarget (guest.pc + 1) (operand (guestStack guest ret) (guestStack guest ret).ptr short) short }

def conditionalJumpAction (mode : Mode) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    let offset ← ops.dec
    if (← ops.dec8) != 0 then ops.jump offset
    return .done (.next (← get))

theorem guest_conditional_jump (guest : Uxn.State) (base : guest.mem.ram guest.pc &&& 0x1f = 13) :
    Uxn.step guest = .done (.next (conditionalJumpNext guest
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = 13) :
      Instruction.ofByte byte = .normal .jcn ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte 13 (by decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;> subst byte <;> rfl
  have action (ret short keep : Bool) :
      (conditionalJumpAction ⟨short, keep, ret⟩ { guest with pc := guest.pc + 1 }).fst =
        .done (.next (conditionalJumpNext guest ret short keep)) := by
    have widen (byte : Byte) : (0#8 ++ byte : Word) = byte.setWidth 16 := by
      simpa using (join_bytes 0#8 byte).symm
    cases ret <;> cases short <;> cases keep
    all_goals as_aux_lemma =>
      simp [conditionalJumpAction, uxn_state, uxn_step, conditionalJumpNext, jumpTarget,
        popStack, guestStack, operandSize, operand, widen]
      split_ifs <;> simp [uxn_state, BitVec.add_assoc]
  have front : Uxn.step guest = (conditionalJumpAction
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ { guest with pc := guest.pc + 1 }).fst := by
    dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
    rw [decoded _ base]
    rfl
  rw [front]
  exact action _ _ _

end ProgramProofs.Uxnmin
