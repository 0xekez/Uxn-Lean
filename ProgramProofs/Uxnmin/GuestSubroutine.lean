import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.GuestStack
import ProgramProofs.Uxnmin.PcSet

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def subroutineNext (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  { pushStack (popStack { guest with pc := guest.pc + 1 } ret keep (operandSize short))
      (!ret) true (guest.pc + 1) with
    pc := jumpTarget (guest.pc + 1) (operand (guestStack guest ret) (guestStack guest ret).ptr short) short }

def subroutineAction (mode : Mode) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    let offset ← ops.dec
    ops.secondary.inc16 (← get).pc
    ops.jump offset
    return .done (.next (← get))

theorem guest_subroutine (guest : Uxn.State) (base : guest.mem.ram guest.pc &&& 0x1f = 14) :
    Uxn.step guest = .done (.next (subroutineNext guest
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = 14) :
      Instruction.ofByte byte = .normal .jsr ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte 14 (by decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;> subst byte <;> rfl
  have action (ret short keep : Bool) :
      (subroutineAction ⟨short, keep, ret⟩ { guest with pc := guest.pc + 1 }).fst =
        .done (.next (subroutineNext guest ret short keep)) := by
    let decrement (pointer : Byte) (short : Bool) := if short then pointer - 1 - 1 else pointer - 1
    let rawOperand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :=
      if short then (stack.data (pointer - 1)).setWidth 16 |||
        (stack.data (pointer - 1 - 1)).setWidth 16 <<< 8
      else (stack.data (pointer - 1)).setWidth 16
    let rawResult (guest : Uxn.State) (ret short keep : Bool) :=
      let source := guestStack guest ret
      let offset := rawOperand source source.ptr short
      { pushStack (if keep then guest else setStack guest ret
          { source with ptr := decrement source.ptr short }) (!ret) true guest.pc with
        pc := if short then offset else guest.pc + (offset.setWidth 8).signExtend 16 }
    have execute (guest : Uxn.State) (ret short keep : Bool) :
        (subroutineAction ⟨short, keep, ret⟩ guest).fst =
          .done (.next (rawResult guest ret short keep)) := by
      as_aux_lemma =>
        cases ret <;> cases short <;> cases keep <;> rfl
    have decrement_eq (pointer : Byte) (short : Bool) :
        decrement pointer short = pointer - operandSize short := by
      cases short <;> simp [decrement, operandSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    have operand_eq (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :
        rawOperand stack pointer short = operand stack pointer short := by
      cases short <;> simp [rawOperand, operand, ← join_bytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [execute]
    congr 2
    simp only [rawResult, operand_eq, decrement_eq]
    cases ret <;> cases short <;> cases keep <;>
      simp [subroutineNext, jumpTarget, guestStack, setStack, popStack, operandSize]
  have front : Uxn.step guest = (subroutineAction
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ { guest with pc := guest.pc + 1 }).fst := by
    dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
    rw [decoded _ base]
    rfl
  rw [front]
  exact action _ _ _

end ProgramProofs.Uxnmin
