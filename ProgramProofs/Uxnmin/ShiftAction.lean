import ProgramProofs.Uxnmin.GuestStack
import ProgramProofs.Uxnmin.ShiftHandler
import ProgramProofs.Uxnmin.OpcodeModes

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def shiftAction (mode : Mode) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    let shift ← ops.dec8
    ops.inc ((← ops.dec) >>> (shift &&& 0x0f).toNat <<< (shift >>> 4).toNat)
    return .done (.next (← get))

def shiftActionResult (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack guest ret keep (1 + operandSize short)) ret short
    (shiftResult (operand (guestStack guest ret) (guestStack guest ret).ptr false)
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - 1) short))

/-- The shift action consumes a byte count and a mode-sized value. -/
theorem shift_stack_action (guest : Uxn.State) (ret short keep : Bool) :
    (shiftAction ⟨short, keep, ret⟩ guest).fst =
      .done (.next (shiftActionResult guest ret short keep)) := by
  let decrement (pointer : Byte) (short : Bool) := if short then pointer - 1 - 1 else pointer - 1
  let rawOperand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :=
    if short then (stack.data (pointer - 1)).setWidth 16 |||
      (stack.data (pointer - 1 - 1)).setWidth 16 <<< 8
    else (stack.data (pointer - 1)).setWidth 16
  let rawResult (guest : Uxn.State) (ret short keep : Bool) :=
    let source := guestStack guest ret
    let shift := source.data (source.ptr - 1)
    pushStack (if keep then guest else setStack guest ret
      { source with ptr := decrement (source.ptr - 1) short }) ret short
      (rawOperand source (source.ptr - 1) short >>> (shift &&& 0x0f).toNat <<< (shift >>> 4).toNat)
  have execute (guest : Uxn.State) (ret short keep : Bool) :
      (shiftAction ⟨short, keep, ret⟩ guest).fst =
        .done (.next (rawResult guest ret short keep)) := by
    as_aux_lemma =>
      cases ret <;> cases short <;> cases keep <;> rfl
  have decrement_eq (pointer : Byte) (short : Bool) :
      decrement pointer short = pointer - operandSize short := by
    cases short <;> simp [decrement, operandSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have operand_eq (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :
      rawOperand stack pointer short = operand stack pointer short := by
    cases short <;>
      simp [rawOperand, operand, ← join_bytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have zero (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by
    simpa using (join_bytes 0#8 byte).symm
  rw [execute]
  congr 2
  simp only [rawResult, operand_eq, decrement_eq]
  cases ret <;> cases short <;> cases keep <;>
    simp [shiftActionResult, guestStack, setStack, popStack, operandSize, shiftResult, operand, zero,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- Opcode decoding selects the shift action without expanding its stack execution. -/
theorem shift_action (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x1f) :
    Uxn.step guest = (shiftAction
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ { guest with pc := guest.pc + 1 }).fst := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = 0x1f) :
      Instruction.ofByte byte = .normal .sft
        ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte _ (by decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;> subst byte <;> rfl
  dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
  rw [decoded _ opcode]
  rfl

end ProgramProofs.Uxnmin
