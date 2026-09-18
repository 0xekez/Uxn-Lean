import ProgramProofs.Uxnmin.StoreAction

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def storeBytes (guest : Uxn.State) (address following value : Word) (short : Bool) : Uxn.State :=
  { guest with mem.ram := if short then
      Function.update (Function.update guest.mem.ram address ((value >>> 8).setWidth 8)) following (value.setWidth 8)
    else Function.update guest.mem.ram address (value.setWidth 8) }

def storeResult (kind : AddressMode) (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  storeBytes (popStack guest ret keep (kind.consumed + operandSize short))
    (kind.address guest ret) (kind.following (kind.address guest ret))
    (operand (guestStack guest ret) ((guestStack guest ret).ptr - kind.consumed) short) short

/-- All three addressing modes implement a pop-address/pop-value/store action. -/
theorem store_action (kind : AddressMode) (guest : Uxn.State) (ret short keep : Bool) :
    (storeAction kind ⟨short, keep, ret⟩ guest).fst = .done (.next (storeResult kind guest ret short keep)) := by
  let decrement (pointer : Byte) (short : Bool) := if short then pointer - 1 - 1 else pointer - 1
  let rawOperand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :=
    if short then (stack.data (pointer - 1)).setWidth 16 |||
      (stack.data (pointer - 1 - 1)).setWidth 16 <<< 8
    else (stack.data (pointer - 1)).setWidth 16
  let rawAddress (kind : AddressMode) (guest : Uxn.State) (ret : Bool) :=
    match kind with
    | .zero => ((guestStack guest ret).data ((guestStack guest ret).ptr - 1)).setWidth 16
    | .relative => guest.pc + ((guestStack guest ret).data ((guestStack guest ret).ptr - 1)).signExtend 16
    | .absolute => rawOperand (guestStack guest ret) (guestStack guest ret).ptr true
  let following (kind : AddressMode) (guest : Uxn.State) (ret : Bool) :=
    match kind with
    | .zero => (((guestStack guest ret).data ((guestStack guest ret).ptr - 1)) + 1#8).setWidth 16
    | _ => rawAddress kind guest ret + 1
  let raw (kind : AddressMode) (guest : Uxn.State) (ret short keep : Bool) :=
    let source := guestStack guest ret
    let cursor := decrement source.ptr (kind == .absolute)
    storeBytes (if keep then guest else setStack guest ret { source with ptr := decrement cursor short })
      (rawAddress kind guest ret) (following kind guest ret) (rawOperand source cursor short) short
  have execute (kind : AddressMode) (guest : Uxn.State) (ret short keep : Bool) :
      (storeAction kind ⟨short, keep, ret⟩ guest).fst = .done (.next (raw kind guest ret short keep)) := by
    dsimp only [raw, rawAddress, following, decrement, rawOperand]
    cases kind <;> cases ret <;> cases short <;> cases keep
    all_goals as_aux_lemma => rfl
  have decrement_eq (pointer : Byte) (short : Bool) : decrement pointer short = pointer - operandSize short := by
    cases short <;> simp [decrement, operandSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have zero (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by
    simpa using (join_bytes 0#8 byte).symm
  have operand_eq (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :
      rawOperand stack pointer short = operand stack pointer short := by
    cases short <;> simp [rawOperand, operand, zero, join_bytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have address (kind : AddressMode) (guest : Uxn.State) (ret : Bool) :
      rawAddress kind guest ret = kind.address guest ret := by
    cases kind <;> simp [rawAddress, AddressMode.address, operand_eq]
  have following_eq (kind : AddressMode) (guest : Uxn.State) (ret : Bool) :
      following kind guest ret = kind.following (kind.address guest ret) := by
    cases kind <;> simp [following, address, AddressMode.following, AddressMode.address]
  rw [execute]
  congr 2
  simp only [raw, address, following_eq, decrement_eq, operand_eq]
  cases kind <;> cases ret <;> cases short <;> cases keep <;>
    simp [storeResult, guestStack, setStack, popStack, operandSize, AddressMode.consumed,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

end ProgramProofs.Uxnmin
