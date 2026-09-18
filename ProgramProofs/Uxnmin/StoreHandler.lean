import ProgramProofs.Uxnmin.StorePrepare
import ProgramProofs.Uxnmin.GuestStack

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The three native memory store handlers, including all operand modes and active frames. -/
theorem handler_store (kind : AddressMode) (memory : Word → Byte)
    (softwareStack pc : Word) (pointer keep : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (firstBound : (kind.nativeAddress pc
      (stackOperand memory softwareStack pointer (kind.operandKind.short short))).toNat < ramSize)
    (secondBound : short = true → ((kind.nativeAddress pc
      (stackOperand memory softwareStack pointer (kind.operandKind.short short)) + 1#16) &&& kind.mask).toNat < ramSize)
    (workingSpace : working.ptr.toNat ≤ 245) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory kind.storeEntry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram =
        pokeMemory
          (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
            (pointer - kind.consumed - operandSize short))
          (kind.nativeAddress pc (stackOperand memory softwareStack pointer (kind.operandKind.short short)))
          kind.mask (stackOperand memory softwareStack (pointer - kind.consumed) short) short ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have calls : OperandPairCode kind.storeEntry kind.operandKind .mode := by
    intro memory working returning offset image position
    cases kind
    case zero =>
      have code46a : memory 0x46a#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code46b : memory 0x46b#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code46c : memory 0x46c#16 = 0x46#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code46d : memory 0x46d#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code46e : memory 0x46e#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code46f : memory 0x46f#16 = 0x3d#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      rcases position with rfl | rfl <;> apply jsi_call <;>
        simp [AddressMode.storeEntry, AddressMode.operandKind, OperandKind.entry, code46a, code46b, code46c, code46d, code46e, code46f]
    case relative =>
      have code487 : memory 0x487#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code488 : memory 0x488#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code489 : memory 0x489#16 = 0x29#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code48a : memory 0x48a#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code48b : memory 0x48b#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code48c : memory 0x48c#16 = 0x20#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      rcases position with rfl | rfl <;> apply jsi_call <;>
        simp [AddressMode.storeEntry, AddressMode.operandKind, OperandKind.entry, code487, code488, code489, code48a, code48b, code48c]
    case absolute =>
      have code4a4 : memory 0x4a4#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code4a5 : memory 0x4a5#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code4a6 : memory 0x4a6#16 = 0x29#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code4a7 : memory 0x4a7#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code4a8 : memory 0x4a8#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code4a9 : memory 0x4a9#16 = 0x03#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      rcases position with rfl | rfl <;> apply jsi_call <;>
        simp [AddressMode.storeEntry, AddressMode.operandKind, OperandKind.entry, code4a4, code4a5, code4a6, code4a7, code4a8, code4a9]
  have amount : (if kind.operandKind.short short then 2#8 else 1#8) = kind.consumed := by
    cases kind <;> rfl
  have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  obtain ⟨popped, popSteps, popPC, popMemory, popCode, popWP, popRP, popShape,
    popReturnShape, popFrame, popReturnFrame⟩ :=
    pop_operand_pair kind.operandKind .mode kind.storeEntry calls memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor (by omega) returnSpace
  rw [amount] at popMemory popShape
  simp only [OperandKind.short] at popMemory popShape
  change popped.mem.ram = Function.update memory
    (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - kind.consumed - operandSize short) at popMemory
  have poppedPC : popped = machine popped.mem.ram (kind.storeEntry + 6) popped.mem.wstk popped.mem.rstk := by
    cases popped
    simpa [machine] using popPC
  obtain ⟨prepared, prepareSteps, preparePC, prepareMemory, prepareWP, prepareShape,
    prepareRP, prepareFrame, prepareReturnFrame⟩ :=
    store_prepare kind popped.mem.ram pc
      (stackOperand memory softwareStack pointer (kind.operandKind.short short))
      (stackOperand memory softwareStack (pointer - kind.consumed) short)
      { popped.mem.wstk with ptr := working.ptr } popped.mem.rstk popCode
      (by rw [popMemory, Function.update_of_ne (separate _ (by decide)), pcHigh])
      (by rw [popMemory, Function.update_of_ne (separate _ (by decide)), pcLow]) (by dsimp; omega)
      (by rw [popRP]; bv_omega)
  change Stack.pushWord (Stack.pushWord { popped.mem.wstk with ptr := working.ptr }
    (stackOperand memory softwareStack pointer (kind.operandKind.short short)))
    (stackOperand memory softwareStack (pointer - kind.consumed) short) = popped.mem.wstk at popShape
  have preparation : Reaches popped prepared := by
    rw [poppedPC]
    simpa only [popShape] using prepareSteps
  have preparedCode : CodeImage prepared.mem.ram := by rw [prepareMemory]; exact popCode
  have preparedMode : prepared.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [prepareMemory, popMemory, Function.update_of_ne (separate _ (by decide)), mode]
  have returnHigh : prepared.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [prepareReturnFrame _ (by rw [popRP]; bv_omega), ← popReturnShape]
    simp [Stack.pushWord, Stack.push]
  have returnLow : prepared.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [prepareReturnFrame _ (by rw [popRP]; bv_omega), ← popReturnShape]
    simp [Stack.pushWord, Stack.push]
  have preparedReturnShape : Stack.pushWord { prepared.mem.rstk with ptr := returning.ptr }
      returnAddress = prepared.mem.rstk := by
    simpa [prepareRP, popRP, BitVec.sub_eq_add_neg, BitVec.add_assoc, returnHigh, returnLow, append_split]
      using Stack.asPushWord prepared.mem.rstk
  obtain ⟨final, tailSteps, finalPC, finalWP, finalRP, finalMemory, finalCode, finalFrame, finalReturnFrame⟩ :=
    store_tail kind prepared.mem.ram
      (kind.nativeAddress pc (stackOperand memory softwareStack pointer (kind.operandKind.short short)))
      (stackOperand memory softwareStack (pointer - kind.consumed) short) short
      { prepared.mem.wstk with ptr := working.ptr } { prepared.mem.rstk with ptr := returning.ptr }
      returnAddress preparedCode preparedMode firstBound secondBound (by dsimp; omega) (by dsimp; omega)
  have preparedEta : prepared = machine prepared.mem.ram kind.storeTail prepared.mem.wstk prepared.mem.rstk := by
    cases prepared
    simpa [machine] using preparePC
  have completion : Reaches prepared final := by
    rw [preparedEta]
    simpa only [prepareShape, preparedReturnShape] using tailSteps
  refine ⟨final, popSteps.trans (preparation.trans completion), finalPC, finalWP, finalRP,
    ?_, finalCode, ?_, ?_⟩
  · rw [finalMemory, prepareMemory, popMemory]
  · intro index bound
    rw [finalFrame _ bound, prepareFrame _ bound, popFrame _ bound]
  · intro index bound
    rw [finalReturnFrame _ bound, prepareReturnFrame _ (by rw [popRP]; bv_omega), popReturnFrame _ bound]

end ProgramProofs.Uxnmin
