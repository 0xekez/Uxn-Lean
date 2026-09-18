import ProgramProofs.Uxnmin.LoadPrepare
import ProgramProofs.Uxnmin.OperandCall

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The three native memory load handlers, including all operand modes and active frames. -/
theorem handler_load (kind : AddressMode) (memory : Word → Byte)
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
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory kind.loadEntry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram =
        (let popped := Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
          (pointer - kind.consumed)
        storeStackOperand popped softwareStack (if keep = 0 then pointer - kind.consumed else pointer)
          (peekValue popped
            (kind.nativeAddress pc (stackOperand memory softwareStack pointer (kind.operandKind.short short)))
            kind.mask short) short) ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have calls : OperandCallCode kind.loadEntry kind.operandKind := by
    intro memory working returning image
    cases kind
    case zero =>
      have code45e : memory 0x45e#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code45f : memory 0x45f#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code460 : memory 0x460#16 = 0x52#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      apply jsi_call <;> simp [AddressMode.loadEntry, AddressMode.operandKind, OperandKind.entry, code45e, code45f, code460]
    case relative =>
      have code477 : memory 0x477#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code478 : memory 0x478#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code479 : memory 0x479#16 = 0x39#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      apply jsi_call <;> simp [AddressMode.loadEntry, AddressMode.operandKind, OperandKind.entry, code477, code478, code479]
    case absolute =>
      have code498 : memory 0x498#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code499 : memory 0x499#16 = 0xfe#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      have code49a : memory 0x49a#16 = 0x35#8 := image _ (by decide) (by decide) (by simp [MutableCode])
      apply jsi_call <;> simp [AddressMode.loadEntry, AddressMode.operandKind, OperandKind.entry, code498, code499, code49a]
  have amount : (if kind.operandKind.short short then 2#8 else 1#8) = kind.consumed := by
    cases kind <;> rfl
  have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  obtain ⟨popped, popSteps, popPC, popMemory, popCode, popWP, popRP, popShape,
    popReturnShape, popFrame, popReturnFrame⟩ :=
    pop_call_operand kind.operandKind kind.loadEntry calls memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor (by omega) returnSpace
  rw [amount] at popMemory
  have poppedPC : popped = machine popped.mem.ram (kind.loadEntry + 3) popped.mem.wstk popped.mem.rstk := by
    cases popped
    simpa [machine] using popPC
  obtain ⟨prepared, prepareSteps, preparePC, prepareMemory, prepareWP, prepareShape,
    prepareRP, prepareFrame, prepareReturnFrame⟩ :=
    load_prepare kind popped.mem.ram pc
      (stackOperand memory softwareStack pointer (kind.operandKind.short short))
      { popped.mem.wstk with ptr := working.ptr } popped.mem.rstk popCode
      (by rw [popMemory, Function.update_of_ne (separate _ (by decide)), pcHigh])
      (by rw [popMemory, Function.update_of_ne (separate _ (by decide)), pcLow]) workingSpace
      (by rw [popRP]; bv_omega)
  have preparation : Reaches popped prepared := by
    rw [poppedPC]
    simpa only [popShape] using prepareSteps
  have preparedCode : CodeImage prepared.mem.ram := by rw [prepareMemory]; exact popCode
  have preparedHigh : prepared.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [prepareMemory, popMemory, Function.update_of_ne (separate _ (by decide)), high]
  have preparedLow : prepared.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [prepareMemory, popMemory, Function.update_of_ne (separate _ (by decide)), low]
  have preparedMode : prepared.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [prepareMemory, popMemory, Function.update_of_ne (separate _ (by decide)), mode]
  have preparedPointer : prepared.mem.ram (softwareStack + 0x100#16) =
      if keep = 0 then pointer - kind.consumed else pointer := by
    rw [prepareMemory, popMemory]
    by_cases zero : keep = 0
    · simp [zero]
    · rw [Function.update_of_ne (by bv_omega), ptr, if_neg zero]
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
    load_tail kind prepared.mem.ram softwareStack
      (if keep = 0 then pointer - kind.consumed else pointer)
      (kind.nativeAddress pc (stackOperand memory softwareStack pointer (kind.operandKind.short short))) short
      { prepared.mem.wstk with ptr := working.ptr } { prepared.mem.rstk with ptr := returning.ptr }
      returnAddress selected preparedCode preparedHigh preparedLow preparedMode preparedPointer workingSpace returnSpace
  have preparedEta : prepared = machine prepared.mem.ram kind.loadTail prepared.mem.wstk prepared.mem.rstk := by
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
