import ProgramProofs.Uxnmin.PopPair
import ProgramProofs.Uxnmin.Arithmetic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def ArithmeticOp.entry : ArithmeticOp → Word
  | .add => 0x4c1 | .sub => 0x4cb | .mul => 0x4d6 | .div => 0x4e0
  | .and => 0x4eb | .ora => 0x4f5 | .eor => 0x4ff

def ArithmeticOp.swap : ArithmeticOp → Bool
  | .sub | .div => true
  | _ => false

def ArithmeticOp.opcode : ArithmeticOp → Byte
  | .add => 0x38 | .sub => 0x39 | .mul => 0x3a | .div => 0x3b
  | .and => 0x3c | .ora => 0x3d | .eor => 0x3e

set_option maxHeartbeats 2000000 in
theorem arithmetic_tail (operator : ArithmeticOp) (memory : Word → Byte)
    (first second : Word) (working returning : Uxn.Stack) (code : CodeImage memory)
    (workingSpace : working.ptr.toNat ≤ 251) :
    ∃ final, Reaches
      (machine memory (operator.entry + 6)
        (Stack.pushWord (Stack.pushWord working first) second) returning) final ∧
      final.pc = 0x28c ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.wstk.data working.ptr = ((operator.result first second) >>> 8).setWidth 8 ∧
      final.mem.wstk.data (working.ptr + 1#8) = (operator.result first second).setWidth 8 ∧
      final.mem.rstk = returning ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) := by
  have swapCode (needed : operator.swap = true) : memory (operator.entry + 6) = 0x24 := by
    cases operator <;> simp [ArithmeticOp.swap] at needed
    all_goals exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, MutableCode])
  have arithmeticCode : memory (operator.entry + (if operator.swap then 7 else 6)) = operator.opcode := by
    cases operator <;> exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, ArithmeticOp.swap, MutableCode])
  have jumpCode : memory (operator.entry + (if operator.swap then 8 else 7)) = 0x40 := by
    cases operator <;> exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, ArithmeticOp.swap, MutableCode])
  have offsetHigh : memory (operator.entry + (if operator.swap then 9 else 8)) =
      ((0x28c - (operator.entry + (if operator.swap then 11 else 10))) >>> 8).setWidth 8 := by
    cases operator <;> exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, ArithmeticOp.swap, MutableCode])
  have offsetLow : memory (operator.entry + (if operator.swap then 10 else 9)) =
      (0x28c - (operator.entry + (if operator.swap then 11 else 10))).setWidth 8 := by
    cases operator <;> exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, ArithmeticOp.swap, MutableCode])
  cases operator <;>
    simp [ArithmeticOp.entry, ArithmeticOp.swap, ArithmeticOp.opcode, ArithmeticOp.result,
      Bool.false_eq_true, if_false, if_true] at *
  case sub | div =>
    iterate 3
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, swapCode, arithmeticCode, jumpCode, offsetHigh, offsetLow]
        rfl
    refine ⟨_, .refl _, rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp [BitVec.sub_eq_add_neg]
    · simp [BitVec.sub_eq_add_neg]
    · intro address bound
      simp (disch := bv_omega) only [Function.update_of_ne]
  all_goals
    iterate 2
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, arithmeticCode, jumpCode, offsetHigh, offsetLow]
        rfl
    refine ⟨_, .refl _, rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp [BitVec.sub_eq_add_neg]
    · simp [BitVec.sub_eq_add_neg]
    · intro address bound
      simp (disch := bv_omega) only [Function.update_of_ne]



theorem ArithmeticOp.call (operator : ArithmeticOp) (memory : Word → Byte) (offset : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory) (position : offset = 0 ∨ offset = 3) :
    Uxn.step (machine memory (operator.entry + offset) working returning) = .done (.next
      (machine memory 0x2ad working (Stack.pushWord returning (operator.entry + offset + 3)))) := by
  apply jsi_call
  · cases operator <;> rcases position with rfl | rfl <;>
      exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, MutableCode])
  · have high : memory (operator.entry + offset + 1) =
        ((0x2ad - (operator.entry + offset + 3)) >>> 8).setWidth 8 := by
      cases operator <;> rcases position with rfl | rfl <;>
        exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, MutableCode])
    have low : memory (operator.entry + offset + 2) =
        (0x2ad - (operator.entry + offset + 3)).setWidth 8 := by
      cases operator <;> rcases position with rfl | rfl <;>
        exact code _ (by decide) (by decide) (by simp [ArithmeticOp.entry, MutableCode])
    rw [high, low, append_split]

theorem handler_arithmetic (operator : ArithmeticOp) (memory : Word → Byte)
    (softwareStack : Word) (pointer keep : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory operator.entry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
          (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8))) softwareStack
        (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
        (operator.result (stackOperand memory softwareStack pointer short)
          (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short)) short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have stackAfter : 0x555 ≤ (softwareStack + (0x100#16 + keep.setWidth 16)).toNat := by bv_omega
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  obtain ⟨second, before, secondPC, combinedMem, combinedCode, workingPointer,
      returningPointer, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_pair operator.entry (fun ram w r offset image position =>
      operator.call ram offset w r image position) memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor workingSpace returnSpace
  have secondShape : second = machine second.mem.ram (operator.entry + 6) second.mem.wstk second.mem.rstk := by
    cases second
    simpa [machine] using secondPC
  obtain ⟨computed, computedSteps, computedPC, computedMem, computedWP, computedHigh, computedLow, computedRP, computedWF⟩ :=
    arithmetic_tail operator second.mem.ram (stackOperand memory softwareStack pointer short)
      (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short)
      { second.mem.wstk with ptr := working.ptr } second.mem.rstk combinedCode (by dsimp; omega)
  have computation : Reaches second computed := by
    rw [secondShape]
    simpa only [workingEta] using computedSteps
  have computedCode : CodeImage computed.mem.ram := by rw [computedMem]; exact combinedCode
  have computedHighPort : computed.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [computedMem, combinedMem, Function.update_of_ne (separate _ (by decide)), high]
  have computedLowPort : computed.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [computedMem, combinedMem, Function.update_of_ne (separate _ (by decide)), low]
  have computedMode : computed.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [computedMem, combinedMem, Function.update_of_ne (separate _ (by decide)), mode]
  have computedPointer : computed.mem.ram (softwareStack + 0x100#16) =
      if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer := by
    rw [computedMem, combinedMem]
    by_cases zero : keep = 0
    · simp [zero]
    · rw [Function.update_of_ne (by bv_omega), ptr, if_neg zero]
  have computedWorkingEta : Stack.pushWord { computed.mem.wstk with ptr := working.ptr }
      (operator.result (stackOperand memory softwareStack pointer short)
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short)) = computed.mem.wstk := by
    have word := Stack.asPushWord computed.mem.wstk
    simpa [computedWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, computedHigh, computedLow, append_split] using word
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalWF, finalRF⟩ :=
    push_operand computed.mem.ram softwareStack
      (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
      (operator.result (stackOperand memory softwareStack pointer short)
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short)) short
      { computed.mem.wstk with ptr := working.ptr } { second.mem.rstk with ptr := returning.ptr }
      returnAddress selected computedCode computedHighPort computedLowPort computedMode computedPointer workingSpace
      (by dsimp; omega)
  have computedShape : computed = machine computed.mem.ram 0x28c computed.mem.wstk computed.mem.rstk := by
    cases computed
    simpa [machine] using computedPC
  have after : Reaches computed final := by
    rw [computedShape, computedRP]
    simpa only [computedWorkingEta, returningEta] using finalSteps
  have finalCode : CodeImage final.mem.ram := by
    rw [finalMem]
    have ptrAfter : 0x555 ≤ (softwareStack + 0x100#16).toNat := by bv_omega
    have dataAfter (index : Byte) : 0x555 ≤ (softwareStack + index.setWidth 16).toNat := by bv_omega
    split <;> first
      | exact ((computedCode.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))).write _ _
          (.inr (.inl (dataAfter _)))
      | exact (computedCode.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))
  refine ⟨final, before.trans (computation.trans after), finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, computedMem, combinedMem]
    rfl
  · intro address bound
    rw [finalWF _ bound, computedWF _ bound, workingFrame _ bound]
  · intro address bound
    rw [finalRF _ bound, returningFrame _ bound]

end ProgramProofs.Uxnmin
