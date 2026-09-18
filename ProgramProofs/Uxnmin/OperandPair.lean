import ProgramProofs.Uxnmin.PushOperand
import ProgramProofs.Uxnmin.MixedOperands
import ProgramProofs.Uxnmin.StackView

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem jsi_call (memory : Word → Byte) (pc target : Word) (working returning : Uxn.Stack)
    (instruction : memory pc = 0x60)
    (immediate : memory (pc + 1) ++ memory (pc + 2) = target - (pc + 3)) :
    Uxn.step (machine memory pc working returning) = .done (.next
      (machine memory target working (Stack.pushWord returning (pc + 3)))) := by
  simp at immediate
  simp [uxn_state, uxn_step, instruction]
  rw [immediate]
  bv_omega

theorem Stack.asPushPair (stack : Uxn.Stack) :
    Stack.pushWord (Stack.pushWord { stack with ptr := stack.ptr - 4#8 }
      (stack.data (stack.ptr - 4#8) ++ stack.data (stack.ptr - 3#8)))
      (stack.data (stack.ptr - 2#8) ++ stack.data (stack.ptr - 1#8)) = stack := by
  have lower := Stack.asPushWord { stack with ptr := stack.ptr - 2#8 }
  simp [BitVec.sub_eq_add_neg, BitVec.add_assoc] at lower ⊢
  rw [lower]
  simpa [BitVec.sub_eq_add_neg] using Stack.asPushWord stack


def OperandPairCode (entry : Word) (firstKind secondKind : OperandKind) : Prop :=
  ∀ (memory : Word → Byte) (working returning : Uxn.Stack) (offset : Word),
    CodeImage memory → (offset = 0 ∨ offset = 3) →
    Uxn.step (machine memory (entry + offset) working returning) = .done (.next
      (machine memory (if offset = 0 then firstKind.entry else secondKind.entry) working
        (Stack.pushWord returning (entry + offset + 3))))

theorem pop_operand_pair (firstKind secondKind : OperandKind)
    (entry : Word) (calls : OperandPairCode entry firstKind secondKind) (memory : Word → Byte)
    (softwareStack : Word) (pointer keep : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory entry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = entry + 6 ∧
      final.mem.ram = Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
        (pointer - (if firstKind.short short then 2#8 else 1#8) - (if secondKind.short short then 2#8 else 1#8)) ∧
      CodeImage final.mem.ram ∧
      final.mem.wstk.ptr = working.ptr + 4#8 ∧
      final.mem.rstk.ptr = returning.ptr + 2#8 ∧
      Stack.pushWord (Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (stackOperand memory softwareStack pointer (firstKind.short short)))
        (stackOperand memory softwareStack (pointer - (if firstKind.short short then 2#8 else 1#8)) (secondKind.short short)) = final.mem.wstk ∧
      Stack.pushWord { final.mem.rstk with ptr := returning.ptr } returnAddress = final.mem.rstk ∧
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
  have dataSeparate (index : Byte) : softwareStack + index.setWidth 16 ≠
      softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  obtain ⟨first, firstSteps, firstPC, firstWP, firstVH, firstVL, firstRP, firstMem, firstWF, firstRF⟩ :=
    pop_operand_kind firstKind memory softwareStack pointer keep short working
      (Stack.pushWord returning returnAddress) (entry + 3) selected code high low mode kept keepBound cursor
      (by omega) (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have firstCode : CodeImage first.mem.ram := by
    rw [firstMem]
    exact code.write _ _ (.inr (.inl stackAfter))
  have firstHigh : first.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), high]
  have firstLow : first.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), low]
  have firstMode : first.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), mode]
  have firstKeep : first.mem.ram 0x2bf#16 = keep := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), kept]
  have firstCursor : first.mem.ram (softwareStack + (0x100#16 + keep.setWidth 16)) =
      pointer - (if firstKind.short short then 2#8 else 1#8) := by rw [firstMem]; simp
  obtain ⟨second, secondSteps, secondPC, secondWP, secondVH, secondVL, secondRP, secondMem, secondWF, secondRF⟩ :=
    pop_operand_kind secondKind first.mem.ram softwareStack (pointer - (if firstKind.short short then 2#8 else 1#8)) keep short
      first.mem.wstk first.mem.rstk (entry + 6) selected firstCode firstHigh firstLow firstMode
      firstKeep keepBound firstCursor
      (by rw [firstWP]; bv_omega)
      (by rw [firstRP]; simp only [Stack.pushWord, Stack.push]; bv_omega)
  have combinedMem : second.mem.ram = Function.update memory
      (softwareStack + (0x100#16 + keep.setWidth 16))
      (pointer - (if firstKind.short short then 2#8 else 1#8) - (if secondKind.short short then 2#8 else 1#8)) := by
    rw [secondMem, firstMem, Function.update_idem]
  have combinedCode : CodeImage second.mem.ram := by
    rw [combinedMem]
    exact code.write _ _ (.inr (.inl stackAfter))
  have workingPointer : second.mem.wstk.ptr = working.ptr + 4#8 := by
    rw [secondWP, firstWP]
    simp [BitVec.add_assoc]
  have workingFirstHigh : second.mem.wstk.data working.ptr =
      if firstKind.short short then memory (softwareStack + (pointer - 2#8).setWidth 16) else 0 := by
    rw [secondWF _ (by rw [firstWP]; bv_omega), firstVH]
  have workingFirstLow : second.mem.wstk.data (working.ptr + 1#8) =
      memory (softwareStack + (pointer - 1#8).setWidth 16) := by
    rw [secondWF _ (by rw [firstWP]; bv_omega), firstVL]
  have workingSecondHigh : second.mem.wstk.data (working.ptr + 2#8) =
      if secondKind.short short then memory (softwareStack + (pointer - (if firstKind.short short then 2#8 else 1#8) - 2#8).setWidth 16) else 0 := by
    rw [firstWP] at secondVH
    rw [secondVH, firstMem]
    split <;> simp [Function.update_of_ne (dataSeparate _)]
  have workingSecondLow : second.mem.wstk.data (working.ptr + 3#8) =
      memory (softwareStack + (pointer - (if firstKind.short short then 2#8 else 1#8) - 1#8).setWidth 16) := by
    rw [firstWP] at secondVL
    simpa [BitVec.add_assoc, firstMem, Function.update_of_ne (dataSeparate _)] using secondVL
  have workingEta : Stack.pushWord
      (Stack.pushWord { second.mem.wstk with ptr := working.ptr }
        (stackOperand memory softwareStack pointer (firstKind.short short)))
      (stackOperand memory softwareStack (pointer - (if firstKind.short short then 2#8 else 1#8)) (secondKind.short short)) = second.mem.wstk := by
    have pair := Stack.asPushPair second.mem.wstk
    simpa [workingPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, workingFirstHigh,
      workingFirstLow, workingSecondHigh, workingSecondLow, stackOperand] using pair
  have workingFrame (address : Byte) (bound : address.toNat < working.ptr.toNat) :
      second.mem.wstk.data address = working.data address := by
    rw [secondWF _ (by rw [firstWP]; bv_omega), firstWF _ bound]
  have returningPointer : second.mem.rstk.ptr = returning.ptr + 2#8 := by
    rw [secondRP, firstRP]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have returningFrame (address : Byte) (bound : address.toNat < (Stack.pushWord returning returnAddress).ptr.toNat) :
      second.mem.rstk.data address = (Stack.pushWord returning returnAddress).data address := by
    rw [secondRF _ (by rw [firstRP]; exact bound), firstRF _ bound]
  have returnHigh : second.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [returningFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : second.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [returningFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningEta : Stack.pushWord { second.mem.rstk with ptr := returning.ptr } returnAddress = second.mem.rstk := by
    have word := Stack.asPushWord second.mem.rstk
    simpa [returningPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      returnHigh, returnLow, append_split] using word
  have firstShape : first = machine first.mem.ram (entry + 3) first.mem.wstk first.mem.rstk := by
    cases first
    simpa [machine] using firstPC
  have secondShape : second = machine second.mem.ram (entry + 6) second.mem.wstk second.mem.rstk := by
    cases second
    simpa [machine] using secondPC
  have before : Reaches (machine memory entry working (Stack.pushWord returning returnAddress)) second := by
    refine Reaches.trans (.next ?_ firstSteps) ?_
    · simpa using calls memory working (Stack.pushWord returning returnAddress) 0 code (.inl rfl)
    · rw [firstShape]
      refine .next ?_ secondSteps
      simpa [BitVec.add_assoc] using calls first.mem.ram first.mem.wstk first.mem.rstk 3 firstCode (.inr rfl)
  refine ⟨second, before, secondPC, combinedMem, combinedCode, workingPointer,
    returningPointer, workingEta, returningEta, workingFrame, ?_⟩
  intro address bound
  rw [returningFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
  simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
