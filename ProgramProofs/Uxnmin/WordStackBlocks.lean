import ProgramProofs.Uxnmin.StackBlocks

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem pop_word (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (ptr : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x2d0 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.wstk.data working.ptr = memory (softwareStack + (pointer - 2#8).setWidth 16) ∧
      final.mem.wstk.data (working.ptr + 1#8) = memory (softwareStack + (pointer - 1#8).setWidth 16) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update memory
        (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - 2#8) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have stackAfter : 0x555 ≤ (softwareStack + (0x100#16 + keep.setWidth 16)).toNat := by
    bv_omega
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have dataSeparate (index : Byte) : softwareStack + index.setWidth 16 ≠
      softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have outerSpace : (Stack.pushWord returning returnAddress).ptr.toNat ≤ 251 := by
    simp only [Stack.pushWord, Stack.push]
    bv_omega
  obtain ⟨first, firstSteps, firstPC, firstWP, firstValue, firstRP, firstMem,
      firstWFrame, firstRFrame⟩ :=
    pop_byte memory softwareStack pointer keep working (Stack.pushWord returning returnAddress)
      0x2d3 selected code high low kept keepBound ptr (by omega) outerSpace
  have firstCode : CodeImage first.mem.ram := by
    rw [firstMem]
    exact code.write _ _ (.inr (.inl stackAfter))
  have firstHigh : first.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), high]
  have firstLow : first.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), low]
  have firstKeep : first.mem.ram 0x2bf#16 = keep := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)), kept]
  have firstPtr : first.mem.ram (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer - 1#8 := by
    rw [firstMem]
    simp
  obtain ⟨second, secondSteps, secondPC, secondWP, secondValue, secondRP, secondMem,
      secondWFrame, secondRFrame⟩ :=
    pop_byte first.mem.ram softwareStack (pointer - 1#8) keep first.mem.wstk first.mem.rstk
      0x2d6 selected firstCode firstHigh firstLow firstKeep keepBound firstPtr
      (by rw [firstWP]; bv_omega) (by rw [firstRP]; exact outerSpace)
  have secondCode : CodeImage second.mem.ram := by
    rw [secondMem]
    exact firstCode.write _ _ (.inr (.inl stackAfter))
  have secondMemory : second.mem.ram = Function.update memory
      (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - 2#8) := by
    rw [secondMem, firstMem, Function.update_idem]
    congr 1
    bv_omega
  have secondWorking : second.mem.wstk.ptr = working.ptr + 2#8 := by
    rw [secondWP, firstWP]
    bv_omega
  have secondReturning : second.mem.rstk.ptr = returning.ptr + 2#8 := by
    rw [secondRP, firstRP]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have secondHigh : second.mem.wstk.data (working.ptr + 1#8) =
      memory (softwareStack + (pointer - 2#8).setWidth 16) := by
    rw [firstWP] at secondValue
    rw [secondValue, firstMem, Function.update_of_ne (dataSeparate _)]
    congr 2
    bv_omega
  have secondLow : second.mem.wstk.data working.ptr =
      memory (softwareStack + (pointer - 1#8).setWidth 16) := by
    rw [secondWFrame _ (by rw [firstWP]; bv_omega), firstValue]
  have returnHigh : second.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [secondRFrame _ (by rw [firstRP]; simp only [Stack.pushWord, Stack.push]; bv_omega)]
    rw [firstRFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : second.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [secondRFrame _ (by rw [firstRP]; simp only [Stack.pushWord, Stack.push]; bv_omega)]
    rw [firstRFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have workingFrame (address : Byte) (bound : address.toNat < working.ptr.toNat) :
      second.mem.wstk.data address = working.data address := by
    rw [secondWFrame _ (by rw [firstWP]; bv_omega), firstWFrame _ bound]
  have returningFrame (address : Byte) (bound : address.toNat < returning.ptr.toNat) :
      second.mem.rstk.data address = returning.data address := by
    rw [secondRFrame _ (by rw [firstRP]; simp only [Stack.pushWord, Stack.push]; bv_omega)]
    rw [firstRFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  have firstShape : first = machine first.mem.ram 0x2d3 first.mem.wstk first.mem.rstk := by
    cases first
    simpa [machine] using firstPC
  have secondShape : second = machine second.mem.ram 0x2d6 second.mem.wstk second.mem.rstk := by
    cases second
    simpa [machine] using secondPC
  have code2d0 : memory 0x2d0#16 = 0x60#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2d1 : memory 0x2d1#16 = 0xff#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2d2 : memory 0x2d2#16 = 0xe2#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b7 : first.mem.ram 0x2d3#16 = 0x60#8 :=
    firstCode _ (by decide) (by decide) (by simp [MutableCode])
  have code2b8 : first.mem.ram 0x2d4#16 = 0xff#8 :=
    firstCode _ (by decide) (by decide) (by simp [MutableCode])
  have code2b9 : first.mem.ram 0x2d5#16 = 0xdf#8 :=
    firstCode _ (by decide) (by decide) (by simp [MutableCode])
  have code2ba : second.mem.ram 0x2d6#16 = 0x04#8 :=
    secondCode _ (by decide) (by decide) (by simp [MutableCode])
  have code2bb : second.mem.ram 0x2d7#16 = 0x6c#8 :=
    secondCode _ (by decide) (by decide) (by simp [MutableCode])
  have before : Reaches (machine memory 0x2d0 working (Stack.pushWord returning returnAddress)) second := by
    refine Reaches.trans (.next ?_ firstSteps) ?_
    · simp [uxn_state, uxn_step, code2d0, code2d1, code2d2]
    · rw [firstShape]
      refine .next ?_ secondSteps
      simp [uxn_state, uxn_step, code2b7, code2b8, code2b9]
  have connect {property : Uxn.State → Prop}
      (after : ∃ final, Reaches second final ∧ property final) :
      ∃ final, Reaches (machine memory 0x2d0 working (Stack.pushWord returning returnAddress)) final ∧
        property final := by
    obtain ⟨final, steps, properties⟩ := after
    exact ⟨final, before.trans steps, properties⟩
  apply connect
  rw [secondShape]
  iterate 2
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, code2ba, code2bb, secondWorking, secondReturning,
        secondHigh, secondLow, returnHigh, returnLow]
      rfl
  refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, secondMemory, ?_, ?_⟩
  · simp [BitVec.sub_eq_add_neg]
  · simp [BitVec.sub_eq_add_neg]
  · intro address bound
    simpa (disch := bv_omega) only [Function.update_of_ne] using workingFrame address bound
  · exact returningFrame


end ProgramProofs.Uxnmin
