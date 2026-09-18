import ProgramProofs.Uxnmin.PushOperand

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

set_option maxHeartbeats 200000 in
theorem handler_inc (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
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
      (machine memory 0x3b4 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
          (pointer - (if short then 2#8 else 1#8))) softwareStack
        (if keep = 0 then pointer - (if short then 2#8 else 1#8) else pointer)
        (stackOperand memory softwareStack pointer short + 1) short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨first, steps, pc, wp, valueHigh, valueLow, rp, mem, wf, rf⟩ :=
    pop_operand memory softwareStack pointer keep short working
      (Stack.pushWord returning returnAddress) 0x3b7 selected code high low mode kept keepBound cursor
      (by omega) (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have stackAfter : 0x555 ≤ (softwareStack + (0x100#16 + keep.setWidth 16)).toNat := by bv_omega
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have codeFirst : CodeImage first.mem.ram := by
    rw [mem]
    exact code.write _ _ (.inr (.inl stackAfter))
  have firstHigh : first.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [mem, Function.update_of_ne (separate _ (by decide)), high]
  have firstLow : first.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [mem, Function.update_of_ne (separate _ (by decide)), low]
  have firstMode : first.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [mem, Function.update_of_ne (separate _ (by decide)), mode]
  have firstPointer : first.mem.ram (softwareStack + 0x100#16) =
      if keep = 0 then pointer - (if short then 2#8 else 1#8) else pointer := by
    rw [mem]
    by_cases zero : keep = 0
    · simp [zero]
    · rw [Function.update_of_ne (by bv_omega), ptr]
      rw [if_neg zero]
  have returnHigh : first.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : first.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningPointer : first.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using rp
  have returningEta : Stack.pushWord { first.mem.rstk with ptr := returning.ptr } returnAddress =
      first.mem.rstk := by
    dsimp [Stack.pushWord, Stack.push]
    rw [← returnHigh, Function.update_eq_self, ← returnLow, Function.update_eq_self]
    simpa [BitVec.add_assoc] using
      congrArg (fun pointer => { first.mem.rstk with ptr := pointer }) returningPointer.symm
  have returningFrame (address : Byte) (bound : address.toNat < returning.ptr.toNat) :
      first.mem.rstk.data address = returning.data address := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalWF, finalRF⟩ :=
    push_operand first.mem.ram softwareStack
      (if keep = 0 then pointer - (if short then 2#8 else 1#8) else pointer)
      (stackOperand memory softwareStack pointer short + 1) short
      { first.mem.wstk with ptr := working.ptr } { first.mem.rstk with ptr := returning.ptr }
      returnAddress selected codeFirst firstHigh firstLow firstMode firstPointer workingSpace (by dsimp; omega)
  have code3b4 : memory 0x3b4#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b5 : memory 0x3b5#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b6 : memory 0x3b6#16 = 0xf6#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b7 : first.mem.ram 0x3b7#16 = 0x21#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3b8 : first.mem.ram 0x3b8#16 = 0x40#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3b9 : first.mem.ram 0x3b9#16 = 0xfe#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3ba : first.mem.ram 0x3ba#16 = 0xd1#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have before : Reaches (machine memory 0x3b4 working (Stack.pushWord returning returnAddress)) first := by
    refine .next ?_ steps
    simp [uxn_state, uxn_step, code3b4, code3b5, code3b6]
  have shape : first = machine first.mem.ram 0x3b7 first.mem.wstk first.mem.rstk := by
    cases first
    simpa [machine] using pc
  have after : Reaches first final := by
    rw [shape]
    apply Reaches.next
    · simp [uxn_state, uxn_step, code3b7, wp, valueHigh, valueLow]
      rfl
    apply Reaches.next
    · simp [uxn_state, uxn_step, code3b8, code3b9, code3ba]
      rfl
    rw [returningEta] at finalSteps
    simpa [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, BitVec.sub_eq_add_neg, stackOperand]
      using finalSteps
  have finalCode : CodeImage final.mem.ram := by
    rw [finalMem]
    have ptrAfter : 0x555 ≤ (softwareStack + 0x100#16).toNat := by bv_omega
    have dataAfter (index : Byte) : 0x555 ≤ (softwareStack + index.setWidth 16).toNat := by bv_omega
    split <;> first
      | exact ((codeFirst.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))).write _ _
          (.inr (.inl (dataAfter _)))
      | exact (codeFirst.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, mem]
    rfl
  · intro address bound
    rw [finalWF _ bound, wf _ bound]
  · intro address bound
    rw [finalRF _ bound, returningFrame _ bound]


end ProgramProofs.Uxnmin
