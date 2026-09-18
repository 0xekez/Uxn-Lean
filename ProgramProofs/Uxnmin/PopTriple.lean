import ProgramProofs.Uxnmin.StackPopPair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem Stack.asPushTriple (stack : Uxn.Stack) :
    Stack.pushWord (Stack.pushWord (Stack.pushWord { stack with ptr := stack.ptr - 6#8 }
      (stack.data (stack.ptr - 6#8) ++ stack.data (stack.ptr - 5#8)))
      (stack.data (stack.ptr - 4#8) ++ stack.data (stack.ptr - 3#8)))
      (stack.data (stack.ptr - 2#8) ++ stack.data (stack.ptr - 1#8)) = stack := by
  have lower := Stack.asPushPair { stack with ptr := stack.ptr - 2#8 }
  simp [BitVec.sub_eq_add_neg, BitVec.add_assoc] at lower ⊢
  rw [lower]
  simpa [BitVec.sub_eq_add_neg] using Stack.asPushWord stack

theorem pop_triple (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 243) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x3d7 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = 0x3e0 ∧
      final.mem.ram = Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
        (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8)) ∧
      CodeImage final.mem.ram ∧ final.mem.wstk.ptr = working.ptr + 6#8 ∧
      final.mem.rstk.ptr = returning.ptr + 2#8 ∧
      Stack.pushWord (Stack.pushWord (Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (stackOperand memory softwareStack pointer short))
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short))
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8)) short) = final.mem.wstk ∧
      Stack.pushWord { final.mem.rstk with ptr := returning.ptr } returnAddress = final.mem.rstk ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨middle, before, middlePC, middleMem, middleCode, nativeWP,
      nativeRP, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_pair StackPermutation.rot.entry (fun ram w r offset image position =>
      StackPermutation.rot.call ram offset w r image position) memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor (by omega) returnSpace
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have stackAfter : 0x555 ≤ (softwareStack + (0x100#16 + keep.setWidth 16)).toNat := by bv_omega
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have dataSeparate (index : Byte) : softwareStack + index.setWidth 16 ≠
      softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  obtain ⟨final, lastSteps, finalPC, finalWP, finalVH, finalVL, finalRP, finalMem, finalWF, finalRF⟩ :=
    pop_operand middle.mem.ram softwareStack
      (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8)) keep short
      middle.mem.wstk middle.mem.rstk 0x3e0 selected middleCode
      (by rw [middleMem, Function.update_of_ne (separate _ (by decide)), high])
      (by rw [middleMem, Function.update_of_ne (separate _ (by decide)), low])
      (by rw [middleMem, Function.update_of_ne (separate _ (by decide)), mode])
      (by rw [middleMem, Function.update_of_ne (separate _ (by decide)), kept]) keepBound
      (by rw [middleMem]; simp)
      (by rw [nativeWP]; bv_omega) (by rw [nativeRP]; bv_omega)
  have combinedMem : final.mem.ram = Function.update memory
      (softwareStack + (0x100#16 + keep.setWidth 16))
      (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8)) := by
    rw [finalMem, middleMem, Function.update_idem]
  have combinedCode : CodeImage final.mem.ram := by
    rw [combinedMem]
    exact code.write _ _ (.inr (.inl stackAfter))
  have finalWorkingPointer : final.mem.wstk.ptr = working.ptr + 6#8 := by
    rw [finalWP, nativeWP]
    simp [BitVec.add_assoc]
  have work0 : final.mem.wstk.data working.ptr = (stackOperand memory softwareStack pointer short >>> 8).setWidth 8 := by
    rw [finalWF _ (by rw [nativeWP]; bv_omega)]
    have slot := congrArg (fun s : Uxn.Stack => s.data working.ptr) workingEta
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using slot.symm
  have work1 : final.mem.wstk.data (working.ptr + 1#8) = (stackOperand memory softwareStack pointer short).setWidth 8 := by
    rw [finalWF _ (by rw [nativeWP]; bv_omega)]
    have slot := congrArg (fun s : Uxn.Stack => s.data (working.ptr + 1#8)) workingEta
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using slot.symm
  have work2 : final.mem.wstk.data (working.ptr + 2#8) = (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short >>> 8).setWidth 8 := by
    rw [finalWF _ (by rw [nativeWP]; bv_omega)]
    have slot := congrArg (fun s : Uxn.Stack => s.data (working.ptr + 2#8)) workingEta
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using slot.symm
  have work3 : final.mem.wstk.data (working.ptr + 3#8) = (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short).setWidth 8 := by
    rw [finalWF _ (by rw [nativeWP]; bv_omega)]
    have slot := congrArg (fun s : Uxn.Stack => s.data (working.ptr + 3#8)) workingEta
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using slot.symm
  have work4 : final.mem.wstk.data (working.ptr + 4#8) =
      if short then memory (softwareStack +
        (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) - 2#8).setWidth 16) else 0 := by
    rw [nativeWP] at finalVH
    rw [finalVH, middleMem]
    split <;> simp [Function.update_of_ne (dataSeparate _)]
  have work5 : final.mem.wstk.data (working.ptr + 5#8) =
      memory (softwareStack +
        (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) - 1#8).setWidth 16) := by
    rw [nativeWP] at finalVL
    simpa [BitVec.add_assoc, middleMem, Function.update_of_ne (dataSeparate _)] using finalVL
  have finalWorkingEta : Stack.pushWord (Stack.pushWord (Stack.pushWord
      { final.mem.wstk with ptr := working.ptr }
      (stackOperand memory softwareStack pointer short))
      (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short))
      (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8)) short)
      = final.mem.wstk := by
    simpa [finalWorkingPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      work0, work1, work2, work3, work4, work5, stackOperand, append_split]
      using Stack.asPushTriple final.mem.wstk
  have finalReturningPointer : final.mem.rstk.ptr = returning.ptr + 2#8 := by rw [finalRP, nativeRP]
  have returnHigh : final.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [finalRF _ (by rw [nativeRP]; bv_omega)]
    have slot := congrArg (fun s : Uxn.Stack => s.data returning.ptr) returningEta
    simpa [Stack.pushWord, Stack.push] using slot.symm
  have returnLow : final.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [finalRF _ (by rw [nativeRP]; bv_omega)]
    have slot := congrArg (fun s : Uxn.Stack => s.data (returning.ptr + 1#8)) returningEta
    simpa [Stack.pushWord, Stack.push] using slot.symm
  have finalReturningEta : Stack.pushWord { final.mem.rstk with ptr := returning.ptr } returnAddress = final.mem.rstk := by
    simpa [finalReturningPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      returnHigh, returnLow, append_split] using Stack.asPushWord final.mem.rstk
  have call : middle.mem.ram 0x3dd#16 = 0x60#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have callHigh : middle.mem.ram 0x3de#16 = 0xfe#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have callLow : middle.mem.ram 0x3df#16 = 0xcd#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have shape : middle = machine middle.mem.ram 0x3dd middle.mem.wstk middle.mem.rstk := by
    cases middle
    simpa [machine, StackPermutation.entry] using middlePC
  have after : Reaches middle final := by
    rw [shape]
    exact .next (jsi_call _ _ _ _ _ call
      (by simpa using congrArg₂ (fun high low : Byte => high ++ low) callHigh callLow)) lastSteps
  refine ⟨final, before.trans after, finalPC, combinedMem, combinedCode, finalWorkingPointer,
    finalReturningPointer, finalWorkingEta, finalReturningEta, ?_, ?_⟩
  · intro address bound
    rw [finalWF _ (by rw [nativeWP]; bv_omega), workingFrame _ bound]
  · intro address bound
    rw [finalRF _ (by rw [nativeRP]; bv_omega), returningFrame _ bound]

end ProgramProofs.Uxnmin
