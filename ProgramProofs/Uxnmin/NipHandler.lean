import ProgramProofs.Uxnmin.StackHandlers
import ProgramProofs.Uxnmin.StackPopPair

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem handler_nip (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 245) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory 0x3c0 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
          (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8))) softwareStack
        (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
        (stackOperand memory softwareStack pointer short) short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨middle, before, middlePC, middleMem, middleCode, nativeWP,
      nativeRP, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_pair StackPermutation.nip.entry (fun ram w r offset image position =>
      StackPermutation.nip.call ram offset w r image position) memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor (by omega) returnSpace
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have middleHigh : middle.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [middleMem, Function.update_of_ne (separate _ (by decide)), high]
  have middleLow : middle.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [middleMem, Function.update_of_ne (separate _ (by decide)), low]
  have middleMode : middle.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [middleMem, Function.update_of_ne (separate _ (by decide)), mode]
  have middlePointer : middle.mem.ram (softwareStack + 0x100#16) =
      if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer := by
    rw [middleMem]
    by_cases zero : keep = 0
    · simp [zero]
    · rw [Function.update_of_ne (by bv_omega), ptr, if_neg zero]
  have code3c6 : middle.mem.ram 0x3c6#16 = 0x22#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3c7 : middle.mem.ram 0x3c7#16 = 0x40#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3c8 : middle.mem.ram 0x3c8#16 = 0xfe#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3c9 : middle.mem.ram 0x3c9#16 = 0xc2#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have workHigh : middle.mem.wstk.data working.ptr =
      (stackOperand memory softwareStack pointer short >>> 8).setWidth 8 := by
    have atHigh := congrArg (fun s : Uxn.Stack => s.data working.ptr) workingEta
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using atHigh.symm
  have workLow : middle.mem.wstk.data (working.ptr + 1#8) =
      (stackOperand memory softwareStack pointer short).setWidth 8 := by
    have atLow := congrArg (fun s : Uxn.Stack => s.data (working.ptr + 1#8)) workingEta
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using atLow.symm
  have lowerEta : Stack.pushWord { middle.mem.wstk with ptr := working.ptr }
      (stackOperand memory softwareStack pointer short) =
      { middle.mem.wstk with ptr := working.ptr + 2#8 } := by
    simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc, workHigh, workLow, append_split]
      using Stack.asPushWord { middle.mem.wstk with ptr := working.ptr + 2#8 }
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalWF, finalRF⟩ :=
    push_operand middle.mem.ram softwareStack
      (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
      (stackOperand memory softwareStack pointer short) short
      { middle.mem.wstk with ptr := working.ptr } { middle.mem.rstk with ptr := returning.ptr }
      returnAddress selected middleCode middleHigh middleLow middleMode middlePointer (by dsimp; omega) (by dsimp; omega)
  have shape : middle = machine middle.mem.ram 0x3c6 middle.mem.wstk middle.mem.rstk := by
    cases middle
    simpa [machine, StackPermutation.entry] using middlePC
  have after : Reaches middle final := by
    rw [shape]
    refine Reaches.next (t := machine middle.mem.ram 0x3c7
      { middle.mem.wstk with ptr := working.ptr + 2#8 } middle.mem.rstk) ?_ ?_
    · simp [uxn_state, uxn_step, code3c6, nativeWP, BitVec.add_assoc]
    refine Reaches.next (t := machine middle.mem.ram 0x28c
      { middle.mem.wstk with ptr := working.ptr + 2#8 } middle.mem.rstk) ?_ ?_
    · simp [uxn_state, uxn_step, code3c7, code3c8, code3c9]
    simpa only [lowerEta, returningEta] using finalSteps
  have finalCode : CodeImage final.mem.ram := by
    rw [finalMem]
    have ptrAfter : 0x555 ≤ (softwareStack + 0x100#16).toNat := by bv_omega
    have dataAfter (index : Byte) : 0x555 ≤ (softwareStack + index.setWidth 16).toNat := by bv_omega
    split <;> first
      | exact ((middleCode.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))).write _ _
          (.inr (.inl (dataAfter _)))
      | exact (middleCode.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, middleMem]
    rfl
  · intro address bound
    rw [finalWF _ bound, workingFrame _ bound]
  · intro address bound
    rw [finalRF _ bound, returningFrame _ bound]

end ProgramProofs.Uxnmin
