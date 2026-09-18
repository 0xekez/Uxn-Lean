import ProgramProofs.Uxnmin.PushTriple
import ProgramProofs.Uxnmin.StackPopPair
import ProgramProofs.Host.Permutation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem handler_ovr (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 243) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory 0x3f5 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (storeStackOperand
          (storeStackOperand
            (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
              (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8))) softwareStack
            (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
            (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short) short)
          softwareStack
          ((if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer) +
            (if short then 2#8 else 1#8))
          (stackOperand memory softwareStack pointer short) short)
        softwareStack
        ((if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer) +
          (if short then 2#8 else 1#8) + (if short then 2#8 else 1#8))
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short) short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨middle, before, middlePC, middleMem, middleCode, nativeWP,
      nativeRP, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_pair StackPermutation.ovr.entry (fun ram w r offset image position =>
      StackPermutation.ovr.call ram offset w r image position) memory softwareStack pointer keep short
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
  have code3fb : middle.mem.ram 0x3fb#16 = 0x24#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3fc : middle.mem.ram 0x3fc#16 = 0x27#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalCode, finalWF, finalRF⟩ :=
    push_triple .ovr middle.mem.ram softwareStack
      (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
      (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short)
      (stackOperand memory softwareStack pointer short)
      (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short) short
      { middle.mem.wstk with ptr := working.ptr } { middle.mem.rstk with ptr := returning.ptr }
      returnAddress selected middleCode middleHigh middleLow middleMode middlePointer workingSpace returnSpace
  have shape : middle = machine middle.mem.ram 0x3fb middle.mem.wstk middle.mem.rstk := by
    cases middle
    simpa [machine, StackPermutation.entry] using middlePC
  have after : Reaches middle final := by
    rw [shape, ← workingEta, ← returningEta]
    refine .next (native_swp _ _ _ _ _ _ code3fb) ?_
    exact .next (native_ovr _ _ _ _ _ _ code3fc) finalSteps
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, middleMem]
  · intro address bound
    rw [finalWF _ bound, workingFrame _ bound]
  · intro address bound
    rw [finalRF _ bound, returningFrame _ bound]

end ProgramProofs.Uxnmin
