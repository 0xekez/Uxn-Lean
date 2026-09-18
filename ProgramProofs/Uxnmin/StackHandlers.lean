import ProgramProofs.Uxnmin.StackPopPair
import ProgramProofs.Uxnmin.StackMemory
import ProgramProofs.Uxnmin.StackView
import ProgramProofs.Host.Permutation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

private theorem update_pair_repeat (data : Byte → Byte) (pointer high low : Byte) :
    Function.update
      (Function.update (Function.update (Function.update data pointer high) (pointer + 1#8) low)
        pointer high) (pointer + 1#8) low =
      Function.update (Function.update data pointer high) (pointer + 1#8) low := by
  funext index
  by_cases first : index = pointer <;> by_cases second : index = pointer + 1#8 <;>
    simp [Function.update_apply, first, second]

private theorem jmi_jump (memory : Word → Byte) (pc target : Word)
    (working returning : Uxn.Stack) (instruction : memory pc = 0x40)
    (immediate : memory (pc + 1) ++ memory (pc + 2) = target - (pc + 3)) :
    Uxn.step (machine memory pc working returning) = .done (.next
      (machine memory target working returning)) := by
  simp at immediate
  simp [uxn_state, uxn_step, instruction]
  rw [immediate]
  bv_omega

/-- A pair of calls to the push routine preserves the native caller's live frames. -/
theorem push_pair (memory : Word → Byte) (softwareStack : Word) (pointer : Byte)
    (first second : Word) (short : Bool) (working returning : Uxn.Stack)
    (returnAddress callPC : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (call : memory callPC = 0x60)
    (callOffset : memory (callPC + 1) ++ memory (callPC + 2) = 0x28c - (callPC + 3))
    (jump : memory (callPC + 3) = 0x40)
    (jumpOffset : memory (callPC + 4) ++ memory (callPC + 5) = 0x28c - (callPC + 6))
    (callLow : (callPC + 3).toNat < 0x555)
    (offsetLow : (callPC + 4).toNat < 0x555 ∧ (callPC + 5).toNat < 0x555)
    (workingSpace : working.ptr.toNat ≤ 245) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory callPC (Stack.pushWord (Stack.pushWord working first) second)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (storeStackOperand memory softwareStack pointer second short) softwareStack
        (pointer + (if short then 2#8 else 1#8)) first short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨middle, firstSteps, firstPC, firstWP, firstRP, firstMem, firstWF, firstRF⟩ :=
    push_operand memory softwareStack pointer second short (Stack.pushWord working first)
      (Stack.pushWord returning returnAddress) (callPC + 3) selected code high low mode ptr
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have before : Reaches
      (machine memory callPC (Stack.pushWord (Stack.pushWord working first) second)
        (Stack.pushWord returning returnAddress)) middle :=
    .next (jsi_call _ _ _ _ _ call callOffset) firstSteps
  have middleMem : middle.mem.ram = storeStackOperand memory softwareStack pointer second short := firstMem
  have middleCode : CodeImage middle.mem.ram := by
    rw [middleMem]
    exact store_operand_code _ _ _ _ _ selected code
  have reads (address : Word) (bound : address.toNat < 0x555) :
      middle.mem.ram address = memory address := by
    rw [middleMem]
    exact store_operand_frame _ _ _ _ _ selected address bound
  have middlePointer : middle.mem.ram (softwareStack + 0x100#16) =
      pointer + (if short then 2#8 else 1#8) := by
    rw [middleMem]
    exact store_operand_pointer _ _ _ _ _
  have nativeWP : middle.mem.wstk.ptr = working.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using firstWP
  have nativeRP : middle.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using firstRP
  have workHigh : middle.mem.wstk.data working.ptr = (first >>> 8).setWidth 8 := by
    rw [firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have workLow : middle.mem.wstk.data (working.ptr + 1#8) = first.setWidth 8 := by
    rw [firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnHigh : middle.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : middle.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have workingEta : Stack.pushWord { middle.mem.wstk with ptr := working.ptr } first = middle.mem.wstk := by
    simpa [nativeWP, workHigh, workLow, BitVec.sub_eq_add_neg, BitVec.add_assoc, append_split]
      using Stack.asPushWord middle.mem.wstk
  have returningEta : Stack.pushWord { middle.mem.rstk with ptr := returning.ptr } returnAddress = middle.mem.rstk := by
    simpa [nativeRP, returnHigh, returnLow, BitVec.sub_eq_add_neg, BitVec.add_assoc, append_split]
      using Stack.asPushWord middle.mem.rstk
  obtain ⟨final, lastSteps, finalPC, finalWP, finalRP, finalMem, finalWF, finalRF⟩ :=
    push_operand middle.mem.ram softwareStack (pointer + (if short then 2#8 else 1#8))
      first short { middle.mem.wstk with ptr := working.ptr } { middle.mem.rstk with ptr := returning.ptr }
      returnAddress selected middleCode
      (by rw [reads _ (by decide), high]) (by rw [reads _ (by decide), low])
      (by rw [reads _ (by decide), mode]) middlePointer (by dsimp; omega) (by dsimp; omega)
  have shape : middle = machine middle.mem.ram (callPC + 3) middle.mem.wstk middle.mem.rstk := by
    cases middle
    simpa [machine] using firstPC
  have after : Reaches middle final := by
    rw [shape]
    refine Reaches.next (t := machine middle.mem.ram 0x28c middle.mem.wstk middle.mem.rstk) ?_ ?_
    · apply jmi_jump
      · rw [reads _ callLow]
        exact jump
      · have immediate : middle.mem.ram (callPC + 4) ++ middle.mem.ram (callPC + 5) =
            0x28c - (callPC + 6) := by
          rw [reads _ offsetLow.1, reads _ offsetLow.2, jumpOffset]
        simpa [BitVec.add_assoc] using immediate
    · simpa only [workingEta, returningEta] using lastSteps
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, ?_, ?_, ?_⟩
  · rw [finalMem, middleMem]
    rfl
  · rw [finalMem]
    exact store_operand_code _ _ _ _ _ selected middleCode
  · intro address bound
    rw [finalWF _ bound, firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  · intro address bound
    rw [finalRF _ bound, firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

theorem handler_dup (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
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
      (machine memory 0x3eb working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (storeStackOperand
          (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
            (pointer - (if short then 2#8 else 1#8))) softwareStack
          (if keep = 0 then pointer - (if short then 2#8 else 1#8) else pointer)
          (stackOperand memory softwareStack pointer short) short)
        softwareStack
        ((if keep = 0 then pointer - (if short then 2#8 else 1#8) else pointer) +
          (if short then 2#8 else 1#8))
        (stackOperand memory softwareStack pointer short) short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨first, steps, pc, wp, valueHigh, valueLow, rp, mem, wf, rf⟩ :=
    pop_operand memory softwareStack pointer keep short working
      (Stack.pushWord returning returnAddress) 0x3ee selected code high low mode kept keepBound cursor
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
    · rw [Function.update_of_ne (by bv_omega), ptr, if_neg zero]
  have returnHigh : first.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : first.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningPointer : first.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using rp
  have returningEta : Stack.pushWord { first.mem.rstk with ptr := returning.ptr } returnAddress = first.mem.rstk := by
    simpa [returningPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      returnHigh, returnLow, append_split] using Stack.asPushWord first.mem.rstk
  have workingEta : Stack.pushWord { first.mem.wstk with ptr := working.ptr }
      (stackOperand memory softwareStack pointer short) = first.mem.wstk := by
    simpa [wp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      valueHigh, valueLow, stackOperand] using Stack.asPushWord first.mem.wstk
  have code3eb : memory 0x3eb#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ec : memory 0x3ec#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ed : memory 0x3ed#16 = 0xbf#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ee : first.mem.ram 0x3ee#16 = 0x26#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3ef : first.mem.ram 0x3ef#16 = 0x60#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3f0 : first.mem.ram 0x3f0#16 = 0xfe#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3f1 : first.mem.ram 0x3f1#16 = 0x9a#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3f2 : first.mem.ram 0x3f2#16 = 0x40#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3f3 : first.mem.ram 0x3f3#16 = 0xfe#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3f4 : first.mem.ram 0x3f4#16 = 0x97#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalCode, finalWF, finalRF⟩ :=
    push_pair first.mem.ram softwareStack
      (if keep = 0 then pointer - (if short then 2#8 else 1#8) else pointer)
      (stackOperand memory softwareStack pointer short)
      (stackOperand memory softwareStack pointer short) short
      { first.mem.wstk with ptr := working.ptr } { first.mem.rstk with ptr := returning.ptr }
      returnAddress 0x3ef selected codeFirst firstHigh firstLow firstMode firstPointer code3ef
      (by simpa using congrArg₂ (fun high low : Byte => high ++ low) code3f0 code3f1)
      code3f2 (by simpa using congrArg₂ (fun high low : Byte => high ++ low) code3f3 code3f4)
      (by decide) (by decide) workingSpace returnSpace
  have before : Reaches (machine memory 0x3eb working (Stack.pushWord returning returnAddress)) first := by
    refine .next ?_ steps
    simp [uxn_state, uxn_step, code3eb, code3ec, code3ed]
  have shape : first = machine first.mem.ram 0x3ee first.mem.wstk first.mem.rstk := by
    cases first
    simpa [machine] using pc
  have after : Reaches first final := by
    rw [shape, ← workingEta, ← returningEta]
    apply Reaches.next
    · simp [uxn_state, uxn_step, code3ee, append_split]
      rfl
    simpa [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split, update_pair_repeat] using finalSteps
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, mem]
  · intro address bound
    rw [finalWF _ bound, wf _ bound]
  · intro address bound
    rw [finalRF _ bound, rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]


/-- SWP's two operands are copied through the native stack and written back in reverse order. -/
theorem handler_swp (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
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
      (machine memory 0x3ca working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (storeStackOperand
          (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
            (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8))) softwareStack
          (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
          (stackOperand memory softwareStack pointer short) short)
        softwareStack
        ((if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer) +
          (if short then 2#8 else 1#8))
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short) short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨middle, before, middlePC, middleMem, middleCode, nativeWP,
      nativeRP, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_pair StackPermutation.swp.entry (fun ram w r offset image position =>
      StackPermutation.swp.call ram offset w r image position) memory softwareStack pointer keep short
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
  have code3d0 : middle.mem.ram 0x3d0#16 = 0x24#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3d1 : middle.mem.ram 0x3d1#16 = 0x60#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3d2 : middle.mem.ram 0x3d2#16 = 0xfe#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3d3 : middle.mem.ram 0x3d3#16 = 0xb8#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3d4 : middle.mem.ram 0x3d4#16 = 0x40#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3d5 : middle.mem.ram 0x3d5#16 = 0xfe#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  have code3d6 : middle.mem.ram 0x3d6#16 = 0xb5#8 := middleCode _ (by decide) (by decide) (by simp [MutableCode])
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalCode, finalWF, finalRF⟩ :=
    push_pair middle.mem.ram softwareStack
      (if keep = 0 then pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8) else pointer)
      (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short)
      (stackOperand memory softwareStack pointer short) short
      { middle.mem.wstk with ptr := working.ptr } { middle.mem.rstk with ptr := returning.ptr }
      returnAddress 0x3d1 selected middleCode middleHigh middleLow middleMode middlePointer code3d1
      (by simpa using congrArg₂ (fun high low : Byte => high ++ low) code3d2 code3d3)
      code3d4 (by simpa using congrArg₂ (fun high low : Byte => high ++ low) code3d5 code3d6)
      (by decide) (by decide) workingSpace returnSpace
  have shape : middle = machine middle.mem.ram 0x3d0 middle.mem.wstk middle.mem.rstk := by
    cases middle
    simpa [machine, StackPermutation.entry] using middlePC
  have after : Reaches middle final := by
    rw [shape, ← workingEta, ← returningEta]
    exact .next (native_swp _ _ _ _ _ _ code3d0) finalSteps
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, middleMem]
  · intro address bound
    rw [finalWF _ bound, workingFrame _ bound]
  · intro address bound
    rw [finalRF _ bound, returningFrame _ bound]

end ProgramProofs.Uxnmin
