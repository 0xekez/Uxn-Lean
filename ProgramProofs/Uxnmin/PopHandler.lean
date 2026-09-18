import ProgramProofs.Uxnmin.WordStackBlocks
import Mathlib.Tactic.Convert
import Mathlib.Tactic.SplitIfs

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem pop_operand (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (ptr : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x2ad working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.wstk.data working.ptr =
        (if short then memory (softwareStack + (pointer - 2#8).setWidth 16) else 0) ∧
      final.mem.wstk.data (working.ptr + 1#8) = memory (softwareStack + (pointer - 1#8).setWidth 16) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update memory
        (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - (if short then 2#8 else 1#8)) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code2ad : memory 0x2ad#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ae : memory 0x2ae#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2af : memory 0x2af#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b0 : memory 0x2b0#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b1 : memory 0x2b1#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b2 : memory 0x2b2#16 = 0x1d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b3 : memory 0x2b3#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b4 : memory 0x2b4#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  cases short with
  | false =>
    obtain ⟨final, steps, pc, wp, value, rp, mem, wf, rf⟩ :=
      pop_byte memory softwareStack pointer keep (Stack.push working 0) returning returnAddress
        selected code high low kept keepBound ptr
        (by simp only [Stack.push]; bv_omega) (by omega)
    have header : Reaches (machine memory 0x2ad working (Stack.pushWord returning returnAddress))
        (machine memory 0x2b5 (Stack.push working 0) (Stack.pushWord returning returnAddress)) := by
      iterate 4
        apply Reaches.next
        · simp [uxn_state, uxn_step, code2ad, code2ae, code2af, code2b0, code2b1,
            code2b2, code2b3, code2b4, mode]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc]
      exact .refl _
    refine ⟨final, header.trans steps, pc, ?_, ?_, ?_, rp, mem, ?_, rf⟩
    · simpa [Stack.push, BitVec.add_assoc] using wp
    · rw [wf _ (by simp only [Stack.push]; bv_omega)]
      simp [Stack.push]
    · simpa [Stack.push] using value
    · intro address bound
      rw [wf _ (by simp only [Stack.push]; bv_omega)]
      simp (disch := bv_omega) only [Stack.push, Function.update_of_ne]
  | true =>
    obtain ⟨final, steps, pc, wp, valueHigh, valueLow, rp, mem, wf, rf⟩ :=
      pop_word memory softwareStack pointer keep
        { working with data := Function.update working.data working.ptr 1 }
        returning returnAddress selected code high low kept keepBound ptr workingSpace returnSpace
    have header : Reaches (machine memory 0x2ad working (Stack.pushWord returning returnAddress))
        (machine memory 0x2d0 { working with data := Function.update working.data working.ptr 1 }
          (Stack.pushWord returning returnAddress)) := by
      iterate 3
        apply Reaches.next
        · simp [uxn_state, uxn_step, code2ad, code2ae, code2af, code2b0, code2b1,
            code2b2, mode]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc]
      exact .refl _
    refine ⟨final, header.trans steps, pc, wp, valueHigh, valueLow, rp, mem, ?_, rf⟩
    intro address bound
    rw [wf _ bound]
    simp (disch := bv_omega) only [Function.update_of_ne]


theorem handler_pop (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (ptr : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory 0x3bb working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update memory
        (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - (if short then 2#8 else 1#8)) ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨first, steps, pc, wp, valueHigh, valueLow, rp, mem, wf, rf⟩ :=
    pop_operand memory softwareStack pointer keep short working
      (Stack.pushWord returning returnAddress) 0x3be selected code high low mode kept keepBound ptr
      workingSpace (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have stackAfter : 0x555 ≤ (softwareStack + (0x100#16 + keep.setWidth 16)).toNat := by bv_omega
  have codeFirst : CodeImage first.mem.ram := by
    rw [mem]
    exact code.write _ _ (.inr (.inl stackAfter))
  have code3bb : memory 0x3bb#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3bc : memory 0x3bc#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3bd : memory 0x3bd#16 = 0xef#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3a2 : first.mem.ram 0x3be#16 = 0x22#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have code3a3 : first.mem.ram 0x3bf#16 = 0x6c#8 := codeFirst _ (by decide) (by decide) (by simp [MutableCode])
  have before : Reaches (machine memory 0x3bb working (Stack.pushWord returning returnAddress)) first := by
    refine .next ?_ steps
    simp [uxn_state, uxn_step, code3bb, code3bc, code3bd]
  have returnHigh : first.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : first.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningPointer : first.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using rp
  have returningFrame (address : Byte) (bound : address.toNat < returning.ptr.toNat) :
      first.mem.rstk.data address = returning.data address := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  have shape : first = machine first.mem.ram 0x3be first.mem.wstk first.mem.rstk := by
    cases first
    simpa [machine] using pc
  have connect {property : Uxn.State → Prop}
      (after : ∃ final, Reaches first final ∧ property final) :
      ∃ final, Reaches (machine memory 0x3bb working (Stack.pushWord returning returnAddress)) final ∧
        property final := by
    obtain ⟨final, after, properties⟩ := after
    exact ⟨final, before.trans after, properties⟩
  apply connect
  rw [shape]
  iterate 2
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, code3a2, code3a3, wp, returningPointer, returnHigh, returnLow]
      rfl
  exact ⟨_, .refl _, rfl, rfl, rfl, mem, codeFirst, wf, returningFrame⟩


end ProgramProofs.Uxnmin
