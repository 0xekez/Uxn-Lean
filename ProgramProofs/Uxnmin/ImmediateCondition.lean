import ProgramProofs.Uxnmin.MixedOperands
import ProgramProofs.Uxnmin.StackView

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JCI consumes its working-stack condition and selects the skip or JMI suffix. -/
theorem immediate_condition (memory : Word → Byte) (pointer : Byte)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (kept : memory 0x2bf#16 = 0#8) (stackPointer : memory 0x655#16 = pointer)
    (workingSpace : working.ptr.toNat ≤ 249) (returnSpace : returning.ptr.toNat ≤ 251) :
    ∃ final, Reaches (machine memory 0x381 working returning) final ∧
      final.pc = (if memory (0x555 + (pointer - 1#8).setWidth 16) = 0#8 then 0x38e else 0x3a4) ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update (Function.update memory 0x40 5) 0x41 0x55)
        0x655 (pointer - 1#8) ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  let selected := Function.update (Function.update memory 0x40 5) 0x41 0x55
  let scratch : Uxn.Stack := { working with data := (Function.update
    (Function.update (Function.update working.data working.ptr 5) (working.ptr + 1#8) 0x55)
    (working.ptr + 2#8) 0x40) }
  have selectedCode : CodeImage selected := (code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  obtain ⟨popped, popRun, popPC, popWorking, popHigh, popLow, popReturning, popMemory, popWF, popRF⟩ :=
    pop_byte_operand selected 0x555 pointer 0 scratch returning 0x38a (.inl rfl) selectedCode
      (by simp [selected]) (by simp [selected]) (by simpa [selected] using kept) (by decide)
      (by simpa [selected] using stackPointer) workingSpace returnSpace
  have condition : selected (0x555 + (pointer - 1#8).setWidth 16) =
      memory (0x555 + (pointer - 1#8).setWidth 16) := by
    simp (disch := bv_omega) [selected, Function.update_of_ne]
  have poppedCode : CodeImage popped.mem.ram := by
    rw [popMemory]
    exact selectedCode.write _ _ (.inr (.inl (by decide)))
  have initial : Reaches (machine memory 0x381 working returning)
      (machine selected 0x2b3 scratch (Stack.pushWord returning 0x38a)) := by
    have code381 : memory 0x381#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code382 : memory 0x382#16 = 0x05#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code383 : memory 0x383#16 = 0x55#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code384 : memory 0x384#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code385 : memory 0x385#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code386 : memory 0x386#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code387 : memory 0x387#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code388 : memory 0x388#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code389 : memory 0x389#16 = 0x29#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    iterate 4
      apply Reaches.next
      · simp [uxn_state, uxn_step, code381, code382, code383, code384, code385, code386, code387, code388, code389]
        rfl
    simpa [scratch, selected, machine, Stack.pushWord, Stack.push, BitVec.add_assoc] using
      Reaches.refl (machine selected 0x2b3 scratch (Stack.pushWord returning 0x38a))
  rw [condition] at popLow
  have valueShape : Stack.pushWord { popped.mem.wstk with ptr := working.ptr }
      (0#8 ++ memory (0x555 + (pointer - 1#8).setWidth 16)) = popped.mem.wstk := by
    simpa [scratch, popWorking, BitVec.sub_eq_add_neg, BitVec.add_assoc, popHigh, popLow]
      using Stack.asPushWord popped.mem.wstk
  have branch (memory : Word → Byte) (working returning : Uxn.Stack) (value : Byte)
      (code : CodeImage memory) (space : working.ptr.toNat ≤ 249) :
      ∃ final, Reaches (machine memory 0x38a (Stack.pushWord working (0#8 ++ value)) returning) final ∧
        final.pc = (if value = 0#8 then 0x38e else 0x3a4) ∧
        final.mem.wstk.ptr = working.ptr ∧ final.mem.ram = memory ∧ final.mem.rstk = returning ∧
        (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) := by
    have code38a : memory 0x38a#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code38b : memory 0x38b#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code38c : memory 0x38c#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code38d : memory 0x38d#16 = 0x16#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have lowValue : (0#8 ++ value).setWidth 8 = value := BitVec.setWidth_append_eq_right
    by_cases zero : value = 0#8
    all_goals
      iterate 2
        apply Reaches.prepend
        · simp [uxn_state, uxn_step, code38a, code38b, code38c, code38d, zero, lowValue]
          rfl
      refine ⟨_, .refl _, ?_, rfl, rfl, rfl, ?_⟩
      · simp [zero]
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]
  obtain ⟨final, after, finalPC, finalWorking, finalMemory, finalReturning, finalFrame⟩ :=
    branch popped.mem.ram { popped.mem.wstk with ptr := working.ptr } popped.mem.rstk
      (memory (0x555 + (pointer - 1#8).setWidth 16)) poppedCode workingSpace
  have afterRun : Reaches popped final := by
    rw [valueShape] at after
    simpa only [← popPC, machine] using after
  refine ⟨final, initial.trans (popRun.trans afterRun), finalPC, finalWorking,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [finalReturning, popReturning]
  · rw [finalMemory, popMemory]
    rfl
  · rw [finalMemory]
    exact poppedCode
  · intro index below
    rw [finalFrame _ below, popWF _ below]
    simp (disch := bv_omega) only [scratch, Function.update_of_ne]
  · intro index below
    rw [finalReturning]
    exact popRF index below

end ProgramProofs.Uxnmin
