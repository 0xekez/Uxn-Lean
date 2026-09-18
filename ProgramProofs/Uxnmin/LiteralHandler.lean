import ProgramProofs.Uxnmin.Peek
import ProgramProofs.Uxnmin.PcRelativeSet

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Literal handlers read from the current guest PC, push the value, and advance past it. -/
theorem handler_lit (memory : Word → Byte) (softwareStack pc : Word) (pointer : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (pointerValue : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x36d working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update
        (Function.update (storeStackOperand memory softwareStack pointer (peekValue memory pc 0xffff short) short)
          0x45 (((pc + (if short then 2#16 else 1#16)) >>> 8).setWidth 8))
        0x46 ((pc + (if short then 2#16 else 1#16)).setWidth 8) ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have initial : Reaches
      (machine memory 0x36d working (Stack.pushWord returning returnAddress))
      (machine memory 0x2f8 (Stack.pushWord (Stack.pushWord working pc) 0xffff)
        (Stack.pushWord (Stack.pushWord returning returnAddress) 0x376)) := by
    have code36d : memory 0x36d#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code36e : memory 0x36e#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code36f : memory 0x36f#16 = 0x30#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code370 : memory 0x370#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code371 : memory 0x371#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code372 : memory 0x372#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code373 : memory 0x373#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code374 : memory 0x374#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code375 : memory 0x375#16 = 0x82#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    iterate 4
      apply Reaches.next
      · simp [uxn_state, uxn_step, pcHigh, pcLow, append_split,
          code36d, code36e, code36f, code370, code371, code372, code373, code374, code375]
        rfl
    simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.reduceSetWidth]
    exact .refl _
  have offset (memory : Word → Byte) (working returning : Uxn.Stack)
      (code : CodeImage memory) (mode : memory 0x44#16 = if short then 1 else 0) :
      Reaches (machine memory 0x379 working returning)
        (machine memory 0x284 (Stack.pushWord working (if short then 2#16 else 1#16)) returning) := by
    have code379 : memory 0x379#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code37a : memory 0x37a#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code37b : memory 0x37b#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code37c : memory 0x37c#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code37d : memory 0x37d#16 = 0x01#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code37e : memory 0x37e#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code37f : memory 0x37f#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code380 : memory 0x380#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    cases short <;> (
      iterate 4
        apply Reaches.next
        · simp [uxn_state, uxn_step, mode,
            code379, code37a, code37b, code37c, code37d, code37e, code37f, code380]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.reduceSetWidth, Bool.false_eq_true, if_false, if_true]
      exact .refl _)
  obtain ⟨read, readSteps, readPC, readMemory, readPointer, readShape, readReturnPointer,
    readFrame, readReturnFrame⟩ :=
    peek_operand memory pc 0xffff 0x376 short working (Stack.pushWord returning returnAddress)
      code mode (by omega) (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  simp only [BitVec.ofNat_eq_ofNat] at readShape
  obtain ⟨pushed, pushSteps, pushPC, pushWP, pushRP, pushMemory, pushFrame, pushReturnFrame⟩ :=
    push_operand memory softwareStack pointer (peekValue memory pc 0xffff short) short
      { read.mem.wstk with ptr := working.ptr } read.mem.rstk 0x379
      selected code high low mode pointerValue workingSpace
      (by rw [readReturnPointer]; simp only [Stack.pushWord, Stack.push]; bv_omega)
  have readEta : read = machine memory 0x376 read.mem.wstk read.mem.rstk := by
    cases read with
    | mk pc memory =>
      cases memory
      simp only [machine] at readPC readMemory ⊢
      rw [readPC, readMemory]
  have pushRun : Reaches read pushed := by
    have code376 : memory 0x376#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code377 : memory 0x377#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code378 : memory 0x378#16 = 0x13#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    rw [readEta]
    apply Reaches.next (jsi_call memory 0x376 0x28c _ _ code376 (by simp [code377, code378]))
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, readShape] using pushSteps
  have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
  have separate (location : Word) (bound : location.toNat < 0x555) :
      pushed.mem.ram location = memory location := by
    rw [pushMemory]
    have data (index : Byte) : location ≠ softwareStack + index.setWidth 16 := by bv_omega
    have pointer : location ≠ softwareStack + 0x100#16 := by bv_omega
    split <;> simp only [Function.update_of_ne pointer, Function.update_of_ne (data _)]
  have pushedCode : CodeImage pushed.mem.ram := by
    intro location lower upper immutable
    rw [separate location upper]
    exact code location lower upper immutable
  have returningPointer : pushed.mem.rstk.ptr = returning.ptr + 2#8 := by
    rw [pushRP, readReturnPointer]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have returningFrame (index : Byte) (bound : index.toNat < (Stack.pushWord returning returnAddress).ptr.toNat) :
      pushed.mem.rstk.data index = (Stack.pushWord returning returnAddress).data index := by
    rw [pushReturnFrame _ (readReturnPointer ▸ bound), readReturnFrame _ bound]
  have returnHigh : pushed.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [returningFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : pushed.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [returningFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningShape : Stack.pushWord { pushed.mem.rstk with ptr := returning.ptr }
      returnAddress = pushed.mem.rstk := by
    simpa [returningPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, returnHigh, returnLow, append_split]
      using Stack.asPushWord pushed.mem.rstk
  obtain ⟨final, advanceSteps, finalPC, finalWP, finalRP, finalMemory, finalCode, finalFrame, finalReturnFrame⟩ :=
    pc_set_relative pushed.mem.ram pc (if short then 2#16 else 1#16) returnAddress
      pushed.mem.wstk { pushed.mem.rstk with ptr := returning.ptr } pushedCode
      ((separate _ (by decide)).trans pcHigh) ((separate _ (by decide)).trans pcLow)
      (by rw [pushWP]; dsimp; omega) (by dsimp; omega)
  have pushedEta : pushed = machine pushed.mem.ram 0x379 pushed.mem.wstk pushed.mem.rstk := by
    cases pushed
    simpa [machine] using pushPC
  have advanceRun : Reaches pushed final := by
    rw [pushedEta]
    apply (offset pushed.mem.ram pushed.mem.wstk pushed.mem.rstk pushedCode
      ((separate _ (by decide)).trans mode)).trans
    simpa only [returningShape] using advanceSteps
  refine ⟨final, initial.trans (readSteps.trans (pushRun.trans advanceRun)), finalPC,
    finalWP.trans pushWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMemory, pushMemory]
    cases short <;> rfl
  · intro index bound
    rw [finalFrame _ (pushWP ▸ bound), pushFrame _ bound, readFrame _ bound]
  · intro index bound
    rw [finalReturnFrame _ bound, returningFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
