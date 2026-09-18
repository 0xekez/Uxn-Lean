import ProgramProofs.Uxnmin.PeekWord
import ProgramProofs.Uxnmin.Pc
import ProgramProofs.Uxnmin.OperandPair
import ProgramProofs.Host.StackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JMI's common suffix reads a word displacement and updates the guest PC. -/
theorem handler_jmi (memory : Word → Byte) (pc returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x3a4 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update memory
        0x45 (((pc + (memory (relocate pc) ++ memory (relocate (pc + 1))) + 2) >>> 8).setWidth 8))
        0x46 ((pc + (memory (relocate pc) ++ memory (relocate (pc + 1))) + 2).setWidth 8) ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have code3a4 : memory 0x3a4#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3a5 : memory 0x3a5#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3a6 : memory 0x3a6#16 = 0x30#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3a7 : memory 0x3a7#16 = 0x26#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3a8 : memory 0x3a8#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3a9 : memory 0x3a9#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3aa : memory 0x3aa#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ab : memory 0x3ab#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ac : memory 0x3ac#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ad : memory 0x3ad#16 = 0x5a#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3ae : memory 0x3ae#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3af : memory 0x3af#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b0 : memory 0x3b0#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b1 : memory 0x3b1#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b2 : memory 0x3b2#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code3b3 : memory 0x3b3#16 = 0xd4#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have repush (stack : Uxn.Stack) (value : Word) :
      Stack.pushWord { Stack.pushWord stack value with ptr := stack.ptr } value = Stack.pushWord stack value := by
    simp only [Stack.pushWord, Stack.push]
    congr 1
    funext index
    by_cases first : index = stack.ptr <;> by_cases second : index = stack.ptr + 1#8 <;> simp [first, second]
  have initial : Reaches (machine memory 0x3a4 working (Stack.pushWord returning returnAddress))
      (machine memory 0x308 (Stack.pushWord (Stack.pushWord (Stack.pushWord working pc) pc) 0xffff)
        (Stack.pushWord (Stack.pushWord returning returnAddress) 0x3ae)) := by
    iterate 5
      apply Reaches.next
      · simp [uxn_state, uxn_step, code3a4, code3a5, code3a6, code3a7, code3a8,
          code3a9, code3aa, code3ab, code3ac, code3ad, pcHigh, pcLow]
        rfl
    convert Reaches.refl (machine memory 0x308
      (Stack.pushWord (Stack.pushWord (Stack.pushWord working pc) pc) 0xffff)
      (Stack.pushWord (Stack.pushWord returning returnAddress) 0x3ae)) using 1
    simp only [machine, Stack.pushWord, Stack.push, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
    congr 3
    funext index
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | exfalso; bv_omega
  obtain ⟨peeked, read, peekPC, peekMemory, peekWorking, peekShape, peekReturning, peekWF, peekRF⟩ :=
    peek_word memory pc 0xffff 0x3ae (Stack.pushWord working pc) (Stack.pushWord returning returnAddress)
      code (by simp only [Stack.pushWord, Stack.push]; bv_omega)
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have workingPtr : (Stack.pushWord working pc).ptr = working.ptr + 2#8 := by
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have returnPtr : (Stack.pushWord returning returnAddress).ptr = returning.ptr + 2#8 := by
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  rw [workingPtr] at peekWorking peekShape peekWF
  have savedPC : Stack.pushWord { peeked.mem.wstk with ptr := working.ptr } pc =
      { peeked.mem.wstk with ptr := working.ptr + 2#8 } := by
    exact Stack.asPushWord_of_frame (Stack.pushWord working pc)
      { peeked.mem.wstk with ptr := working.ptr + 2#8 } working.ptr pc (repush _ _) (by omega)
      workingPtr.symm (by simpa only [workingPtr] using peekWF)
  have pairShape : Stack.pushWord (Stack.pushWord { peeked.mem.wstk with ptr := working.ptr } pc)
      (memory (relocate pc) ++ memory (relocate (pc + 1))) = peeked.mem.wstk := by
    rw [savedPC]
    have mask (value : Word) : value &&& 0xffff#16 = value := BitVec.and_allOnes
    simpa only [BitVec.ofNat_eq_ofNat, mask] using peekShape
  have returnShape := Stack.asPushWord_of_frame (Stack.pushWord returning returnAddress)
    peeked.mem.rstk returning.ptr returnAddress (repush _ _) (by omega) peekReturning peekRF
  have adding (working returning : Uxn.Stack) (displacement : Word)
      (space : working.ptr.toNat ≤ 251) :
      ∃ added, Reaches (machine memory 0x3ae (Stack.pushWord (Stack.pushWord working pc) displacement) returning) added ∧
        added.pc = 0x288 ∧ added.mem.ram = memory ∧ added.mem.wstk.ptr = working.ptr + 2 ∧
        Stack.pushWord { added.mem.wstk with ptr := working.ptr } (pc + displacement + 2) = added.mem.wstk ∧
        added.mem.rstk = returning ∧
        (∀ index : Byte, index.toNat < working.ptr.toNat → added.mem.wstk.data index = working.data index) := by
    have addition : pc + (displacement + 2#16) = displacement + (2#16 + pc) := by
      exact (BitVec.add_comm pc (displacement + 2#16)).trans (BitVec.add_assoc displacement 2#16 pc)
    iterate 4
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, code3ae, code3af, code3b0, code3b1, code3b2, code3b3]
        rfl
    refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp [BitVec.add_assoc]
    · apply congrArg₂ Uxn.Stack.mk
      · funext index
        by_cases first : index = working.ptr <;> by_cases second : index = working.ptr + 1#8 <;>
          simp [Stack.pushWord, Stack.push, BitVec.add_assoc, first, second, addition]
      · simp [Stack.push, BitVec.add_assoc]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  obtain ⟨added, addRun, addedPC, addedMemory, addedWorking, addedShape, addedReturning, addedFrame⟩ :=
    adding { peeked.mem.wstk with ptr := working.ptr } peeked.mem.rstk
      (memory (relocate pc) ++ memory (relocate (pc + 1))) (by change working.ptr.toNat ≤ 251; omega)
  have peekRun : Reaches peeked added := by
    rw [pairShape] at addRun
    simpa only [← peekMemory, ← peekPC, machine] using addRun
  obtain ⟨final, finish, finalPC, finalMemory, finalWorking, finalReturning, finalWF, finalRF⟩ :=
    pc_set_absolute memory (pc + (memory (relocate pc) ++ memory (relocate (pc + 1))) + 2)
      returnAddress { added.mem.wstk with ptr := working.ptr }
      { added.mem.rstk with ptr := returning.ptr } code (by dsimp; omega) (by dsimp; omega)
  have finalRun : Reaches added final := by
    have returned : Stack.pushWord { added.mem.rstk with ptr := returning.ptr } returnAddress = added.mem.rstk := by
      rw [addedReturning]
      exact returnShape
    rw [addedShape, returned] at finish
    simpa only [← addedMemory, ← addedPC, machine] using finish
  refine ⟨final, initial.trans (read.trans (peekRun.trans finalRun)), finalPC,
    finalWorking, finalReturning, finalMemory, ?_, ?_, ?_⟩
  · rw [finalMemory]
    exact (code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  · intro index below
    rw [finalWF _ below, addedFrame _ below, peekWF _ (by bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  · intro index below
    rw [finalRF _ below, addedReturning, peekRF _ (by rw [returnPtr]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
