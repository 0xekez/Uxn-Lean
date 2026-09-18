import ProgramProofs.Uxnmin.MemoryBlocks
import ProgramProofs.Uxnmin.OperandPair

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def peekValue (memory : Word → Byte) (address mask : Word) (short : Bool) : Word :=
  if short then memory (relocate address) ++ memory (relocate ((address + 1) &&& mask))
  else 0#8 ++ memory (relocate address)

/-- The common memory reader preserves the native frames below its operands. -/
theorem peek_operand (memory : Word → Byte) (address mask returnAddress : Word)
    (short : Bool) (working returning : Uxn.Stack) (code : CodeImage memory)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (workingSpace : working.ptr.toNat ≤ 249) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x2f8 (Stack.pushWord (Stack.pushWord working address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (peekValue memory address mask short) = final.mem.wstk ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat →
        final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat →
        final.mem.rstk.data index = returning.data index) := by
  have workingOffset (index : Byte) (below : index.toNat < working.ptr.toNat) :
      5 ≤ (index - working.ptr).toNat := by bv_omega
  have returnOffset (index : Byte) (below : index.toNat < returning.ptr.toNat) :
      6 ≤ (index - returning.ptr).toNat := by bv_omega
  have offset_eq (first second : Byte) : first + (second - first) = second := by bv_omega
  cases short with
  | false =>
    obtain ⟨final, steps, pc, ram, pointer, high, low, returningPointer, returningData, frame⟩ :=
      peek_byte memory address mask returnAddress working returning code mode
    simp only [BitVec.ofNat_eq_ofNat] at high low pointer
    refine ⟨final, steps, pc, ram, pointer, ?_, returningPointer, ?_, ?_⟩
    · simpa [pointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, high, low, peekValue]
        using Stack.asPushWord final.mem.wstk
    · intro index below
      simpa only [offset_eq] using frame (index - working.ptr) (workingOffset index below)
    · intro index below
      rw [returningData]
      simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  | true =>
    let scratch : Uxn.Stack :=
      { data := Function.update (Stack.pushWord (Stack.pushWord working address) mask).data
          (working.ptr + 4#8) 1#8, ptr := working.ptr + 4#8 }
    have scratchPointer : scratch.ptr = working.ptr + 4#8 := rfl
    have scratchFirst : scratch.data working.ptr ++ scratch.data (working.ptr + 1#8) = address := by
      simp [scratch, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
    have scratchSecond : scratch.data (working.ptr + 2#8) ++ scratch.data (working.ptr + 3#8) = mask := by
      simp [scratch, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
    have scratchPair : Stack.pushWord (Stack.pushWord { scratch with ptr := working.ptr }
        address) mask = scratch := by
      simpa [scratchPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        scratchFirst, scratchSecond] using Stack.asPushPair scratch
    have initial : Reaches
        (machine memory 0x2f8 (Stack.pushWord (Stack.pushWord working address) mask)
          (Stack.pushWord returning returnAddress))
        (machine memory 0x308 scratch (Stack.pushWord returning returnAddress)) := by
      have code2f8 : memory 0x2f8#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2f9 : memory 0x2f9#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2fa : memory 0x2fa#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2fb : memory 0x2fb#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2fc : memory 0x2fc#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2fd : memory 0x2fd#16 = 0x0a#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 3
        apply Reaches.next
        · simp [uxn_state, uxn_step, code2f8, code2f9, code2fa, code2fb, code2fc, code2fd, mode]
          rfl
      simpa [machine, scratch, Stack.pushWord, Stack.push, BitVec.add_assoc] using
        (Reaches.refl (machine memory 0x308 scratch (Stack.pushWord returning returnAddress)))
    obtain ⟨final, steps, pc, ram, pointer, high, low, returningPointer, frame, returnFrame⟩ :=
      peek_short memory address mask returnAddress { scratch with ptr := working.ptr } returning code
    rw [scratchPair] at steps
    simp only [BitVec.ofNat_eq_ofNat] at high low pointer
    refine ⟨final, initial.trans steps, pc, ram, pointer, ?_, returningPointer, ?_, ?_⟩
    · simpa [pointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, high, low, peekValue]
        using Stack.asPushWord final.mem.wstk
    · intro index below
      have preserved := frame (index - working.ptr) (workingOffset index below)
      simp only [offset_eq] at preserved
      rw [preserved]
      simp (disch := bv_omega) only [scratch, Stack.pushWord, Stack.push, Function.update_of_ne]
    · intro index below
      simpa only [offset_eq] using returnFrame (index - returning.ptr) (returnOffset index below)

end ProgramProofs.Uxnmin
