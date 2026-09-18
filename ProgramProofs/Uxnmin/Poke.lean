import ProgramProofs.Uxnmin.MemoryBlocks
import ProgramProofs.Uxnmin.OperandPair

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def pokeMemory (memory : Word → Byte) (address mask value : Word) (short : Bool) : Word → Byte :=
  if short then
    Function.update (Function.update memory (relocate address) ((value >>> 8).setWidth 8))
      (relocate ((address + 1) &&& mask)) (value.setWidth 8)
  else Function.update memory (relocate address) (value.setWidth 8)

/-- The memory writer preserves both active native stack frames. -/
theorem poke_operand (memory : Word → Byte) (address mask value returnAddress : Word)
    (short : Bool) (working returning : Uxn.Stack) (code : CodeImage memory)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (firstBound : address.toNat < ramSize)
    (secondBound : short = true → ((address + 1#16) &&& mask).toNat < ramSize)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x2d8 (Stack.pushWord (Stack.pushWord (Stack.pushWord working value) address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = pokeMemory memory address mask value short ∧
      CodeImage final.mem.ram ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat →
        final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat →
        final.mem.rstk.data index = returning.data index) := by
  have workingOffset (index : Byte) (below : index.toNat < working.ptr.toNat) :
      7 ≤ (index - working.ptr).toNat := by bv_omega
  have returnOffset (index : Byte) (below : index.toNat < returning.ptr.toNat) :
      6 ≤ (index - returning.ptr).toNat := by bv_omega
  have offset_eq (first second : Byte) : first + (second - first) = second := by bv_omega
  have after (location : Word) (bound : location.toNat < ramSize) : 0x555 ≤ (relocate location).toNat := by
    dsimp [relocate, ramSize] at *
    bv_omega
  cases short with
  | false =>
    obtain ⟨final, steps, pc, ram, pointer, returningPointer, returningData, frame⟩ :=
      poke_byte memory address mask value returnAddress working returning code mode firstBound
    refine ⟨final, steps, pc, ram, ?_, pointer, returningPointer, ?_, ?_⟩
    · rw [ram]
      exact code.write _ _ (.inr (.inl (after address firstBound)))
    · intro index below
      simpa only [offset_eq] using frame (index - working.ptr) (workingOffset index below)
    · intro index below
      rw [returningData]
      simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  | true =>
    let scratch : Uxn.Stack :=
      { data := Function.update (Stack.pushWord (Stack.pushWord (Stack.pushWord working value) address) mask).data
          (working.ptr + 6#8) 1#8, ptr := working.ptr + 6#8 }
    have triple (stack : Uxn.Stack) :
        Stack.pushWord (Stack.pushWord (Stack.pushWord { stack with ptr := stack.ptr - 6#8 }
          (stack.data (stack.ptr - 6#8) ++ stack.data (stack.ptr - 5#8)))
          (stack.data (stack.ptr - 4#8) ++ stack.data (stack.ptr - 3#8)))
          (stack.data (stack.ptr - 2#8) ++ stack.data (stack.ptr - 1#8)) = stack := by
      have lower := Stack.asPushPair { stack with ptr := stack.ptr - 2#8 }
      simp [BitVec.sub_eq_add_neg, BitVec.add_assoc] at lower ⊢
      rw [lower]
      simpa [BitVec.sub_eq_add_neg] using Stack.asPushWord stack
    have scratchPointer : scratch.ptr = working.ptr + 6#8 := rfl
    have scratchFirst : scratch.data working.ptr ++ scratch.data (working.ptr + 1#8) = value := by
      simp [scratch, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
    have scratchSecond : scratch.data (working.ptr + 2#8) ++ scratch.data (working.ptr + 3#8) = address := by
      simp [scratch, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
    have scratchThird : scratch.data (working.ptr + 4#8) ++ scratch.data (working.ptr + 5#8) = mask := by
      simp [scratch, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
    have scratchShape : Stack.pushWord (Stack.pushWord (Stack.pushWord { scratch with ptr := working.ptr }
        value) address) mask = scratch := by
      simpa [scratchPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        scratchFirst, scratchSecond, scratchThird] using triple scratch
    have initial : Reaches
        (machine memory 0x2d8 (Stack.pushWord (Stack.pushWord (Stack.pushWord working value) address) mask)
          (Stack.pushWord returning returnAddress))
        (machine memory 0x2e6 scratch (Stack.pushWord returning returnAddress)) := by
      have code2d8 : memory 0x2d8#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2d9 : memory 0x2d9#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2da : memory 0x2da#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2db : memory 0x2db#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2dc : memory 0x2dc#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code2dd : memory 0x2dd#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 3
        apply Reaches.next
        · simp [uxn_state, uxn_step, code2d8, code2d9, code2da, code2db, code2dc, code2dd, mode]
          rfl
      simpa [machine, scratch, Stack.pushWord, Stack.push, BitVec.add_assoc] using
        (Reaches.refl (machine memory 0x2e6 scratch (Stack.pushWord returning returnAddress)))
    obtain ⟨final, steps, pc, ram, pointer, returningPointer, frame, returnFrame⟩ :=
      poke_short memory address mask value returnAddress { scratch with ptr := working.ptr } returning code
        firstBound (secondBound rfl)
    rw [scratchShape] at steps
    refine ⟨final, initial.trans steps, pc, ram, ?_, pointer, returningPointer, ?_, ?_⟩
    · rw [ram]
      exact (code.write _ _ (.inr (.inl (after address firstBound)))).write _ _
        (.inr (.inl (after _ (secondBound rfl))))
    · intro index below
      have preserved := frame (index - working.ptr) (by have := workingOffset index below; omega)
      simp only [offset_eq] at preserved
      rw [preserved]
      simp (disch := bv_omega) only [scratch, Stack.pushWord, Stack.push, Function.update_of_ne]
    · intro index below
      simpa only [offset_eq] using returnFrame (index - returning.ptr) (returnOffset index below)

end ProgramProofs.Uxnmin
