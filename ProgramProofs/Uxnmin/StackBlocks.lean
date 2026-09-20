import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Reaches

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem pop_byte (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (ptr : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 250)
    (returnSpace : returning.ptr.toNat ≤ 251) :
    ∃ final, Reaches
      (machine memory 0x2b5 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr + 1#8 ∧
      final.mem.wstk.data working.ptr = memory (softwareStack + (pointer - 1#8).setWidth 16) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update memory
        (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - 1#8) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code2b5 : memory 0x2b5#16 = 0x80#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b6 : memory 0x2b6#16 = 0x40#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b7 : memory 0x2b7#16 = 0x30#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b8 : memory 0x2b8#16 = 0x26#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b9 : memory 0x2b9#16 = 0xa0#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ba : memory 0x2ba#16 = 0x01#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2bb : memory 0x2bb#16 = 0x00#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2bc : memory 0x2bc#16 = 0x38#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2bd : memory 0x2bd#16 = 0xa0#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2be : memory 0x2be#16 = 0x00#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c0 : memory 0x2c0#16 = 0x38#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c1 : memory 0x2c1#16 = 0x2f#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c2 : memory 0x2c2#16 = 0xd4#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c3 : memory 0x2c3#16 = 0x4f#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c4 : memory 0x2c4#16 = 0x80#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c5 : memory 0x2c5#16 = 0x01#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c6 : memory 0x2c6#16 = 0x19#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c7 : memory 0x2c7#16 = 0xef#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c8 : memory 0x2c8#16 = 0x15#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2c9 : memory 0x2c9#16 = 0x80#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ca : memory 0x2ca#16 = 0x00#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2cb : memory 0x2cb#16 = 0x54#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2cc : memory 0x2cc#16 = 0x4f#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2cd : memory 0x2cd#16 = 0x38#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ce : memory 0x2ce#16 = 0x14#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2cf : memory 0x2cf#16 = 0x6c#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have extended (byte : Byte) : (0#8 ++ byte) = byte.setWidth 16 := by
    rw [BitVec.append_def, BitVec.shiftLeftZeroExtend_eq, BitVec.setWidth'_eq]
    simp
  have scratch_order : 0x100#16 + softwareStack = softwareStack + 0x100#16 :=
    BitVec.add_comm _ _
  have keep_order : keep.setWidth 16 + (softwareStack + 0x100#16) =
      softwareStack + (0x100#16 + keep.setWidth 16) := by
    rw [BitVec.add_comm (keep.setWidth 16), BitVec.add_assoc]
  have decremented : (pointer.setWidth 16 + 65535#16).setWidth 8 = pointer + 255#8 := by bv_omega
  have code2ad_separate : 0x2c9#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have code2ae_separate : 0x2ca#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have code2af_separate : 0x2cb#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have code2b0_separate : 0x2cc#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have code2b1_separate : 0x2cd#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have code2b2_separate : 0x2ce#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have code2b3_separate : 0x2cf#16 ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have data_separate : softwareStack + (pointer + 255#8).setWidth 16 ≠
      softwareStack + (0x100#16 + keep.setWidth 16) := by bv_omega
  have data_order : (pointer + 255#8).setWidth 16 + softwareStack =
      softwareStack + (pointer + 255#8).setWidth 16 := BitVec.add_comm _ _
  iterate 20
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code2b5, code2b6, code2b7, code2b8, code2b9, code2ba, code2bb, code2bc, code2bd, code2be,
        code2c0, code2c1, code2c2, code2c3, code2c4, code2c5, code2c6, code2c7, code2c8, code2c9,
        code2ca, code2cb, code2cc, code2cd, code2ce, code2cf,
        code2ad_separate, code2ae_separate, code2af_separate, code2b0_separate, code2b1_separate,
        code2b2_separate, code2b3_separate,
        high, low, kept, ptr, extended, scratch_order, keep_order, decremented,
        data_order, data_separate]
      rfl
  refine ⟨_, .refl _, ?_⟩
  refine ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp [BitVec.sub_eq_add_neg]
  · simp [BitVec.sub_eq_add_neg]
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
