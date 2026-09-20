import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Reaches

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem pc_relative (memory : Word → Byte) (pc returnAddress : Word) (offset : Byte)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (high : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (low : memory 0x46#16 = pc.setWidth 8)
    (workingSpace : working.ptr.toNat ≤ 252)
    (returnSpace : returning.ptr.toNat ≤ 254) :
    ∃ final, Reaches
      (machine memory 0x271 (Stack.push working offset)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      final.mem.wstk.data working.ptr ++ final.mem.wstk.data (working.ptr + 1) =
        pc + offset.signExtend 16 ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code271 : memory 0x271#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code272 : memory 0x272#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code273 : memory 0x273#16 = 0x7f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code274 : memory 0x274#16 = 0x0a#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code275 : memory 0x275#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code276 : memory 0x276#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code277 : memory 0x277#16 = 0x1a#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code278 : memory 0x278#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code279 : memory 0x279#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code27a : memory 0x27a#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code27b : memory 0x27b#16 = 0x30#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code27c : memory 0x27c#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code27d : memory 0x27d#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 10
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code271, code272, code273, code274, code275, code276, code277, code278,
        code279, code27a, code27b, code27c, code27d, high, low]
      rfl
  refine ⟨_, .refl _, ?_⟩
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp [high, low, append_split]
    by_cases positive : offset.toNat < 128
    · have comparison : ¬ 127#16 < offset.setWidth 16 := by bv_omega
      have msb : offset.msb = false := by
        rw [BitVec.msb_eq_decide]
        simpa using positive
      simp only [if_neg comparison]
      change 0#8 ++ offset = offset.signExtend 16
      rw [BitVec.signExtend_eq_setWidth_of_msb_false msb,
        BitVec.append_def, BitVec.shiftLeftZeroExtend_eq, BitVec.setWidth'_eq]
      simp
    · have comparison : 127#16 < offset.setWidth 16 := by bv_omega
      have msb : offset.msb = true := by
        rw [BitVec.msb_eq_decide]
        simpa using (show 128 ≤ offset.toNat by omega)
      simp only [if_pos comparison]
      change 255#8 ++ offset = offset.signExtend 16
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_append, BitVec.toNat_signExtend, msb]
      rw [← Nat.shiftLeft_add_eq_or_of_lt (show offset.toNat < 2^8 from offset.isLt)]
      simp [Nat.shiftLeft_eq]
      omega
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]

theorem pc_set_absolute (memory : Word → Byte) (pc returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (workingSpace : working.ptr.toNat ≤ 253)
    (returnSpace : returning.ptr.toNat ≤ 254) :
    ∃ final, Reaches
      (machine memory 0x288 (Stack.pushWord working pc)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧
      final.mem.ram = Function.update
        (Function.update memory 0x45 ((pc >>> 8).setWidth 8)) 0x46 (pc.setWidth 8) ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code288 : memory 0x288#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code289 : memory 0x289#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code28a : memory 0x28a#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code28b : memory 0x28b#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 3
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code288, code289, code28a, code28b]
      rfl
  refine ⟨_, .refl _, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin

