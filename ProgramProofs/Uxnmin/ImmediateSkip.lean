import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Execution

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- A false JCI skips its immediate word without reading either operand byte. -/
theorem immediate_skip (memory : Word → Byte) (pc returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (high : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (low : memory 0x46#16 = pc.setWidth 8)
    (workingSpace : working.ptr.toNat ≤ 252) (returnSpace : returning.ptr.toNat ≤ 254) :
    ∃ final, Reaches (machine memory 0x38e working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update memory 0x45 (((pc + 2#16) >>> 8).setWidth 8))
        0x46 ((pc + 2#16).setWidth 8) ∧ CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have code38e : memory 0x38e#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code38f : memory 0x38f#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code390 : memory 0x390#16 = 0xb0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code391 : memory 0x391#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code392 : memory 0x392#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code393 : memory 0x393#16 = 0x05#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code394 : memory 0x394#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code395 : memory 0x395#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 7
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, code38e, code38f, code390, code391, code392, code393, code394, code395,
        high, low, append_split, BitVec.add_assoc]
      rfl
  refine ⟨_, .refl _, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact (code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  · intro index below
    simp (disch := bv_omega) only [Function.update_of_ne]
  · intro index below
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
