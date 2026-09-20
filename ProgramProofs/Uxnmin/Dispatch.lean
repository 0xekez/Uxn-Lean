import ProgramProofs.Host.Reaches
import ProgramProofs.Uxnmin.Code
import ProgramProofs.Uxnmin.Embedding

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem fetch (memory : Word → Byte) (pc : Word) (working returning : Uxn.Stack)
    (code : CodeImage memory) (empty : working.ptr = 0)
    (high : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (low : memory 0x46#16 = pc.setWidth 8)
    (confined : pc.toNat < ramSize) :
    ∃ final, Reaches (machine memory 0x222 working returning) final ∧
      final.pc = 0x22e ∧ final.mem.wstk.ptr = 1 ∧
      final.mem.wstk.data 0 = memory (relocate pc) ∧
      final.mem.rstk = returning ∧
      final.mem.ram = Function.update
        (Function.update memory 0x45 (((pc + 1) >>> 8).setWidth 8))
        0x46 ((pc + 1).setWidth 8) := by
  have code222 : memory 0x222#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code223 : memory 0x223#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code224 : memory 0x224#16 = 0x30#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code225 : memory 0x225#16 = 0xa1#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code226 : memory 0x226#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code227 : memory 0x227#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code228 : memory 0x228#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code229 : memory 0x229#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code22a : memory 0x22a#16 = 0x8#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code22b : memory 0x22b#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code22c : memory 0x22c#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code22d : memory 0x22d#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have separate : 2137#16 + pc ≠ 69#16 ∧ 2137#16 + pc ≠ 70#16 := by
    dsimp [ramSize, ramBase] at confined
    constructor <;> bv_omega
  iterate 8
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, empty, high, low, code222, code223, code224, code225,
        code226, code227, code228, code229, code22a, code22b, code22c, code22d,
        separate.1, separate.2]
      rfl
  refine ⟨_, .refl _, rfl, rfl, ?_, rfl, ?_⟩
  · rfl
  · rfl

end ProgramProofs.Uxnmin
