import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Execution

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JSR and STH both select the other guest stack using this four-instruction block. -/
theorem select_destination (memory : Word → Byte) (entry destination : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (location : entry = 0x446 ∨ entry = 0x455)
    (high : memory 0x42#16 = (destination >>> 8).setWidth 8)
    (low : memory 0x43#16 = destination.setWidth 8)
    (space : working.ptr.toNat ≤ 252) :
    ∃ final, Reaches (machine memory entry working returning) final ∧
      final.pc = entry + 6#16 ∧
      final.mem.ram = Function.update (Function.update memory 0x40 ((destination >>> 8).setWidth 8))
        0x41 (destination.setWidth 8) ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk = returning ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) := by
  have byte0 : memory entry = 0x80#8 := by
    rcases location with rfl | rfl <;> exact code _ (by decide) (by decide) (by simp [MutableCode])
  have byte1 : memory (entry + 1#16) = 0x42#8 := by
    rcases location with rfl | rfl <;> exact code _ (by decide) (by decide) (by simp [MutableCode])
  have byte2 : memory (entry + 2#16) = 0x30#8 := by
    rcases location with rfl | rfl <;> exact code _ (by decide) (by decide) (by simp [MutableCode])
  have byte3 : memory (entry + 3#16) = 0x80#8 := by
    rcases location with rfl | rfl <;> exact code _ (by decide) (by decide) (by simp [MutableCode])
  have byte4 : memory (entry + 4#16) = 0x40#8 := by
    rcases location with rfl | rfl <;> exact code _ (by decide) (by decide) (by simp [MutableCode])
  have byte5 : memory (entry + 5#16) = 0x31#8 := by
    rcases location with rfl | rfl <;> exact code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 4
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, byte0, byte1, byte2, byte3, byte4, byte5, high, low]
      rfl
  refine ⟨_, .refl _, rfl, rfl, rfl, rfl, ?_⟩
  intro index smaller
  simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
