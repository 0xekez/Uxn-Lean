import ProgramProofs.Uxnmin.Immediate
import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Execution

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def ImmediateKind.entry : ImmediateKind → Word
  | .jci => 0x381 | .jmi => 0x3a4 | .jsi => 0x396 | .lit _ _ => 0x36d

/-- The immediate dispatcher preserves the opcode and both native frames. -/
theorem immediate_dispatch (kind : ImmediateKind) (memory : Word → Byte)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (workingSpace : working.ptr.toNat ≤ 253) :
    ∃ final, Reaches (machine memory 0x353 (Stack.push working kind.opcode) returning) final ∧
      final.pc = kind.entry ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 1 ∧
      final.mem.wstk.data working.ptr = kind.opcode ∧
      final.mem.rstk = returning ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) := by
  have code353 : memory 0x353#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code354 : memory 0x354#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code355 : memory 0x355#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code356 : memory 0x356#16 = 0x01#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code357 : memory 0x357#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code358 : memory 0x358#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code359 : memory 0x359#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code35a : memory 0x35a#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code35b : memory 0x35b#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code35c : memory 0x35c#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code35d : memory 0x35d#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code35e : memory 0x35e#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code35f : memory 0x35f#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code360 : memory 0x360#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code361 : memory 0x361#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code362 : memory 0x362#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code363 : memory 0x363#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code364 : memory 0x364#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code365 : memory 0x365#16 = 0x3e#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code366 : memory 0x366#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code367 : memory 0x367#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code368 : memory 0x368#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code369 : memory 0x369#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code36a : memory 0x36a#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code36b : memory 0x36b#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code36c : memory 0x36c#16 = 0x29#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  cases kind with
  | jci =>
    iterate 6
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, ImmediateKind.opcode,
          code353, code354, code355, code356, code357, code358, code359, code35a, code35b, code35c, code35d, code35e, code35f, code360, code361, code362, code363, code364, code365, code366, code367, code368, code369, code36a, code36b, code36c]
        rfl
    refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp [BitVec.add_assoc]
    · simp [ImmediateKind.opcode]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  | jmi =>
    iterate 10
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, ImmediateKind.opcode,
          code353, code354, code355, code356, code357, code358, code359, code35a, code35b, code35c, code35d, code35e, code35f, code360, code361, code362, code363, code364, code365, code366, code367, code368, code369, code36a, code36b, code36c]
        rfl
    refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp [BitVec.add_assoc]
    · simp [ImmediateKind.opcode]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  | jsi =>
    iterate 14
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, ImmediateKind.opcode,
          code353, code354, code355, code356, code357, code358, code359, code35a, code35b, code35c, code35d, code35e, code35f, code360, code361, code362, code363, code364, code365, code366, code367, code368, code369, code36a, code36b, code36c]
        rfl
    refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp [BitVec.add_assoc]
    · simp [ImmediateKind.opcode]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  | lit short ret =>
    cases short <;> cases ret
    all_goals
      iterate 14
        apply Reaches.prepend
        · simp [uxn_state, uxn_step, ImmediateKind.opcode,
            code353, code354, code355, code356, code357, code358, code359, code35a, code35b, code35c, code35d, code35e, code35f, code360, code361, code362, code363, code364, code365, code366, code367, code368, code369, code36a, code36b, code36c]
          rfl
      refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, ?_⟩
      · simp [BitVec.add_assoc]
      · simp [ImmediateKind.opcode]
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
