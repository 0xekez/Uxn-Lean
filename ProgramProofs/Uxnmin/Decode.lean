import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Substs
import ProgramProofs.Host.Execution
import ProgramProofs.Uxnmin.Code
import ProgramProofs.Uxnmin.Embedding

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host


theorem decode_modes (memory : Word → Byte) (opcode : Byte) (working returning : Uxn.Stack)
    (code : CodeImage memory) (pointer : working.ptr = 1#8)
    (top : working.data 0#8 = opcode) (_returnSpace : returning.ptr.toNat ≤ 250) :
    ∃ final, Reaches (machine memory 0x22e working returning) final ∧
      final.mem.wstk.ptr = 1 ∧ final.mem.wstk.data 0 = opcode ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram 0x44 = (if 0#16 = 32#16 &&& opcode.setWidth 16 then 0 else 1) ∧
      final.mem.ram 0x2bf = (if 0#16 = 128#16 &&& opcode.setWidth 16 then 0 else 1) ∧
      final.pc = memory (0x515#16 + (opcode &&& 0x1f).setWidth 16 * 2) ++
        memory (0x516#16 + (opcode &&& 0x1f).setWidth 16 * 2) ∧
      final.mem.ram 0x40 ++ final.mem.ram 0x41 =
        (if 64#16 &&& opcode.setWidth 16 = 0 then 0x555#16 else 0x657#16) ∧
      final.mem.ram 0x42 ++ final.mem.ram 0x43 =
        (if 64#16 &&& opcode.setWidth 16 = 0 then 0x657#16 else 0x555#16) ∧
      CodeImage final.mem.ram ∧
      final.mem.ram (if 64#16 &&& opcode.setWidth 16 = 0 then 0x656 else 0x758) =
        memory (if 64#16 &&& opcode.setWidth 16 = 0 then 0x655 else 0x757) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) ∧
      ∀ address, address ∉ [0x40#16, 0x41#16, 0x42#16, 0x43#16, 0x44#16,
        0x2bf#16, 0x656#16, 0x758#16] → final.mem.ram address = memory address := by
  have code22e : memory 0x22e#16 = 0x6#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code22f : memory 0x22f#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code230 : memory 0x230#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code231 : memory 0x231#16 = 0x1c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code232 : memory 0x232#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code233 : memory 0x233#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code234 : memory 0x234#16 = 0x9#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code235 : memory 0x235#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code236 : memory 0x236#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code237 : memory 0x237#16 = 0x11#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code238 : memory 0x238#16 = 0x6#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code239 : memory 0x239#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code23a : memory 0x23a#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code23b : memory 0x23b#16 = 0x1c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code23c : memory 0x23c#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code23d : memory 0x23d#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code23e : memory 0x23e#16 = 0x9#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code23f : memory 0x23f#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code240 : memory 0x240#16 = 0x2#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code241 : memory 0x241#16 = 0xbf#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code242 : memory 0x242#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code243 : memory 0x243#16 = 0x6#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code244 : memory 0x244#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code245 : memory 0x245#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code246 : memory 0x246#16 = 0x1c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code247 : memory 0x247#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code248 : memory 0x248#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code249 : memory 0x249#16 = 0x9#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code24a : memory 0x24a#16 = 0xf#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code24b : memory 0x24b#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code24c : memory 0x24c#16 = 0x6#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code24d : memory 0x24d#16 = 0x57#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code24e : memory 0x24e#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code24f : memory 0x24f#16 = 0x5#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code250 : memory 0x250#16 = 0x55#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code251 : memory 0x251#16 = 0x4f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code252 : memory 0x252#16 = 0xc#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code253 : memory 0x253#16 = 0x24#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code254 : memory 0x254#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code255 : memory 0x255#16 = 0x42#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code256 : memory 0x256#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code257 : memory 0x257#16 = 0x26#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code258 : memory 0x258#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code259 : memory 0x259#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code25a : memory 0x25a#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code25b : memory 0x25b#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code25c : memory 0x25c#16 = 0x1#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code25d : memory 0x25d#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code25e : memory 0x25e#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code25f : memory 0x25f#16 = 0x94#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code260 : memory 0x260#16 = 0x6#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code261 : memory 0x261#16 = 0x24#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code262 : memory 0x262#16 = 0x35#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code263 : memory 0x263#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code264 : memory 0x264#16 = 0x0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code265 : memory 0x265#16 = 0x7#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code266 : memory 0x266#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code267 : memory 0x267#16 = 0x1f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code268 : memory 0x268#16 = 0x1c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code269 : memory 0x269#16 = 0x26#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code26a : memory 0x26a#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code26b : memory 0x26b#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code26c : memory 0x26c#16 = 0x5#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code26d : memory 0x26d#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code26e : memory 0x26e#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code26f : memory 0x26f#16 = 0x34#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code270 : memory 0x270#16 = 0x2c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have packed : 0#8 ++ (31#8 &&& opcode) = (opcode &&& 31#8).setWidth 16 := by
    rw [BitVec.append_def, BitVec.shiftLeftZeroExtend_eq, BitVec.setWidth'_eq]
    simp [BitVec.and_comm]
  have small : (opcode.setWidth 16 &&& 31#16).toNat ≤ 31 := by
    change (opcode.setWidth 16).toNat &&& 31 ≤ 31
    exact Nat.and_le_right
  by_cases ret : 64#16 &&& opcode.setWidth 16 = 0#16
  · iterate 46
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, pointer, top, ret,
          code22e, code22f, code230, code231, code232, code233, code234, code235, code236, code237, code238, code239, code23a, code23b, code23c, code23d, code23e, code23f, code240, code241, code242, code243, code244, code245, code246, code247, code248, code249, code24a, code24b, code24c, code24d, code24e, code24f, code250, code251, code252, code253, code254, code255, code256, code257, code258, code259, code25a, code25b, code25c, code25d, code25e, code25f, code260, code261, code262, code263, code264, code265, code266, code267, code268, code269, code26a, code26b, code26c, code26d, code26e, code26f, code270]
        rfl
    refine ⟨_, .refl _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [top, ret]
    all_goals try (simp only [packed, BitVec.setWidth_and,
      show (31#8).setWidth 16 = 31#16 from rfl] <;> simp (disch := bv_omega) only [Function.update_of_ne] <;> congr 2 <;> bv_omega)
    all_goals try
      intro address lower upper immutable
      have different : address ≠ 0x2bf#16 := by
        intro equality
        subst address
        exact immutable (by simp [MutableCode])
      simp (disch := first | exact different | bv_omega) only [Function.update_of_ne]
      exact code address lower upper immutable
    all_goals try exact BitVec.setWidth_append_eq_right
    all_goals try
      refine fun (address : Byte) (lower : address.toNat < returning.ptr.toNat) => ?_
      simp (disch := bv_omega) only [Function.update_of_ne]
    all_goals
      intro address h40 h41 h42 h43 h44 h2a3 h63a h73c
      simp only [BitVec.setWidth_ushiftRight_eq_extractLsb,
        BitVec.extractLsb'_append_eq_left, BitVec.setWidth_append_eq_right, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
      all_goals exact BitVec.extractLsb'_append_eq_left
  · iterate 45
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, pointer, top, ret, Ne.symm ret,
          code22e, code22f, code230, code231, code232, code233, code234, code235, code236, code237, code238, code239, code23a, code23b, code23c, code23d, code23e, code23f, code240, code241, code242, code243, code244, code245, code246, code247, code248, code249, code24a, code24b, code24c, code24d, code24e, code24f, code250, code251, code252, code253, code254, code255, code256, code257, code258, code259, code25a, code25b, code25c, code25d, code25e, code25f, code260, code261, code262, code263, code264, code265, code266, code267, code268, code269, code26a, code26b, code26c, code26d, code26e, code26f, code270]
        rfl
    refine ⟨_, .refl _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [top, ret]
    all_goals try (simp only [packed, BitVec.setWidth_and,
      show (31#8).setWidth 16 = 31#16 from rfl] <;> simp (disch := bv_omega) only [Function.update_of_ne] <;> congr 2 <;> bv_omega)
    all_goals try
      intro address lower upper immutable
      have different : address ≠ 0x2bf#16 := by
        intro equality
        subst address
        exact immutable (by simp [MutableCode])
      simp (disch := first | exact different | bv_omega) only [Function.update_of_ne]
      exact code address lower upper immutable
    all_goals try exact BitVec.setWidth_append_eq_right
    all_goals try
      refine fun (address : Byte) (lower : address.toNat < returning.ptr.toNat) => ?_
      simp (disch := bv_omega) only [Function.update_of_ne]
    all_goals
      intro address h40 h41 h42 h43 h44 h2a3 h63a h73c
      simp only [BitVec.setWidth_ushiftRight_eq_extractLsb,
        BitVec.extractLsb'_append_eq_left, BitVec.setWidth_append_eq_right, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
      all_goals exact BitVec.extractLsb'_append_eq_left

end ProgramProofs.Uxnmin
