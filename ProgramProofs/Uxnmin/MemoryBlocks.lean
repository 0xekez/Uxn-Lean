import ProgramProofs.Uxnmin.Embedding
import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Execution

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem peek_byte (memory : Word → Byte) (address mask returnAddress : Word)
    (working returning : Uxn.Stack)
    (code : CodeImage memory)
    (mode : memory 0x44#16 = 0#8) :
    ∃ final, Reaches
      (machine memory 0x2f8
        (Stack.pushWord (Stack.pushWord working address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      final.mem.wstk.data working.ptr = 0 ∧
      final.mem.wstk.data (working.ptr + 1) = memory (relocate address) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.rstk.data = (Stack.pushWord returning returnAddress).data ∧
      ∀ offset : Byte, 5 ≤ offset.toNat →
        final.mem.wstk.data (working.ptr + offset) = working.data (working.ptr + offset) := by
  have code2f8 : memory 0x2f8#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f9 : memory 0x2f9#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2fa : memory 0x2fa#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2fb : memory 0x2fb#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2fe : memory 0x2fe#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ff : memory 0x2ff#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code300 : memory 0x300#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code301 : memory 0x301#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code302 : memory 0x302#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code303 : memory 0x303#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code304 : memory 0x304#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code305 : memory 0x305#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code306 : memory 0x306#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code307 : memory 0x307#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 10
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code2f8, code2f9, code2fa, code2fb, code2fe, code2ff, code300, code301, code302, code303,
        code304, code305, code306, code307, mode]
      rfl
  refine ⟨_, .refl _, ?_⟩
  simp [uxn_step, relocate, ramBase]
  intro offset outside
  simp (disch := bv_omega) only [Function.update_of_ne]

theorem peek_short (memory : Word → Byte) (address mask returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory) :
    ∃ final, Reaches
      (machine memory 0x308
        (Stack.pushWord (Stack.pushWord working address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      final.mem.wstk.data working.ptr = memory (relocate address) ∧
      final.mem.wstk.data (working.ptr + 1) = memory (relocate ((address + 1) &&& mask)) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ offset : Byte, 5 ≤ offset.toNat →
        final.mem.wstk.data (working.ptr + offset) = working.data (working.ptr + offset)) ∧
      ∀ offset : Byte, 6 ≤ offset.toNat →
        final.mem.rstk.data (returning.ptr + offset) = returning.data (returning.ptr + offset) := by
  have code308 : memory 0x308#16 = 0x2f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code309 : memory 0x309#16 = 0xaf#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code30a : memory 0x30a#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code30b : memory 0x30b#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code30c : memory 0x30c#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code30d : memory 0x30d#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code30e : memory 0x30e#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code30f : memory 0x30f#16 = 0x61#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code310 : memory 0x310#16 = 0x7c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code311 : memory 0x311#16 = 0x6f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code312 : memory 0x312#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code313 : memory 0x313#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code314 : memory 0x314#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code315 : memory 0x315#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code316 : memory 0x316#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code317 : memory 0x317#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have masked : ((address + 1#16 &&& mask) >>> 8).setWidth 8 ++
      ((address + 1#16).setWidth 8 &&& mask.setWidth 8) = (address + 1#16) &&& mask := by
    rw [← BitVec.setWidth_and, append_split]
  iterate 12
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code308, code309, code30a, code30b, code30c, code30d, code30e, code30f, code310, code311,
        code312, code313, code314, code315, code316, code317]
      rfl
  refine ⟨_, .refl _, ?_⟩
  simp [uxn_step, relocate, ramBase, masked]
  constructor <;> intro offset outside <;>
    simp (disch := bv_omega) only [Function.update_of_ne]

theorem poke_byte (memory : Word → Byte) (address mask value returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (mode : memory 0x44#16 = 0#8) (confined : address.toNat < ramSize) :
    ∃ final, Reaches
      (machine memory 0x2d8
        (Stack.pushWord (Stack.pushWord (Stack.pushWord working value) address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧
      final.mem.ram = Function.update memory (relocate address) (value.setWidth 8) ∧
      final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.rstk.data = (Stack.pushWord returning returnAddress).data ∧
      ∀ offset : Byte, 7 ≤ offset.toNat →
        final.mem.wstk.data (working.ptr + offset) = working.data (working.ptr + offset) := by
  have code2d8 : memory 0x2d8#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2d9 : memory 0x2d9#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2da : memory 0x2da#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2db : memory 0x2db#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2de : memory 0x2de#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2df : memory 0x2df#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e0 : memory 0x2e0#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e1 : memory 0x2e1#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e2 : memory 0x2e2#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e3 : memory 0x2e3#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e4 : memory 0x2e4#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e5 : memory 0x2e5#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have separate (location : Word) (below : location.toNat < 0x859) :
      location ≠ 2137#16 + address := by
    dsimp [ramSize, ramBase] at confined
    bv_omega
  iterate 9
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code2d8, code2d9, code2da, code2db, code2de, code2df, code2e0, code2e1, code2e2, code2e3,
        code2e4, code2e5, mode, Function.update_of_ne, separate]
      rfl
  refine ⟨_, .refl _, ?_⟩
  simp [uxn_step, relocate, ramBase]
  intro offset outside
  simp (disch := bv_omega) only [Function.update_of_ne]

theorem poke_short (memory : Word → Byte) (address mask value returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (firstConfined : address.toNat < ramSize)
    (secondConfined : ((address + 1#16) &&& mask).toNat < ramSize) :
    ∃ final, Reaches
      (machine memory 0x2e6
        (Stack.pushWord (Stack.pushWord (Stack.pushWord working value) address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧
      final.mem.ram = Function.update
        (Function.update memory (relocate address) ((value >>> 8).setWidth 8))
        (relocate ((address + 1) &&& mask)) (value.setWidth 8) ∧
      final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ offset : Byte, 6 ≤ offset.toNat →
        final.mem.wstk.data (working.ptr + offset) = working.data (working.ptr + offset)) ∧
      ∀ offset : Byte, 6 ≤ offset.toNat →
        final.mem.rstk.data (returning.ptr + offset) = returning.data (returning.ptr + offset) := by
  have code2e6 : memory 0x2e6#16 = 0x2f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e7 : memory 0x2e7#16 = 0x2f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e8 : memory 0x2e8#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2e9 : memory 0x2e9#16 = 0xef#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ea : memory 0x2ea#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2eb : memory 0x2eb#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ec : memory 0x2ec#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ed : memory 0x2ed#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ee : memory 0x2ee#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2ef : memory 0x2ef#16 = 0x61#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f0 : memory 0x2f0#16 = 0x7c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f1 : memory 0x2f1#16 = 0x6f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f2 : memory 0x2f2#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f3 : memory 0x2f3#16 = 0x08#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f4 : memory 0x2f4#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f5 : memory 0x2f5#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f6 : memory 0x2f6#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2f7 : memory 0x2f7#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have separate (location : Word) (below : location.toNat < 0x859) :
      location ≠ 2137#16 + address := by
    dsimp [ramSize, ramBase] at firstConfined
    bv_omega
  have secondSeparate (location : Word) (below : location.toNat < 0x859) :
      location ≠ 2137#16 + ((address + 1#16) &&& mask) := by
    change ((address + 1#16) &&& mask).toNat < 0xf7a7 at secondConfined
    bv_omega
  have masked : ((address + 1#16 &&& mask) >>> 8).setWidth 8 ++
      ((address + 1#16).setWidth 8 &&& mask.setWidth 8) = (address + 1#16) &&& mask := by
    rw [← BitVec.setWidth_and, append_split]
  iterate 14
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code2e6, code2e7, code2e8, code2e9, code2ea, code2eb, code2ec, code2ed, code2ee, code2ef,
        code2f0, code2f1, code2f2, code2f3, code2f4, code2f5, code2f6, code2f7,
        Function.update_of_ne, separate, secondSeparate, masked]
      rfl
  refine ⟨_, .refl _, ?_⟩
  simp [uxn_step, relocate, ramBase, masked]
  constructor <;> intro offset outside <;>
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
