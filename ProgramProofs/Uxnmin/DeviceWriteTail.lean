import ProgramProofs.Uxnmin.DeviceWriteShadow

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Unhandled non-file output ports change only the shadow port table. -/
theorem device_write_silent (ram : Word → Byte) (code : CodeImage ram)
    (port value : Byte) (working returning : Uxn.Stack) (returnAddress : Word)
    (workingSpace : working.ptr.toNat ≤ 253) (returnSpace : returning.ptr.toNat ≤ 253) :
    ∃ final, Reaches (machine ram 0x1f5 (Stack.push (Stack.push working value) port)
      (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = ram ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have h1f5 : ram 0x1f5#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1f6 : ram 0x1f6#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 2
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, h1f5, h1f6]
      rfl
  refine ⟨_, .refl _, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals intro index below; simp (disch := bv_omega) only [Function.update_of_ne]

/-- Console-vector output updates the two self-modified immediate bytes. -/
theorem device_write_vector (ram : Word → Byte) (code : CodeImage ram)
    (value : Byte) (working returning : Uxn.Stack) (returnAddress : Word)
    (workingSpace : working.ptr.toNat ≤ 248) (returnSpace : returning.ptr.toNat ≤ 253) :
    ∃ final, Reaches (machine ram 0x1d5 (Stack.push (Stack.push working value) 0x11)
      (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = Function.update (Function.update ram 0x175 (ram 0x769)) 0x176 value ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have h1d5 : ram 0x1d5#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d6 : ram 0x1d6#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d7 : ram 0x1d7#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d8 : ram 0x1d8#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d9 : ram 0x1d9#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1da : ram 0x1da#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1db : ram 0x1db#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1dc : ram 0x1dc#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1dd : ram 0x1dd#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1de : ram 0x1de#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1df : ram 0x1df#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e0 : ram 0x1e0#16 = 0x93#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e1 : ram 0x1e1#16 = 0x33#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e2 : ram 0x1e2#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  iterate 9
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, byteHigh, byteLow]
      rfl
  refine ⟨_, .refl _, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp [byteHigh, byteLow]
  · intro index below
    simp (disch := bv_omega) only [Function.update_of_ne]
  · intro index below
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
