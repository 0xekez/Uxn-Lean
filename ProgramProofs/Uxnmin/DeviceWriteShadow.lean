import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Reaches
import ProgramProofs.Host.Reduction

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Every native DEO helper first commits its output to the shadow port table. -/
theorem device_write_shadow (ram : Word → Byte) (code : CodeImage ram)
    (port value : Byte) (working returning : Uxn.Stack)
    (workingSpace : working.ptr.toNat ≤ 248) :
    ∃ final, Reaches (machine ram 0x1af (Stack.push (Stack.push working value) port) returning) final ∧
      final.pc = 0x1bc ∧ final.mem.ram = Function.update ram (0x759 + port.setWidth 16) value ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧ final.mem.wstk.data working.ptr = value ∧
      final.mem.wstk.data (working.ptr + 1) = port ∧ final.mem.rstk = returning ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) := by
  have h1af : ram 0x1af#16 = 0x26#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b0 : ram 0x1b0#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b1 : ram 0x1b1#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b2 : ram 0x1b2#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b3 : ram 0x1b3#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b4 : ram 0x1b4#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b5 : ram 0x1b5#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b6 : ram 0x1b6#16 = 0x3c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b7 : ram 0x1b7#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b8 : ram 0x1b8#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1b9 : ram 0x1b9#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ba : ram 0x1ba#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1bb : ram 0x1bb#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  have joined : 0#8 ++ port = port.setWidth 16 := by simpa using (join_bytes 0#8 port).symm
  have masked : port.setWidth 16 &&& 0xff#16 = port.setWidth 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
    change port.toNat % 65536 &&& (2^8-1) = port.toNat % 65536
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have bound := port.isLt
    simp (disch := omega) [Nat.mod_eq_of_lt]
  have byteMask : port &&& 255#8 = port := BitVec.and_allOnes
  have padHigh : ((port.setWidth 16) >>> 8).setWidth 8 = 0#8 := by bv_omega
  iterate 8
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, h1af, h1b0, h1b1, h1b2, h1b3, h1b4, h1b5, h1b6, h1b7, h1b8, h1b9, h1ba, h1bb, joined, masked, byteMask, BitVec.and_comm, padHigh,
        byteHigh, byteLow]
      rfl
  refine ⟨_, .refl _, rfl, ?_, rfl, ?_, ?_, rfl, ?_⟩
  · simp [BitVec.add_comm, joined, masked, byteMask, BitVec.and_comm, padHigh,
      byteHigh, byteLow]
  · simp [byteHigh, byteLow]
  · simp [byteHigh, byteLow]
  · intro index below
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
