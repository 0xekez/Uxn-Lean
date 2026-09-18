import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Execution
import ProgramProofs.Host.Reduction

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The second byte of DEI2 comes from the shadow port table, with byte wrapping. -/
theorem device_reader_low (ram : Word → Byte) (code : CodeImage ram) (port : Byte)
    (working returning : Uxn.Stack) (workingSpace : working.ptr.toNat ≤ 250) :
    ∃ final, Reaches (machine ram 0x346 (Stack.pushWord working (port.setWidth 16)) returning) final ∧
      final.pc = 0x293 ∧ final.mem.ram = ram ∧ final.mem.rstk = returning ∧
      final.mem.wstk.ptr = working.ptr + 1 ∧
      final.mem.wstk.data working.ptr = ram (0x759 + (port + 1).setWidth 16) ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) := by
  have h346 : ram 0x346#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h347 : ram 0x347#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h348 : ram 0x348#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h349 : ram 0x349#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h34a : ram 0x34a#16 = 0x3c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h34b : ram 0x34b#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h34c : ram 0x34c#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h34d : ram 0x34d#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h34e : ram 0x34e#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h34f : ram 0x34f#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h350 : ram 0x350#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h351 : ram 0x351#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h352 : ram 0x352#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have masked : (port.setWidth 16 + 1) &&& 255#16 = (port + 1).setWidth 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change ((port.toNat % 65536 + 1) % 65536) &&& (2^8 - 1) = ((port.toNat + 1) % 256) % 65536
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have bound := port.isLt
    simp (disch := omega) only [Nat.mod_eq_of_lt]
  have smallMask (byte : Byte) : byte.setWidth 16 &&& 255#16 = byte.setWidth 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
    change byte.toNat % 65536 &&& (2^8 - 1) = byte.toNat % 65536
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have bound := byte.isLt
    simp (disch := omega) only [Nat.mod_eq_of_lt]
  have padHigh (byte : Byte) : ((byte.setWidth 16) >>> 8).setWidth 8 = 0#8 := by bv_omega
  have incrementLow : (1#16 + port.setWidth 16).setWidth 8 = port + 1#8 := by bv_omega
  have maskedLeft : (1#16 + port.setWidth 16) &&& 255#16 = (port + 1#8).setWidth 16 := by
    rw [BitVec.add_comm]
    exact masked
  have maskHigh : (((port + 1).setWidth 16) >>> 8).setWidth 8 = 0#8 := by bv_omega
  have byteMask : (port + 1) &&& 255#8 = port + 1 := BitVec.and_allOnes
  have joined (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by simpa using (join_bytes 0#8 byte).symm
  simp only [BitVec.ofNat_eq_ofNat] at masked maskHigh byteMask
  iterate 7
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, h346, h347, h348, h349, h34a, h34b, h34c, h34d, h34e, h34f, h350, h351, h352, smallMask, masked, maskedLeft, incrementLow, padHigh, maskHigh,
        byteMask, joined, BitVec.and_comm]
      rfl
  refine ⟨_, .refl _, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [BitVec.add_comm, smallMask, masked, maskedLeft, incrementLow, padHigh, maskHigh, byteMask, joined, BitVec.and_comm]
  · intro index before
    simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
