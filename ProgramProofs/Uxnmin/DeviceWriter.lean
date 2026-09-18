import ProgramProofs.Uxnmin.DeviceWriteShadow
import ProgramProofs.Uxnmin.OperandPair

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The device writer stores a word's high byte and invokes vm/deo for its low byte. -/
theorem device_writer (ram : Word → Byte) (code : CodeImage ram)
    (short : Bool) (port : Byte) (value : Word) (working returning : Uxn.Stack)
    (mode : ram 0x44#16 = if short then 1 else 0)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 253) :
    ∃ final, Reaches (machine ram 0x318
      (Stack.pushWord (Stack.pushWord working value) (port.setWidth 16)) returning) final ∧
      final.pc = 0x1af ∧
      final.mem.ram = (if short then Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8) else ram) ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      final.mem.wstk.data working.ptr = value.setWidth 8 ∧
      final.mem.wstk.data (working.ptr + 1) = port + (if short then 1 else 0) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have h318 : ram 0x318#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h319 : ram 0x319#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h31a : ram 0x31a#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h31b : ram 0x31b#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h31c : ram 0x31c#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h31d : ram 0x31d#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h31e : ram 0x31e#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h31f : ram 0x31f#16 = 0x05#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h320 : ram 0x320#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h321 : ram 0x321#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h322 : ram 0x322#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h323 : ram 0x323#16 = 0x8b#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h324 : ram 0x324#16 = 0x2f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h325 : ram 0x325#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h326 : ram 0x326#16 = 0xef#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h327 : ram 0x327#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h328 : ram 0x328#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h329 : ram 0x329#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h32a : ram 0x32a#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h32b : ram 0x32b#16 = 0x15#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h32c : ram 0x32c#16 = 0x4f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h32d : ram 0x32d#16 = 0x42#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h32e : ram 0x32e#16 = 0x01#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h32f : ram 0x32f#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h330 : ram 0x330#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h331 : ram 0x331#16 = 0x7d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  have padHigh : (port.setWidth 16 >>> 8).setWidth 8 = 0#8 := by bv_omega
  have joined : 0#8 ++ port = port.setWidth 16 := by simpa using (join_bytes 0#8 port).symm
  have separate (address : Word) (small : address.toNat < 0x555) : address ≠ 0x759 + port.setWidth 16 := by bv_omega
  have h32cupdated : (Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8)) 0x32c#16 = ram 0x32c#16 := by rw [Function.update_of_ne (separate _ (by decide))]
  have h32dupdated : (Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8)) 0x32d#16 = ram 0x32d#16 := by rw [Function.update_of_ne (separate _ (by decide))]
  have h32eupdated : (Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8)) 0x32e#16 = ram 0x32e#16 := by rw [Function.update_of_ne (separate _ (by decide))]
  have h32fupdated : (Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8)) 0x32f#16 = ram 0x32f#16 := by rw [Function.update_of_ne (separate _ (by decide))]
  have h330updated : (Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8)) 0x330#16 = ram 0x330#16 := by rw [Function.update_of_ne (separate _ (by decide))]
  have h331updated : (Function.update ram (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8)) 0x331#16 = ram 0x331#16 := by rw [Function.update_of_ne (separate _ (by decide))]
  simp only [BitVec.ofNat_eq_ofNat] at h32cupdated h32dupdated h32eupdated h32fupdated h330updated h331updated
  cases short
  · iterate 7
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, h318, h319, h31a, h31b, h31c, h31d, h31e, h31f, h320, h321, h322, h323, h324, h325, h326, h327, h328, h329, h32a, h32b, h32c, h32d, h32e, h32f, h330, h331, h32cupdated, h32dupdated, h32eupdated, h32fupdated, h330updated, h331updated, mode, byteHigh, byteLow, padHigh, joined]
        rfl
    refine ⟨_, .refl _, rfl, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
    · simp [byteHigh, byteLow, padHigh, joined, BitVec.add_comm]
    · simp [byteHigh, byteLow, padHigh, joined]
    · simp [byteHigh, byteLow, padHigh, joined]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  · iterate 13
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, h318, h319, h31a, h31b, h31c, h31d, h31e, h31f, h320, h321, h322, h323, h324, h325, h326, h327, h328, h329, h32a, h32b, h32c, h32d, h32e, h32f, h330, h331, h32cupdated, h32dupdated, h32eupdated, h32fupdated, h330updated, h331updated, mode, byteHigh, byteLow, padHigh, joined]
        rfl
    refine ⟨_, .refl _, rfl, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
    · simp [byteHigh, byteLow, padHigh, joined, BitVec.add_comm]
    · simp [byteHigh, byteLow, padHigh, joined]
    · simp [byteHigh, byteLow, padHigh, joined] <;> bv_omega
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
