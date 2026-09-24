import ProgramProofs.Host.Memory

namespace ProgramProofs.HelloWorld
open Uxn Uxn.Host ProgramProofs.Host

/-- The hello-world program with an arbitrary zero-terminated byte string. -/
def rom (s : List Byte) : ByteArray :=
  ⟨#[0xa0, 0x01, 0x12, 0x94, 0x06, 0x20, 0x00, 0x03,
     0x02, 0x22, 0x00, 0x80, 0x18, 0x17, 0x21, 0x40,
     0xff, 0xf1] ++ (s.map UInt8.ofBitVec).toArray ++ #[0]⟩

/-- Loading any string preserves the program's fixed instruction prefix. -/
theorem rom_code (s : List Byte) : Code (rom []) 18 (initialState (rom s)).vm.mem.ram := by
  intro i
  have hi := i.isLt
  rw [initial_ram_byte _ _ (by simp [← ByteArray.size_data, rom] <;> omega) (by omega)]
  unfold rom
  rw [getElem!_pos _ _ (by simp <;> omega), getElem!_pos _ _ (by simp <;> omega)]
  rw [Array.getElem_append_left (by simp <;> omega), Array.getElem_append_left (by exact hi)]
  rw [Array.getElem_append_left (by simp)]
  simp

/-- The byte immediately after the string is its terminating NUL. -/
theorem rom_terminator (s : List Byte) (hsize : s.length < 0xfeee) :
    (initialState (rom s)).vm.mem.ram (0x112 + BitVec.ofNat 16 s.length) = 0 := by
  have address : 0x112 + BitVec.ofNat 16 s.length =
      0x100 + BitVec.ofNat 16 (18 + s.length) := by bv_omega
  rw [address, initial_ram_byte _ _ (by simp [← ByteArray.size_data, rom] <;> omega) (by omega)]
  unfold rom
  rw [getElem!_pos _ _ (by simp <;> omega)]
  rw [Array.getElem_append_right (by simp <;> omega)]
  simp

end ProgramProofs.HelloWorld
