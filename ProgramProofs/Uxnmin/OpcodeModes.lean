import ProgramProofs.Host.Reduction

namespace ProgramProofs.Uxnmin
open Uxn

/-- Clearing the mode bits leaves exactly eight possible instruction bytes. -/
theorem opcode_modes (byte opcode : Byte) (small : opcode.toNat < 32)
    (base : byte &&& 0x1f = opcode) :
    byte = opcode ∨ byte = opcode + 0x20 ∨ byte = opcode + 0x40 ∨ byte = opcode + 0x60 ∨
    byte = opcode + 0x80 ∨ byte = opcode + 0xa0 ∨ byte = opcode + 0xc0 ∨ byte = opcode + 0xe0 := by
  have bound := byte.isLt
  have value := congrArg BitVec.toNat base
  simp only [BitVec.toNat_and] at value
  change byte.toNat &&& (2^5-1) = opcode.toNat at value
  rw [Nat.and_two_pow_sub_one_eq_mod] at value
  simp only [← BitVec.toNat_inj, BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

end ProgramProofs.Uxnmin
