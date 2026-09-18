import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.Immediate

namespace ProgramProofs.Uxnmin
open Uxn

/-- A nonzero instruction whose low five bits vanish is an immediate instruction. -/
theorem immediate_of_zero_opcode (byte : Byte) (base : byte &&& 0x1f = 0) (nonzero : byte ≠ 0) :
    ∃ kind : ImmediateKind, byte = kind.opcode := by
  rcases opcode_modes byte 0 (by decide) base with
    opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode
  · exact (nonzero opcode).elim
  · exact ⟨.jci, by simpa [ImmediateKind.opcode] using opcode⟩
  · exact ⟨.jmi, by simpa [ImmediateKind.opcode] using opcode⟩
  · exact ⟨.jsi, by simpa [ImmediateKind.opcode] using opcode⟩
  · exact ⟨.lit false false, by simpa [ImmediateKind.opcode] using opcode⟩
  · exact ⟨.lit true false, by simpa [ImmediateKind.opcode] using opcode⟩
  · exact ⟨.lit false true, by simpa [ImmediateKind.opcode] using opcode⟩
  · exact ⟨.lit true true, by simpa [ImmediateKind.opcode] using opcode⟩

/-- The instruction-family dispatch exhausts all five-bit opcodes. -/
theorem low_opcode_cases (byte : Byte) :
    byte &&& 0x1f = 0 ∨ byte &&& 0x1f = 1 ∨ byte &&& 0x1f = 2 ∨ byte &&& 0x1f = 3 ∨
    byte &&& 0x1f = 4 ∨ byte &&& 0x1f = 5 ∨ byte &&& 0x1f = 6 ∨ byte &&& 0x1f = 7 ∨
    byte &&& 0x1f = 8 ∨ byte &&& 0x1f = 9 ∨ byte &&& 0x1f = 10 ∨ byte &&& 0x1f = 11 ∨
    byte &&& 0x1f = 12 ∨ byte &&& 0x1f = 13 ∨ byte &&& 0x1f = 14 ∨ byte &&& 0x1f = 15 ∨
    byte &&& 0x1f = 16 ∨ byte &&& 0x1f = 17 ∨ byte &&& 0x1f = 18 ∨ byte &&& 0x1f = 19 ∨
    byte &&& 0x1f = 20 ∨ byte &&& 0x1f = 21 ∨ byte &&& 0x1f = 22 ∨ byte &&& 0x1f = 23 ∨
    byte &&& 0x1f = 24 ∨ byte &&& 0x1f = 25 ∨ byte &&& 0x1f = 26 ∨ byte &&& 0x1f = 27 ∨
    byte &&& 0x1f = 28 ∨ byte &&& 0x1f = 29 ∨ byte &&& 0x1f = 30 ∨ byte &&& 0x1f = 31 := by
  have bound : (byte &&& 0x1f#8).toNat < 32 := by
    simpa only [BitVec.toNat_and, BitVec.toNat_ofNat] using Nat.and_lt_two_pow byte.toNat (by decide : 31 < 2^5)
  simp only [← BitVec.toNat_inj, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

end ProgramProofs.Uxnmin
