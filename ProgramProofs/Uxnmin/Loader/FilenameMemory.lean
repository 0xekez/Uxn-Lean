import ProgramProofs.Uxnmin.Loader.NameBytes
import ProgramProofs.Uxnmin.Loader.FilenameDecode

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.NameBytes
open private Uxn.Host.fileName from Uxn.Host

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- The filename loop writes exactly the given byte interval. -/
theorem writeName_spec (bytes : List UInt8) (offset : Nat) (ram : Word → Byte)
    (fits : offset + bytes.length < 0x10000) :
    (∀ (i : Nat) (hi : i < bytes.length),
      ProgramProofs.Uxnmin.writeName bytes offset ram (BitVec.ofNat 16 (offset + i)) = (bytes[i]'hi).toBitVec) ∧
    (∀ address : Word, address.toNat < offset ∨ offset + bytes.length ≤ address.toNat →
      ProgramProofs.Uxnmin.writeName bytes offset ram address = ram address) := by
  induction bytes generalizing offset ram with
  | nil => simp [ProgramProofs.Uxnmin.writeName]
  | cons byte bytes ih =>
    have tail := ih (offset + 1) (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec)
      (by simp at fits; omega)
    constructor
    · intro i hi
      cases i with
      | zero =>
        have low : (BitVec.ofNat 16 offset).toNat < offset + 1 := by
          have small : offset < 0x10000 := by simp at fits; omega
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        simpa [ProgramProofs.Uxnmin.writeName] using tail.2 (BitVec.ofNat 16 offset) (Or.inl low)
      | succ i =>
        simpa [ProgramProofs.Uxnmin.writeName, Nat.add_assoc, Nat.add_comm 1 i] using
          tail.1 i (by simpa using hi)
    · intro address outside
      have different : address ≠ BitVec.ofNat 16 offset := by
        intro same
        have small : offset < 0x10000 := by simp at fits; omega
        simp only [same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, List.length_cons] at outside
        omega
      change ProgramProofs.Uxnmin.writeName bytes (offset + 1)
        (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec) address = ram address
      rw [tail.2 address (by simp only [List.length_cons] at outside; omega),
        Function.update_of_ne different]

/-- Filename input preserves memory outside the first 64 bytes and decodes as
its original String after the loop's self-modifying immediate is updated. -/
theorem filename_memory (filename : String) (ram : Word → Byte)
    (working returning : Uxn.Stack)
    (fits : filename.utf8ByteSize < 0x40) (noNul : 0 ∉ filename.toUTF8.data)
    (zero : ram (BitVec.ofNat 16 filename.utf8ByteSize) = 0) :
    (∀ address : Word, 0x40 ≤ address.toNat →
      ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 ram address = ram address) ∧
    Uxn.Host.fileName { ram := (Function.update (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 ram)
      0x13e (BitVec.ofNat 8 filename.utf8ByteSize)), wstk := working, rstk := returning } 0 =
        some filename := by
  have length : filename.toUTF8.data.toList.length = filename.utf8ByteSize := rfl
  have spec := writeName_spec filename.toUTF8.data.toList 0 ram (by rw [length]; omega)
  constructor
  · intro address high
    exact spec.2 address (Or.inr (by rw [length]; omega))
  · apply fileName_string
    · omega
    · exact noNul
    · intro i hi
      have small : i < 0x40 := by change i < filename.utf8ByteSize at hi; omega
      have different : BitVec.ofNat 16 i ≠ 0x13e#16 := by bv_omega
      dsimp only
      simp only [BitVec.ofNat_eq_ofNat]
      rw [Function.update_of_ne different]
      simpa [ByteArray.getElem_eq_getElem_data] using spec.1 i hi
    · have different : BitVec.ofNat 16 filename.utf8ByteSize ≠ 0x13e#16 := by bv_omega
      dsimp only
      simp only [BitVec.ofNat_eq_ofNat]
      rw [Function.update_of_ne different]
      rw [spec.2 _ (Or.inr (by rw [length]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show filename.utf8ByteSize < 65536 by omega)]))]
      exact zero

/-- The filename's zero-page writes preserve the loaded ROM. -/
theorem writeName_code (bytes : List UInt8) (offset : Nat) (ram : Word → Byte)
    (fits : offset + bytes.length < 0x40) (code : Code rom rom.size ram) :
    Code rom rom.size (ProgramProofs.Uxnmin.writeName bytes offset ram) := by
  intro i
  rw [(writeName_spec bytes offset ram (by omega)).2 _ (Or.inr ?_)]
  · exact code i
  · have bound : i.val < 0x456 := i.isLt
    bv_omega

end ProgramProofs.Uxnmin
