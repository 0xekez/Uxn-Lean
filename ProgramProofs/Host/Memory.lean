import Uxn.Host

namespace ProgramProofs.Host
open Uxn Uxn.Host

/-- A copied source byte, independent of the destination's contents. -/
theorem copied_byte (source : ByteArray) (destination : Array UInt8)
    (offset count i : Nat) (hoffset : offset ≤ destination.size)
    (hi : i < count) (hsource : i < source.size) :
    (source.copySlice 0 ⟨destination⟩ offset count)[offset + i]! = source.data[i]! := by
  simp (disch := omega) [getElem!_def, getElem?_def, ByteArray.copySlice,
    ByteArray.getElem_eq_getElem_data, ← ByteArray.size_data, Array.getElem_append,
    Array.getElem_extract, Nat.min_eq_left hoffset]
  have hcopied : i < min count source.size := Nat.lt_min.mpr ⟨hi, hsource⟩
  simp [hcopied, hsource, show ¬ offset + i < offset by omega,
    show i < min count source.size +
      (destination.size - (offset + min count source.size)) by omega]

theorem initial_ram (source : ByteArray) (address : Word) :
    (initialState source).vm.mem.ram address =
      (source.copySlice 0 ⟨Array.replicate 0x10000 0⟩ 0x100 (0x10000 - 0x100))[address.toNat]!.toBitVec := by
  dsimp only [initialState, Uxn.Host.State.write]

theorem initial_ram_byte (source : ByteArray) (i : Nat)
    (hi : i < source.size) (hbound : i < 0xff00) :
    (initialState source).vm.mem.ram (0x100 + BitVec.ofNat 16 i) =
      source.data[i]!.toBitVec := by
  have haddress : (0x100 + BitVec.ofNat 16 i).toNat = 0x100 + i := by bv_omega
  rw [initial_ram, haddress]
  -- Normalize the copy length before applying the slice lemma, keeping
  -- conversion from unfolding the concrete destination array.
  simp only [Nat.reduceSub]
  exact congrArg UInt8.toBitVec
    (copied_byte source (Array.replicate 0x10000 0) 0x100 0xff00 i (by simp) hbound hi)

/-- The first `count` ROM bytes are present at the host's load address.
Only this code prefix is constrained; the rest of RAM may contain arbitrary data. -/
def Code (source : ByteArray) (count : Nat) (ram : Word → Byte) : Prop :=
  ∀ i : Fin count, ram (0x100 + BitVec.ofNat 16 i.val) = source.data[i.val]!.toBitVec

theorem Code.initial (source : ByteArray) (count : Nat)
    (hsize : count ≤ source.size) (hbound : count ≤ 0xff00) :
    Code source count (initialState source).vm.mem.ram := by
  intro i
  exact initial_ram_byte source i.val (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- Turn an absolute instruction address into an index into the code image. -/
theorem Code.read {source : ByteArray} {count : Nat} {ram : Word → Byte}
    (hc : Code source count ram) (address : Word)
    (hlo : 256 ≤ address.toNat) (hhi : address.toNat < 256 + count) :
    ram address = source.data[address.toNat - 256]!.toBitVec := by
  have haddress : 0x100 + BitVec.ofNat 16 (address.toNat - 256) = address := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simpa only [haddress] using hc ⟨address.toNat - 256, by omega⟩

/-- Initial RAM is the source ROM at 0x100, with zeroes outside it. -/
theorem initial_ram_eq (source : ByteArray) (address : Word) :
    (initialState source).vm.mem.ram address =
      if 0x100 ≤ address.toNat ∧ address.toNat - 0x100 < source.size then
        source.data[address.toNat - 0x100]!.toBitVec
      else 0 := by
  have bound : address.toNat < 0x10000 := address.isLt
  by_cases present : 0x100 ≤ address.toNat ∧ address.toNat - 0x100 < source.size
  · rw [if_pos present]
    have position : 0x100 + BitVec.ofNat 16 (address.toNat - 0x100) = address := by bv_omega
    simpa only [position] using ProgramProofs.Host.initial_ram_byte source
      (address.toNat - 0x100) present.2 (by omega)
  · rw [if_neg present, ProgramProofs.Host.initial_ram]
    change ¬ (0x100 ≤ address.toNat ∧ address.toNat - 0x100 < source.data.size) at present
    simp (disch := omega) [getElem!_def, getElem?_def, ByteArray.copySlice,
      ByteArray.getElem_eq_getElem_data, ← ByteArray.size_data,
      Array.getElem_append, Array.getElem_replicate]
    split <;> rename_i equality
    · split at equality
      · cases Option.some.inj equality
        rfl
      · cases equality
    · rfl

end ProgramProofs.Host
