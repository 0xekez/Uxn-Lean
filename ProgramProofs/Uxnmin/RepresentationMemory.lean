import ProgramProofs.Uxnmin.StoreResult

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Guest RAM writes change their relocated native byte and preserve the rest of the invariant. -/
theorem Represents.writeRam {guest outer : Uxn.State} (rep : Represents guest outer)
    (address : Word) (value : Byte) (confined : address.toNat < ramSize) :
    Represents { guest with mem.ram := Function.update guest.mem.ram address value }
      { outer with mem.ram := Function.update outer.mem.ram (relocate address) value } := by
  have after : 0x859 ≤ (relocate address).toNat := by
    dsimp [relocate, ramSize] at *
    bv_omega
  have separate (location : Word) (below : location.toNat < 0x859) : location ≠ relocate address := by
    intro equal
    rw [equal] at below
    omega
  refine ⟨rep.code.write _ _ (.inr (.inl (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · intro location below
    change Function.update outer.mem.ram (relocate address) value (relocate location) =
      Function.update guest.mem.ram address value location
    by_cases equal : location = address
    · simp [equal]
    · rw [Function.update_of_ne (by simpa [relocate] using equal), Function.update_of_ne equal]
      exact rep.ram location below
  · intro ret index
    change Function.update outer.mem.ram (relocate address) value (stackBase ret + index.setWidth 16) = _
    rw [Function.update_of_ne (separate _ (by cases ret <;> dsimp [stackBase] <;> bv_omega))]
    exact rep.stackData ret index
  · intro ret
    change Function.update outer.mem.ram (relocate address) value (stackBase ret + 0x100) = _
    rw [Function.update_of_ne (separate _ (by cases ret <;> decide))]
    exact rep.stackPointer ret
  · change Function.update outer.mem.ram (relocate address) value 0x45 = _
    rw [Function.update_of_ne (separate _ (by decide))]
    exact rep.pcHigh
  · change Function.update outer.mem.ram (relocate address) value 0x46 = _
    rw [Function.update_of_ne (separate _ (by decide))]
    exact rep.pcLow

/-- One- and two-byte stores preserve the full interpreter representation. -/
theorem Represents.storeBytes {guest outer : Uxn.State} (rep : Represents guest outer)
    (address following value : Word) (short : Bool)
    (firstBound : address.toNat < ramSize) (secondBound : short = true → following.toNat < ramSize) :
    Represents (storeBytes guest address following value short)
      (storeBytes outer (relocate address) (relocate following) value short) := by
  cases short with
  | false => exact rep.writeRam address (value.setWidth 8) firstBound
  | true =>
    exact (rep.writeRam address ((value >>> 8).setWidth 8) firstBound).writeRam
      following (value.setWidth 8) (secondBound rfl)

end ProgramProofs.Uxnmin
