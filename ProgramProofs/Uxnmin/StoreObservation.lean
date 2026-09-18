import ProgramProofs.Uxnmin.GuestStore

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem AddressMode.following_ne (kind : AddressMode) (guest : Uxn.State) (ret : Bool) :
    kind.following (kind.address guest ret) ≠ kind.address guest ret := by
  cases kind
  · dsimp [AddressMode.following, AddressMode.address]
    bv_omega
  · dsimp [AddressMode.following]
    bv_omega
  · dsimp [AddressMode.following]
    bv_omega

/-- Each written byte has its value prescribed by the popped operand. -/
theorem storeResult_byte (kind : AddressMode) (guest : Uxn.State) (ret short keep second : Bool)
    (word : second = true → short = true) :
    (storeResult kind guest ret short keep).mem.ram
      ((if second then kind.following else id) (kind.address guest ret)) =
      ((if short && !second then fun value : Word => value >>> 8 else id)
        (operand (guestStack guest ret) ((guestStack guest ret).ptr - kind.consumed) short)).setWidth 8 := by
  cases second
  · cases short <;> simp [storeResult, storeBytes, Ne.symm (AddressMode.following_ne kind guest ret)]
  · rw [word rfl]
    simp [storeResult, storeBytes]

end ProgramProofs.Uxnmin
