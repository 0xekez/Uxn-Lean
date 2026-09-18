import ProgramProofs.Uxnmin.GuestLoad

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The first byte written by a load records its first memory read. -/
theorem loadResult_first (kind : AddressMode) (guest : Uxn.State) (ret short keep : Bool) :
    (guestStack (loadResult kind guest ret short keep) ret).data
      (if keep then (guestStack guest ret).ptr else (guestStack guest ret).ptr - kind.consumed) =
      guest.mem.ram (kind.address guest ret) := by
  cases ret <;> cases short <;> cases keep <;>
    simp [loadResult, guestStack, popStack, pushStack, Stack.pushWord, Stack.push,
      BitVec.setWidth_ushiftRight_eq_extractLsb]
  all_goals rw [BitVec.extractLsb'_append_eq_left]

/-- The second byte of a short load records its second memory read. -/
theorem loadResult_second (kind : AddressMode) (guest : Uxn.State) (ret keep : Bool) :
    (guestStack (loadResult kind guest ret true keep) ret).data
      ((if keep then (guestStack guest ret).ptr else (guestStack guest ret).ptr - kind.consumed) + 1) =
      guest.mem.ram (kind.following (kind.address guest ret)) := by
  cases ret <;> cases keep <;>
    simp [loadResult, guestStack, popStack, pushStack, Stack.pushWord, Stack.push]
  all_goals rw [BitVec.setWidth_append_eq_right]

end ProgramProofs.Uxnmin
