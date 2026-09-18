import ProgramProofs.Uxnmin.GuestImmediate

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def ImmediateKind.reads (kind : ImmediateKind) (guest : Uxn.State) (second : Bool) : Prop :=
  match kind with
  | .jci => guest.mem.wstk.data (guest.mem.wstk.ptr - 1) ≠ 0
  | .jmi | .jsi => True
  | .lit short _ => second = true → short = true

def immediateObserve (kind : ImmediateKind) (guest : Uxn.State) (second : Bool) (result : Uxn.State) : Byte :=
  match kind with
  | .lit _ ret => (guestStack result ret).data ((guestStack guest ret).ptr + if second then 1 else 0)
  | _ =>
    if second then (result.pc - (guest.pc + 3)).setWidth 8
    else ((result.pc - (guest.pc + 3)) >>> 8).setWidth 8

/-- The resulting PC or pushed stack byte determines each immediate byte that was read. -/
theorem immediate_observed (kind : ImmediateKind) (guest : Uxn.State) (second : Bool)
    (read : kind.reads guest second) :
    immediateObserve kind guest second (immediateNext kind guest) =
      guest.mem.ram (guest.pc + 1 + if second then 1 else 0) := by
  have highByte (high low : Byte) : ((high ++ low) >>> 8).setWidth 8 = high := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have lowByte (high low : Byte) : (high ++ low).setWidth 8 = low := by
    rw [BitVec.setWidth_append_eq_right]
  have cancel (base offset : Word) : base + offset - base = offset := by bv_omega
  have jump (result : Uxn.State) (pc : result.pc = guest.pc + 3 + immediateWord guest) :
      (if second then (result.pc - (guest.pc + 3)).setWidth 8
       else ((result.pc - (guest.pc + 3)) >>> 8).setWidth 8) =
        guest.mem.ram (guest.pc + 1 + if second then 1 else 0) := by
    rw [pc, cancel]
    cases second <;> simp [immediateWord, highByte, lowByte, BitVec.add_assoc]
  cases kind with
  | jci =>
    apply jump
    change (if guest.mem.wstk.data (guest.mem.wstk.ptr - 1) = 0 then guest.pc + 3
      else guest.pc + 3 + immediateWord guest) = _
    exact if_neg read
  | jmi => exact jump _ rfl
  | jsi => exact jump _ rfl
  | lit short ret =>
    cases short <;> cases ret <;> cases second <;>
      simp_all [ImmediateKind.reads, immediateObserve, immediateNext, immediateWord,
        pushStack, guestStack, Stack.pushWord, Stack.push, BitVec.add_assoc]

end ProgramProofs.Uxnmin
