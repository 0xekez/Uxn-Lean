import ProgramProofs.Uxnmin.Immediate
import ProgramProofs.Uxnmin.GuestStack

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def immediateWord (guest : Uxn.State) : Word :=
  guest.mem.ram (guest.pc + 1) ++ guest.mem.ram (guest.pc + 2)

def immediateNext (kind : ImmediateKind) (guest : Uxn.State) : Uxn.State :=
  match kind with
  | .jci =>
    { guest with
      pc := if guest.mem.wstk.data (guest.mem.wstk.ptr - 1) = 0 then guest.pc + 3
        else guest.pc + 3 + immediateWord guest
      mem.wstk.ptr := guest.mem.wstk.ptr - 1 }
  | .jmi => { guest with pc := guest.pc + 3 + immediateWord guest }
  | .jsi => { guest with
      pc := guest.pc + 3 + immediateWord guest
      mem.rstk := Stack.pushWord guest.mem.rstk (guest.pc + 3) }
  | .lit short ret => pushStack { guest with pc := guest.pc + (if short then 3 else 2) } ret short
      (if short then immediateWord guest else (guest.mem.ram (guest.pc + 1)).setWidth 16)

/-- Direct semantics of all seven non-BRK immediate instructions. -/
theorem guest_immediate (kind : ImmediateKind) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc = kind.opcode) :
    Uxn.step guest = .done (.next (immediateNext kind guest)) := by
  have highByte (high low : Byte) : ((high ++ low) >>> 8).setWidth 8 = high := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have lowByte (high low : Byte) : (high ++ low).setWidth 8 = low := by
    rw [BitVec.setWidth_append_eq_right]
  cases kind with
  | jci =>
    by_cases condition : guest.mem.wstk.data (guest.mem.wstk.ptr - 1) = 0
    all_goals simp [BitVec.sub_eq_add_neg] at condition
    all_goals simp [uxn_state, uxn_step, opcode, ImmediateKind.opcode, immediateNext, immediateWord,
      condition, BitVec.sub_eq_add_neg]
    all_goals bv_omega
  | jmi =>
    simp [uxn_state, uxn_step, opcode, ImmediateKind.opcode, immediateNext, immediateWord]
    bv_omega
  | jsi =>
    simp [uxn_state, uxn_step, opcode, ImmediateKind.opcode, immediateNext, immediateWord]
    bv_omega
  | lit short ret =>
    cases short <;> cases ret <;>
      simp [uxn_state, uxn_step, opcode, ImmediateKind.opcode, immediateNext, immediateWord,
        pushStack, highByte, lowByte]

end ProgramProofs.Uxnmin
