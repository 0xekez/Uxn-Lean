import ProgramProofs.Uxnmin.GuestStack
import ProgramProofs.Host.Reduction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

def deviceReadNext (guest : Uxn.State) (host : Uxn.Host.State) (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack {guest with pc := guest.pc + 1} ret keep 1) ret short
    (if short then host.readWord ((guestStack guest ret).data ((guestStack guest ret).ptr - 1))
     else (host.read ((guestStack guest ret).data ((guestStack guest ret).ptr - 1))).setWidth 16)

/-- Direct DEI semantics reads one or two ports in every selected-stack and keep mode. -/
theorem guest_device_read (guest : Uxn.State) (host : Uxn.Host.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x16) :
    Uxn.Host.step guest host = pure (.next (deviceReadNext guest host
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7)), host) := by
  have possibilities (byte : Byte) (low : byte &&& 0x1f = 0x16) :
      byte = 0x16 ∨ byte = 0x36 ∨ byte = 0x56 ∨ byte = 0x76 ∨
      byte = 0x96 ∨ byte = 0xb6 ∨ byte = 0xd6 ∨ byte = 0xf6 := by
    have bound := byte.isLt
    have value := congrArg BitVec.toNat low
    simp only [BitVec.toNat_and] at value
    change byte.toNat &&& (2^5 - 1) = _ at value
    rw [Nat.and_two_pow_sub_one_eq_mod] at value
    simp [← BitVec.toNat_inj, BitVec.ofNat_eq_ofNat] at value ⊢
    omega
  rcases possibilities _ opcode with byte | byte | byte | byte | byte | byte | byte | byte
  all_goals
    simp [Uxn.Host.step, uxn_state, uxn_step, byte, respond, Request.Result, Patch.apply,
      deviceReadNext, popStack, pushStack, guestStack, Host.State.readWord]

end ProgramProofs.Uxnmin
