import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.DeviceEffect
import ProgramProofs.Uxnmin.GuestStack

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

def deviceWriteNext (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  popStack {guest with pc := guest.pc + 1} ret keep (if short then 3 else 2)

def deviceWriteHost (guest : Uxn.State) (host : Uxn.Host.State) (ret short : Bool) : Uxn.Host.State :=
  let stack := guestStack guest ret
  let port := stack.data (stack.ptr - 1)
  deviceHost (if short then host.write port (stack.data (stack.ptr - 3)) else host)
    (port + (if short then 1 else 0)) (stack.data (stack.ptr - 2))

/-- Direct DEO semantics consists of the same output action in every opcode mode. -/
theorem guest_device_write (guest : Uxn.State) (host : Uxn.Host.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x17)
    (supported : (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).data
      ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr - 1) +
        (if (guest.mem.ram guest.pc).getLsbD 5 then 1 else 0) ∉ Port.File.ports) :
    Uxn.Host.step guest host = (do
      deviceOutput ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).data
        ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr - 1) +
          (if (guest.mem.ram guest.pc).getLsbD 5 then 1 else 0))
        ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).data
          ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr - 2))
      pure (.next (deviceWriteNext guest ((guest.mem.ram guest.pc).getLsbD 6)
        ((guest.mem.ram guest.pc).getLsbD 5) ((guest.mem.ram guest.pc).getLsbD 7)),
        deviceWriteHost guest host ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5))) := by
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  rcases opcode_modes (guest.mem.ram guest.pc) 0x17 (by decide) opcode with byte | byte | byte | byte | byte | byte | byte | byte
  all_goals
    simp only [byte] at supported ⊢
    simp [guestStack, BitVec.sub_eq_add_neg] at supported
    simp [Uxn.Host.step, uxn_state, uxn_step, byte, respond, Request.Result,
      deviceWriteNext, deviceWriteHost, popStack, guestStack]
    rw [deo_nonfile _ _ _ _ supported]
    simp [uxn_state, Patch.apply, byteHigh, byteLow]

end ProgramProofs.Uxnmin
