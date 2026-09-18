import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.GuestDeviceWrite

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host

/-- Device compatibility supplies all supported-port assumptions needed by output simulation. -/
theorem device_write_compatible {start : Configuration} (compatible : CompatibleDevices start)
    (guest : Uxn.State) (host : Uxn.Host.State) (world : Void IO.RealWorld)
    (reachable : Reachable start (.ok (.next guest, host) world))
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x17) :
    let ret := (guest.mem.ram guest.pc).getLsbD 6
    let short := (guest.mem.ram guest.pc).getLsbD 5
    let stack := guestStack guest ret
    let port := stack.data (stack.ptr - 1)
    let outputPort := port + (if short then 1 else 0)
    port ≠ Port.Console.read ∧ port ≠ Port.Console.type ∧
    outputPort ≠ Port.Console.read ∧ outputPort ≠ Port.Console.type ∧ outputPort ∉ Port.File.ports := by
  have allowed := compatible guest host world reachable
  rcases opcode_modes (guest.mem.ram guest.pc) 0x17 (by decide) opcode with byte | byte | byte | byte | byte | byte | byte | byte
  all_goals
    simp [uxn_state, uxn_step, byte] at allowed
    simp [byte, guestStack, BitVec.sub_eq_add_neg]
    first
    | exact ⟨allowed.2.1, allowed.2.2, allowed.2.1, allowed.2.2, allowed.1⟩
    | obtain ⟨_, pair⟩ := allowed
      exact ⟨pair.1.2.1, pair.1.2.2, pair.2.2.1, pair.2.2.2, pair.2.1⟩

end ProgramProofs.Uxnmin
