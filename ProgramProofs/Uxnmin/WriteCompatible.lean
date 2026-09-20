import ProgramProofs.Uxnmin.Compatible
import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.GuestDeviceWrite

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Device compatibility supplies all supported-port assumptions needed by output simulation. -/
theorem device_write_compatible {start : Configuration} (compatible : CompatibleDevices start)
    (host : Uxn.Host.State) (world : Void IO.RealWorld)
    (after : ReturnTo)
    (reachable : Reachable start (.running host world))
    (control : host.control = .evaluating after)
    (opcode : host.vm.mem.ram host.vm.pc &&& 0x1f = 0x17) :
    let ret := (host.vm.mem.ram host.vm.pc).getLsbD 6
    let short := (host.vm.mem.ram host.vm.pc).getLsbD 5
    let stack := guestStack host.vm ret
    let port := stack.data (stack.ptr - 1)
    let outputPort := port + (if short then 1 else 0)
    port ≠ Port.Console.read ∧ port ≠ Port.Console.type ∧
    outputPort ≠ Port.Console.read ∧ outputPort ≠ Port.Console.type ∧ outputPort ∉ Port.File.ports ∧ (short = true → port ≠ Port.System.state) := by
  have allowed := compatible host world after reachable control
  rcases opcode_modes (host.vm.mem.ram host.vm.pc) 0x17 (by decide) opcode with byte | byte | byte | byte | byte | byte | byte | byte
  all_goals
    simp [uxn_state, uxn_step, byte] at allowed
    simp [byte, guestStack, BitVec.sub_eq_add_neg, Port.Console.read, Port.Console.type, Port.System.state]
    first
    | exact ⟨allowed.2.1, allowed.2.2, allowed.2.1, allowed.2.2, allowed.1⟩
    | obtain ⟨high, pair⟩ := allowed
      exact ⟨pair.1.2.1, pair.1.2.2, pair.2.2.1, pair.2.2.2, pair.2.1, high⟩

end ProgramProofs.Uxnmin.Model
