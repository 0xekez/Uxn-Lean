import ProgramProofs.Uxnmin.Boundary
import ProgramProofs.Uxnmin.OpcodeModes

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem CompatibleDevices.read_word {start : Configuration}
    (compatible : CompatibleDevices start) (guest : Uxn.Host.State)
    (world : Void IO.RealWorld) (after : ReturnTo)
    (reachable : Reachable start (.running guest world))
    (control : guest.control = .evaluating after)
    (opcode : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 0x16)
    (short : (guest.vm.mem.ram guest.vm.pc).getLsbD 5 = true) :
    let port := (guestStack guest.vm ((guest.vm.mem.ram guest.vm.pc).getLsbD 6)).data
      ((guestStack guest.vm ((guest.vm.mem.ram guest.vm.pc).getLsbD 6)).ptr - 1)
    port + 1 ≠ Port.Console.read ∧ port + 1 ≠ Port.Console.type := by
  have allowed := compatible guest world after reachable control
  rcases opcode_modes (guest.vm.mem.ram guest.vm.pc) 0x16 (by decide) opcode with
    byte | byte | byte | byte | byte | byte | byte | byte
  all_goals simp [byte] at short
  all_goals simp [uxn_state, uxn_step, byte] at allowed
  all_goals simpa [byte, guestStack, BitVec.sub_eq_add_neg, Port.Console.read, Port.Console.type] using allowed.2

end ProgramProofs.Uxnmin.Model
