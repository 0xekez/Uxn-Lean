import ProgramProofs.Uxnmin.LoadingBlock
import ProgramProofs.Uxnmin.WriteBlock
import ProgramProofs.Uxnmin.BrkBlock
import ProgramProofs.Uxnmin.ConsoleInput
import ProgramProofs.Uxnmin.DeliveryBlock

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host

/-- Every reachable boundary admits a finite silent chunk around its matching step. -/
theorem boundary_blocks (filename : String) (world : Void IO.RealWorld)
    (fits : filename.utf8ByteSize < 0x40) (noNul : 0 ∉ filename.toUTF8.data)
    (loadable : Loadable filename world)
    (confined : Confined (.starting (Uxn.Host.file filename) world))
    (compatible : CompatibleDevices (.starting (Uxn.Host.file filename) world)) :
    ∀ direct nested, Boundary filename world direct nested →
      Block (Boundary filename world) direct nested := by
  intro direct nested related
  cases related with
  | loading => exact loading_block filename world fits noNul loadable
  | @evaluating guest outer current invocation reachable image =>
    by_cases brk : guest.vm.mem.ram guest.vm.pc = 0
    · exact brk_block confined _ reachable image brk
    · by_cases write : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 0x17
      · exact write_block confined compatible _ reachable image write
      · exact pure_block confined compatible _ reachable image brk write
  | input reachable image directControl outerControl =>
    exact input_block _ reachable image directControl outerControl
  | delivering value kind last reachable image directControl outerControl =>
    exact delivery_block _ value kind last reachable image directControl outerControl
  | stopped directStopped nestedStopped agree =>
    refine ⟨_, .refl, agree, ?_⟩
    rw [directStopped, nestedStopped]
    exact .none

end ProgramProofs.Uxnmin.Model
