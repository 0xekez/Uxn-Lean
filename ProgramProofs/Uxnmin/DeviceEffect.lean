import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO
import ProgramProofs.Uxnmin.Rom

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- Observable effects of one supported device-byte output. -/
def deviceOutput (port value : Byte) : IO Unit :=
  if port = Port.Console.write then writeStdout value
  else if port = Port.Console.error then (do (← IO.getStderr).write ⟨#[UInt8.ofBitVec value]⟩)
  else pure ()

def deviceHost (host : Uxn.Host.State) (port value : Byte) : Uxn.Host.State :=
  if port = Port.Console.vectorLow then
    { host.write port value with consoleVector := (host.write port value).read Port.Console.vector ++ value }
  else host.write port value

/-- Outside the file devices, the host emits at most one byte and never patches RAM. -/
theorem deo_nonfile (memory : Uxn.Memory) (host : Uxn.Host.State) (port value : Byte)
    (supported : port ∉ Port.File.ports) :
    deo memory port value host = (do deviceOutput port value; pure ({}, deviceHost host port value)) := by
  change ¬(0xa0#8 ≤ port ∧ port < 0xc0#8) at supported
  simp only [deo, state_bind_apply, state_modify_apply, pure_bind]
  split
  all_goals
    simp_all [deviceOutput, deviceHost, uxn_state, writeStdout]

end ProgramProofs.Uxnmin
