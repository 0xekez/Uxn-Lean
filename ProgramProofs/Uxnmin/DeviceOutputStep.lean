import ProgramProofs.Uxnmin.DeviceEffect

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- A native DEO executes the same host action as the guest byte write. -/
theorem device_output_step (ram : Word → Byte) (pc : Word) (code : ram pc = 0x17)
    (port value : Byte) (working returning : Uxn.Stack) (host : Uxn.Host.State)
    (supported : port ∉ Port.File.ports) :
    Uxn.Host.step (machine ram pc (Stack.push (Stack.push working value) port) returning) host =
      (do deviceOutput port value
          pure (.next (machine ram (pc + 1)
            {Stack.push (Stack.push working value) port with ptr := working.ptr} returning),
            deviceHost host port value)) := by
  simp [Uxn.Host.step, uxn_state, uxn_step, code, respond, Request.Result]
  rw [deo_nonfile _ _ _ _ supported]
  simp [uxn_state, Patch.apply]

/-- A write helper's final return preserves native RAM and both active frames. -/
theorem device_output_return (ram : Word → Byte) (pc : Word) (code : ram pc = 0x6c)
    (working returning : Uxn.Stack) (returnAddress : Word) :
    Uxn.step (machine ram pc working (Stack.pushWord returning returnAddress)) =
      .done (.next (machine ram returnAddress working
        {Stack.pushWord returning returnAddress with ptr := returning.ptr})) := by
  simp [uxn_state, uxn_step, code]

end ProgramProofs.Uxnmin
