import ProgramProofs.Uxnmin.Steps
import Mathlib.Tactic.Conv

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem host_read (host : Uxn.Host.State) (port : Byte) :
    host.read port = host.ports[port.toNat] := rfl

macro "host_steps" count:num "[" facts:term,* "]" : tactic => `(tactic|
  iterate $count
    apply PureReaches.prepend
    · simp only [Uxn.Host.State.next, Uxn.Host.step]
      conv =>
        pattern Uxn.step _
        simp [uxn_state, uxn_step, $[$facts:term],*]
      simp [respond, deo, uxn_state, host_read,
        Uxn.Host.State.write, Uxn.Host.State.readWord, Uxn.Host.State.writeWord,
        Vector.getElem_set, Patch.apply,
        Port.Console.vector, Port.Console.vectorLow, Port.Console.read, Port.Console.type,
        Port.File.name, Port.File.length, Port.File.nameLow, Port.File.lengthLow,
        Port.File.success, $[$facts:term],*]
      try rfl)

end ProgramProofs.Uxnmin.Model
