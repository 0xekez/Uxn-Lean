import ProgramProofs.Uxnmin.Semantics
import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO
import Mathlib.Tactic.Conv

set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- After loading, ten native instructions establish the guest evaluation boundary. -/
theorem post_load_boot_continue (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index : Byte) (w r : Byte → Byte) (host : Uxn.Host.State) (fuel : Nat) :
    ∃ vm : Uxn.State, ∃ final : Uxn.Host.State,
      evalLoop (.next (machine (Function.update ram 0x13e index) 0x136 ⟨w, 0⟩ ⟨r, 0⟩))
        { host with fuel := some (fuel + 10) } = evalLoop (.next vm) final ∧
      final.fuel = some fuel ∧ final.read 0x0f = host.read 0x0f ∧ vm.pc = 0x16d ∧ final.consoleVector = 0 ∧
      vm.mem.ram = Function.update (Function.update (Function.update ram 0x13e index) 0x45 1) 0x46 0 ∧
      vm.mem.wstk.ptr = 0 ∧ vm.mem.rstk.ptr = 4 ∧
      vm.mem.rstk.data 0 = 1 ∧ vm.mem.rstk.data 1 = 0x39 ∧
      vm.mem.rstk.data 2 = 1 ∧ vm.mem.rstk.data 3 = 0x54 := by
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  have deo_vector (mem : Memory) (value : Byte) :
      deo mem 0x11#8 value = (do
        modify (·.write 0x11 value)
        modify fun host => { host with consoleVector := host.read 0x10 ++ value }
        return {}) := rfl
  have h54 : ram 0x136#16 = 0x60#8 := hc ⟨54, by decide⟩
  have h55 : ram 0x137#16 = 0x0#8 := hc ⟨55, by decide⟩
  have h56 : ram 0x138#16 = 0xc#8 := hc ⟨56, by decide⟩
  have h69 : ram 0x145#16 = 0xa0#8 := hc ⟨69, by decide⟩
  have h70 : ram 0x146#16 = 0x0#8 := hc ⟨70, by decide⟩
  have h71 : ram 0x147#16 = 0x0#8 := hc ⟨71, by decide⟩
  have h72 : ram 0x148#16 = 0x80#8 := hc ⟨72, by decide⟩
  have h73 : ram 0x149#16 = 0x10#8 := hc ⟨73, by decide⟩
  have h74 : ram 0x14a#16 = 0x37#8 := hc ⟨74, by decide⟩
  have h75 : ram 0x14b#16 = 0xa0#8 := hc ⟨75, by decide⟩
  have h76 : ram 0x14c#16 = 0x1#8 := hc ⟨76, by decide⟩
  have h77 : ram 0x14d#16 = 0x0#8 := hc ⟨77, by decide⟩
  have h78 : ram 0x14e#16 = 0x60#8 := hc ⟨78, by decide⟩
  have h79 : ram 0x14f#16 = 0x1#8 := hc ⟨79, by decide⟩
  have h80 : ram 0x150#16 = 0x37#8 := hc ⟨80, by decide⟩
  have h81 : ram 0x151#16 = 0x60#8 := hc ⟨81, by decide⟩
  have h82 : ram 0x152#16 = 0x0#8 := hc ⟨82, by decide⟩
  have h83 : ram 0x153#16 = 0x19#8 := hc ⟨83, by decide⟩
  have h392 : ram 0x288#16 = 0x80#8 := hc ⟨392, by decide⟩
  have h393 : ram 0x289#16 = 0x45#8 := hc ⟨393, by decide⟩
  have h394 : ram 0x28a#16 = 0x31#8 := hc ⟨394, by decide⟩
  have h395 : ram 0x28b#16 = 0x6c#8 := hc ⟨395, by decide⟩
  iterate 10
    rw [evalLoop.eq_def]
    simp [uxn_state, Uxn.Host.step]
    conv =>
      pattern Uxn.step _
      simp only [machine, Uxn.step, stepM, fetchInstruction, fetchByte,
        StateT.run, Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Pure.pure, StateT.pure]
      simp [h54, h55, h56, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h392, h393, h394, h395, Function.update_apply]
      dsimp [Uxn.Instruction.ofByte]
      simp [uxn_state, uxn_step, h54, h55, h56, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h392, h393, h394, h395, Function.update_apply]
    try dsimp [Request.Result]
    simp [respond, uxn_state]
    try rw [deo_vector]
    try simp [uxn_state, read_eq, Host.State.write, Patch.apply,
      Function.update_apply, BitVec.sub_eq_add_neg, BitVec.add_assoc, Vector.getElem_set]
  refine ⟨_, _, rfl, ?_⟩
  simp [read_eq, Vector.getElem_set]

end ProgramProofs.Uxnmin
