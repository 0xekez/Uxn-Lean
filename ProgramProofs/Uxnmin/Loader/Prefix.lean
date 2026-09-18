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

/-- The argument terminator prepares File/name, File/length, and the destination. -/
theorem load_prefix_continue (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index : Byte) (w r : Byte → Byte) (host : Uxn.Host.State) (fuel : Nat)
    (kind : host.read 0x17#8 = 4#8) :
    ∃ vm : Uxn.State, ∃ final : Uxn.Host.State,
      evalLoop (.next (machine (Function.update ram 0x13e index) 0x118 ⟨w, 0⟩ ⟨r, 0⟩))
        { host with fuel := some (fuel + 14) } = evalLoop (.next vm) final ∧
      final.fuel = some fuel ∧ final.read 0x0f = host.read 0x0f ∧ vm.pc = 0x135 ∧
      final.file.name = some 0 ∧ final.file.length = 0xf6a7 ∧ final.file.handle = none ∧
      vm.mem.ram = Function.update ram 0x13e index ∧
      vm.mem.wstk.ptr = 3 ∧ vm.mem.rstk.ptr = 0 ∧
      vm.mem.wstk.data 0 = 0x09 ∧ vm.mem.wstk.data 1 = 0x59 ∧
      vm.mem.wstk.data 2 = 0xac := by
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  have deo_name (mem : Memory) (value : Byte) :
      deo mem 0xa9#8 value = (do
        modify (·.write 0xa9 value)
        modify fun host => { host.writeWord Port.File.success 0 with
          file := { host.file with name := some (host.readWord Port.File.name), handle := none } }
        return {}) := rfl
  have deo_length (mem : Memory) (value : Byte) :
      deo mem 0xab#8 value = (do
        modify (·.write 0xab value)
        modify fun host => { host with file.length := host.readWord Port.File.length }
        return {}) := rfl
  rw [read_eq] at kind
  simp at kind
  have h24 : ram 0x118#16 = 0xa0#8 := hc ⟨24, by decide⟩
  have h25 : ram 0x119#16 = 0x3#8 := hc ⟨25, by decide⟩
  have h26 : ram 0x11a#16 = 0x17#8 := hc ⟨26, by decide⟩
  have h27 : ram 0x11b#16 = 0x16#8 := hc ⟨27, by decide⟩
  have h28 : ram 0x11c#16 = 0xa#8 := hc ⟨28, by decide⟩
  have h29 : ram 0x11d#16 = 0x20#8 := hc ⟨29, by decide⟩
  have h30 : ram 0x11e#16 = 0x0#8 := hc ⟨30, by decide⟩
  have h31 : ram 0x11f#16 = 0x1a#8 := hc ⟨31, by decide⟩
  have h32 : ram 0x120#16 = 0xa0#8 := hc ⟨32, by decide⟩
  have h33 : ram 0x121#16 = 0x0#8 := hc ⟨33, by decide⟩
  have h34 : ram 0x122#16 = 0x0#8 := hc ⟨34, by decide⟩
  have h35 : ram 0x123#16 = 0x80#8 := hc ⟨35, by decide⟩
  have h36 : ram 0x124#16 = 0xa8#8 := hc ⟨36, by decide⟩
  have h37 : ram 0x125#16 = 0x37#8 := hc ⟨37, by decide⟩
  have h38 : ram 0x126#16 = 0xa0#8 := hc ⟨38, by decide⟩
  have h39 : ram 0x127#16 = 0x0#8 := hc ⟨39, by decide⟩
  have h40 : ram 0x128#16 = 0x0#8 := hc ⟨40, by decide⟩
  have h41 : ram 0x129#16 = 0xa0#8 := hc ⟨41, by decide⟩
  have h42 : ram 0x12a#16 = 0x9#8 := hc ⟨42, by decide⟩
  have h43 : ram 0x12b#16 = 0x59#8 := hc ⟨43, by decide⟩
  have h44 : ram 0x12c#16 = 0x39#8 := hc ⟨44, by decide⟩
  have h45 : ram 0x12d#16 = 0x80#8 := hc ⟨45, by decide⟩
  have h46 : ram 0x12e#16 = 0xaa#8 := hc ⟨46, by decide⟩
  have h47 : ram 0x12f#16 = 0x37#8 := hc ⟨47, by decide⟩
  have h48 : ram 0x130#16 = 0xa0#8 := hc ⟨48, by decide⟩
  have h49 : ram 0x131#16 = 0x9#8 := hc ⟨49, by decide⟩
  have h50 : ram 0x132#16 = 0x59#8 := hc ⟨50, by decide⟩
  have h51 : ram 0x133#16 = 0x80#8 := hc ⟨51, by decide⟩
  have h52 : ram 0x134#16 = 0xac#8 := hc ⟨52, by decide⟩
  iterate 14
    rw [evalLoop.eq_def]
    simp [uxn_state, Uxn.Host.step]
    conv =>
      pattern Uxn.step _
      simp only [machine, Uxn.step, stepM, fetchInstruction, fetchByte,
        StateT.run, Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Pure.pure, StateT.pure]
      simp [h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, Function.update_apply]
      dsimp [Uxn.Instruction.ofByte]
      simp [uxn_state, uxn_step, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, Function.update_apply, kind]
    try dsimp [Request.Result]
    simp [respond, uxn_state]
    try rw [deo_name]
    try rw [deo_length]
    try simp [uxn_state, read_eq, kind, Host.State.write, Host.State.readWord, Host.State.writeWord,
      Patch.apply, Function.update_apply, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      Port.File.success, Port.File.name, Port.File.length, Vector.getElem_set]
  refine ⟨_, _, rfl, ?_⟩
  simp [read_eq, Vector.getElem_set]

end ProgramProofs.Uxnmin
