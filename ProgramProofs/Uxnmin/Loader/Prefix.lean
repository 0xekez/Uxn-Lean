import ProgramProofs.Uxnmin.Loader.Tactics

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- The filename terminator prepares the file transfer without performing IO. -/
theorem loader_prefix (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index : Byte) (w r : Byte → Byte) (host : Uxn.Host.State)
    (kind : host.read 0x17#8 = 4#8) :
    ∃ final : Uxn.Host.State,
      PureReaches {host with
        vm := machine (Function.update ram 0x13e index) 0x118 ⟨w, 0⟩ ⟨r, 0⟩,
        control := .evaluating (.console .input)} final ∧
      final.control = .evaluating (.console .input) ∧
      final.read 0x0f = host.read 0x0f ∧ final.consoleVector = host.consoleVector ∧
      final.vm.pc = 0x135 ∧
      final.file.name = some 0 ∧ final.file.length = 0xf6a7 ∧ final.file.handle = none ∧
      final.vm.mem.ram = Function.update ram 0x13e index ∧
      final.vm.mem.wstk.ptr = 3 ∧ final.vm.mem.rstk.ptr = 0 ∧
      final.vm.mem.wstk.data 0 = 0x09 ∧ final.vm.mem.wstk.data 1 = 0x59 ∧
      final.vm.mem.wstk.data 2 = 0xac := by
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
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
  host_steps 14 [h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, Function.update_apply, kind]
  refine ⟨_, .refl _, ?_⟩
  simp [host_read, Vector.getElem_set]

end ProgramProofs.Uxnmin.Model
