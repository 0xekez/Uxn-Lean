import ProgramProofs.Uxnmin.Loader.Tactics

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- One filename callback copies its byte and returns to the saved argument work. -/
theorem loader_character (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index byte : Byte) (w r : Byte → Byte) (host : Uxn.Host.State) (after : Console)
    (input : host.read 0x12#8 = byte) (kind : host.read 0x17#8 = 2#8) :
    ∃ final : Uxn.Host.State,
      PureReaches {host with
        vm := machine (Function.update ram 0x13e index) 0x118 ⟨w, 0⟩ ⟨r, 0⟩,
        control := .evaluating (.console after)} final ∧
      final.control = .console after ∧ final.vm.pc = 0x145 ∧
      final.ports = host.ports ∧ final.consoleVector = host.consoleVector ∧ final.file = host.file ∧
      final.vm.mem.ram = Function.update (Function.update ram 0x13e (index + 1))
        (index.setWidth 16) byte ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have low : 0x144#16 ≠ index.setWidth 16 := by bv_omega
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  rw [read_eq] at input kind
  simp at input kind
  have h24 : ram 0x118#16 = 0xa0#8 := hc ⟨24, by decide⟩
  have h25 : ram 0x119#16 = 0x3#8 := hc ⟨25, by decide⟩
  have h26 : ram 0x11a#16 = 0x17#8 := hc ⟨26, by decide⟩
  have h27 : ram 0x11b#16 = 0x16#8 := hc ⟨27, by decide⟩
  have h28 : ram 0x11c#16 = 0xa#8 := hc ⟨28, by decide⟩
  have h29 : ram 0x11d#16 = 0x20#8 := hc ⟨29, by decide⟩
  have h30 : ram 0x11e#16 = 0x0#8 := hc ⟨30, by decide⟩
  have h31 : ram 0x11f#16 = 0x1a#8 := hc ⟨31, by decide⟩
  have h58 : ram 0x13a#16 = 0x80#8 := hc ⟨58, by decide⟩
  have h59 : ram 0x13b#16 = 0x12#8 := hc ⟨59, by decide⟩
  have h60 : ram 0x13c#16 = 0x16#8 := hc ⟨60, by decide⟩
  have h61 : ram 0x13d#16 = 0x80#8 := hc ⟨61, by decide⟩
  have h63 : ram 0x13f#16 = 0x81#8 := hc ⟨63, by decide⟩
  have h64 : ram 0x140#16 = 0x80#8 := hc ⟨64, by decide⟩
  have h65 : ram 0x141#16 = 0xfb#8 := hc ⟨65, by decide⟩
  have h66 : ram 0x142#16 = 0x13#8 := hc ⟨66, by decide⟩
  have h67 : ram 0x143#16 = 0x11#8 := hc ⟨67, by decide⟩
  have h68 : ram 0x144#16 = 0x0#8 := hc ⟨68, by decide⟩
  host_steps 12 [h24, h25, h26, h27, h28, h29, h30, h31, h58, h59, h60, h61,
    h63, h64, h65, h66, h67, h68, Function.update_apply, low, input, kind]
  refine ⟨_, .refl _, ?_⟩
  have increment : (index.setWidth 16 + 1#16).setWidth 8 = index + 1#8 := by bv_omega
  simp [Function.update_comm, Function.update_idem, increment]

end ProgramProofs.Uxnmin.Model
