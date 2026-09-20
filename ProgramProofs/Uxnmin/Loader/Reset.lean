import ProgramProofs.Uxnmin.Loader.Tactics

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Reset installs the filename callback and enters argument delivery. -/
theorem loader_reset (ram : Word → Byte) (hc : Code rom rom.size ram) (filename : String) :
    ∃ final : Uxn.Host.State,
      PureReaches
        { vm := machine ram 0x100 Stack.empty Stack.empty,
          control := .evaluating (.arguments [filename]),
          ports := (Vector.replicate 256 0).set 0x17 1 } final ∧
      final.control = .console (.argument filename.toUTF8.data.toList []) ∧
      final.consoleVector = 0x118 ∧ final.read 0x0f = 0 ∧
      final.vm.pc = 0x118 ∧ final.vm.mem.ram = ram ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have h0 : ram 0x100#16 = 0x80#8 := hc ⟨0, by decide⟩
  have h1 : ram 0x101#16 = 0x17#8 := hc ⟨1, by decide⟩
  have h2 : ram 0x102#16 = 0x16#8 := hc ⟨2, by decide⟩
  have h3 : ram 0x103#16 = 0x20#8 := hc ⟨3, by decide⟩
  have h4 : ram 0x104#16 = 0x0#8 := hc ⟨4, by decide⟩
  have h5 : ram 0x105#16 = 0xb#8 := hc ⟨5, by decide⟩
  have h17 : ram 0x111#16 = 0xa0#8 := hc ⟨17, by decide⟩
  have h18 : ram 0x112#16 = 0x1#8 := hc ⟨18, by decide⟩
  have h19 : ram 0x113#16 = 0x18#8 := hc ⟨19, by decide⟩
  have h20 : ram 0x114#16 = 0x80#8 := hc ⟨20, by decide⟩
  have h21 : ram 0x115#16 = 0x10#8 := hc ⟨21, by decide⟩
  have h22 : ram 0x116#16 = 0x37#8 := hc ⟨22, by decide⟩
  have h23 : ram 0x117#16 = 0x0#8 := hc ⟨23, by decide⟩
  host_steps 7 [h0, h1, h2, h3, h4, h5, h17, h18, h19, h20, h21, h22, h23]
  refine ⟨_, .refl _, ?_⟩
  simp [Console.arguments, host_read, Vector.getElem_set]

end ProgramProofs.Uxnmin.Model
