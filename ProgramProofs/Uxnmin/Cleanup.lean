import ProgramProofs.Uxnmin.Loader.Tactics
import ProgramProofs.Uxnmin.Boundary

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- The reset return selects either the installed guest callback or host completion. -/
theorem reset_cleanup (ram : Word → Byte) (working returning : Uxn.Stack)
    (host : Uxn.Host.State) (code : CodeImage ram)
    (wp : working.ptr = 0) (rp : returning.ptr = 4)
    (loaderFrame : returning.data 0 ++ returning.data 1 = 0x139#16)
    (runFrame : returning.data 2 ++ returning.data 3 = 0x154#16) :
    ∃ final : Uxn.Host.State,
      PureReaches {host with
        vm := machine ram 0x173 working returning, control := .evaluating (.console .input)} final ∧
      final.control = .evaluating (.console .input) ∧ final.vm.pc = 0x139 ∧
      final.vm.mem.ram = ram ∧ final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 ∧
      final.consoleVector = (if ram 0x176 ||| ram 0x175 = 0 then host.consoleVector else 0x174) ∧
      final.read Port.System.state =
        (if ram 0x176 ||| ram 0x175 = 0 then host.read Port.System.state ||| 0x80 else host.read Port.System.state) := by
  have code139 : ram 0x139#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code154 : ram 0x154#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code155 : ram 0x155#16 = 0x01#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code156 : ram 0x156#16 = 0x75#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code157 : ram 0x157#16 = 0x34#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code158 : ram 0x158#16 = 0x1d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code159 : ram 0x159#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code15a : ram 0x15a#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code15b : ram 0x15b#16 = 0x0a#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code15c : ram 0x15c#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code15d : ram 0x15d#16 = 0x0f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code15e : ram 0x15e#16 = 0x16#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code15f : ram 0x15f#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code160 : ram 0x160#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code161 : ram 0x161#16 = 0x1d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code162 : ram 0x162#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code163 : ram 0x163#16 = 0x0f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code164 : ram 0x164#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code165 : ram 0x165#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code166 : ram 0x166#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code167 : ram 0x167#16 = 0x01#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code168 : ram 0x168#16 = 0x74#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code169 : ram 0x169#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code16a : ram 0x16a#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code16b : ram 0x16b#16 = 0x37#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code16c : ram 0x16c#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code173 : ram 0x173#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have highByte (high low : Byte) : ((high ++ low) >>> 8).setWidth 8 = high := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have lowByte (high low : Byte) : (high ++ low).setWidth 8 = low := by
    rw [BitVec.setWidth_append_eq_right]
  simp only [BitVec.ofNat_eq_ofNat] at loaderFrame runFrame
  host_steps 4 [code139, code154, code155, code156, code157, code158, code159, code15a, code15b, code15c, code15d, code15e, code15f, code160, code161, code162, code163, code164, code165, code166, code167, code168, code169, code16a, code16b, code16c, code173, wp, rp, loaderFrame, runFrame, highByte, lowByte]
  by_cases zero : ram 0x176#16 ||| ram 0x175#16 = 0#8
  · host_steps 8 [code139, code154, code155, code156, code157, code158, code159, code15a, code15b, code15c, code15d, code15e, code15f, code160, code161, code162, code163, code164, code165, code166, code167, code168, code169, code16a, code16b, code16c, code173, wp, rp, loaderFrame, runFrame, highByte, lowByte, zero]
    refine ⟨_, .refl _, ?_⟩
    simp [zero, host_read, Uxn.Host.State.write, Vector.getElem_set, Port.System.state]
    try exact BitVec.or_comm _ _
  · host_steps 5 [code139, code154, code155, code156, code157, code158, code159, code15a, code15b, code15c, code15d, code15e, code15f, code160, code161, code162, code163, code164, code165, code166, code167, code168, code169, code16a, code16b, code16c, code173, wp, rp, loaderFrame, runFrame, highByte, lowByte, zero]
    refine ⟨_, .refl _, ?_⟩
    simp [zero, host_read, Uxn.Host.State.write, Vector.getElem_set, Port.System.state]
    try exact BitVec.or_comm _ _

/-- An input callback returns directly to its saved outer BRK. -/
theorem callback_cleanup (ram : Word → Byte) (working returning : Uxn.Stack)
    (host : Uxn.Host.State) (after : Console) (code : CodeImage ram)
    (wp : working.ptr = 0) (rp : returning.ptr = 2)
    (frame : returning.data 0 ++ returning.data 1 = 0x18f#16) :
    ∃ final : Uxn.Host.State,
      PureReaches {host with
        vm := machine ram 0x173 working returning, control := .evaluating (.console after)} final ∧
      final.control = .evaluating (.console after) ∧ final.vm.pc = 0x18f ∧
      final.vm.mem.ram = ram ∧ final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 ∧
      final.consoleVector = host.consoleVector ∧ final.ports = host.ports := by
  have opcode : ram 0x173#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  simp only [BitVec.ofNat_eq_ofNat] at frame
  host_steps 1 [opcode, wp, rp, frame]
  exact ⟨_, .refl _, rfl, rfl, rfl, wp, rfl, rfl, rfl⟩

end ProgramProofs.Uxnmin.Model
