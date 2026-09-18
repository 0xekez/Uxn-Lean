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

/-- The reset block installs the filename callback without performing IO. -/
theorem reset_prefix (ram : Word → Byte) (hc : Code rom rom.size ram) (fuel : Nat) :
    ∃ final : Uxn.Host.State,
      evalLoop (.next (machine ram 0x100 Stack.empty Stack.empty))
        { vm := machine ram 0x100 Stack.empty Stack.empty,
          ports := (Vector.replicate 256 0).set 0x17 1, fuel := some (fuel + 7) } = pure ((), final) ∧
      final.consoleVector = 0x118 ∧ final.fuel = some fuel ∧ final.read 0x0f = 0 ∧
      final.vm.pc = 0x118 ∧ final.vm.mem.ram = ram ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have deo_vector (mem : Memory) (value : Byte) :
      deo mem 0x11#8 value = (do
        modify (·.write 0x11 value)
        modify fun host => { host with consoleVector := host.read 0x10 ++ value }
        return {}) := rfl
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
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
  iterate 7
    rw [evalLoop.eq_def]
    simp [uxn_state, Uxn.Host.step]
    conv =>
      pattern Uxn.step _
      simp only [machine, Uxn.step, stepM, fetchInstruction, fetchByte,
        StateT.run, Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Pure.pure, StateT.pure, h0, h1, h2, h3, h4, h5, h17, h18, h19, h20, h21, h22, h23]
      dsimp [Uxn.Instruction.ofByte]
      simp [uxn_state, uxn_step, h0, h1, h2, h3, h4, h5, h17, h18, h19, h20, h21, h22, h23]
    try dsimp [Request.Result]
    simp [respond, uxn_state]
    try rw [deo_vector]
    try simp (disch := decide) [uxn_state, read_eq, Host.State.write,
      Patch.apply, Function.update_apply, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      Vector.getElem_set]
  rw [evalLoop.eq_def]
  simp only [uxn_state]
  refine ⟨_, rfl, ?_⟩
  simp [read_eq, Vector.getElem_set]

/-- Pausing after reset performs no IO and leaves the filename callback installed. -/
theorem run_reset (filename : String) :
    ∃ final : Uxn.Host.State,
      Uxn.Host.run rom [filename] (some 7) = pure (0, final) ∧
      final.consoleVector = 0x118 ∧ final.fuel = some 0 ∧
      final.vm.pc = 0x118 ∧ final.vm.mem.ram = (initialState rom).vm.mem.ram ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  obtain ⟨final, run, vector, fuel, state, pc, memory, wstk, rstk⟩ :=
    reset_prefix (initialState rom).vm.mem.ram (Code.initial rom rom.size (by omega) (by decide)) 0
  refine ⟨final, ?_, vector, fuel, pc, memory, wstk, rstk⟩
  unfold Uxn.Host.run
  rw [← initial_shape rom] at run ⊢
  simp [machine, uxn_state, Uxn.Host.State.write] at run ⊢
  rw [run]
  simp only [BitVec.ofNat_eq_ofNat] at state
  simp [fuel, uxn_state, state]

end ProgramProofs.Uxnmin
