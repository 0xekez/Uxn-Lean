import ProgramProofs.Uxnmin.Loader.Reset
import ProgramProofs.Uxnmin.Loader.Filename
import ProgramProofs.Uxnmin.Loader.Callback
import Mathlib.Tactic.Conv

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.Filename
open private Uxn.Host.fileName from Uxn.Host
open private ProgramProofs.Host.io_bind_apply from ProgramProofs.Host.IO

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- Startup reduces to the final filename callback with the complete input in zero page. -/
theorem run_filename (filename : String) (fits : filename.utf8ByteSize < 0x40)
    (noNul : 0 ∉ filename.toUTF8.data) :
    ∃ middle : Uxn.Host.State,
      Uxn.Host.run rom [filename] (some (32 + 12 * filename.utf8ByteSize)) = (do
        let (_, final) ← run.consoleInput 10 4 middle
        let (_, final) ← run.readConsole final
        let (_, final) ← run.consoleInput 10 4 final
        pure (((final.read Port.System.state &&& 0x7f).toNat.toUInt32), final)) ∧
      middle.fuel = some 25 ∧ middle.consoleVector = 0x118 ∧ middle.read 0x0f = 0 ∧
      middle.vm.mem.ram = Function.update
        (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram) 0x13e
        (BitVec.ofNat 8 filename.utf8ByteSize) ∧
      middle.vm.mem.wstk.ptr = 0 ∧ middle.vm.mem.rstk.ptr = 0 := by
  have hc : Code rom rom.size (initialState rom).vm.mem.ram :=
    Code.initial rom rom.size (by omega) (by decide)
  obtain ⟨reset, resetRun, resetVector, resetFuel, resetHalt, resetPC, resetRAM, resetW, resetR⟩ :=
    reset_prefix (initialState rom).vm.mem.ram hc (25 + 12 * filename.utf8ByteSize)
  have codeCursor (ram : Word → Byte) (code : Code rom rom.size ram) : ram 0x13e = 0 :=
    code ⟨62, by decide⟩
  have cursor := codeCursor (initialState rom).vm.mem.ram hc
  have resetRAM' : reset.vm.mem.ram = Function.update (initialState rom).vm.mem.ram 0x13e 0 := by
    have updated := Function.update_eq_self 0x13e (initialState rom).vm.mem.ram
    rw [cursor] at updated
    exact resetRAM.trans updated.symm
  obtain ⟨middle, filenameRun, fuel, vector, halt, memory, wptr, rptr⟩ :=
    console_filename filename (initialState rom).vm.mem.ram hc reset 25 (by decide)
      fits noNul resetVector resetRAM' resetW resetR resetHalt
  refine ⟨middle, ?_, fuel, vector, halt, memory, wptr, rptr⟩
  rw [← resetFuel] at filenameRun
  have fuelOrder : (25 + 12 * filename.utf8ByteSize) + 7 = 32 + 12 * filename.utf8ByteSize := by omega
  rw [fuelOrder] at resetRun
  unfold Uxn.Host.run
  rw [← initial_shape rom] at resetRun ⊢
  simp [machine, uxn_state, Uxn.Host.State.write] at resetRun ⊢
  rw [resetRun]
  simp [uxn_state, resetFuel, resetVector]
  rw [filenameRun]
  simp [uxn_state]

end ProgramProofs.Uxnmin
