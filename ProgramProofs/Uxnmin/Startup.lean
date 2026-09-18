import ProgramProofs.Uxnmin.Loader.Run
import ProgramProofs.Uxnmin.Loader.FilenameMemory

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.Filename
open private Uxn.Host.fileName from Uxn.Host
open private ProgramProofs.Host.io_bind_apply from ProgramProofs.Host.IO

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- The complete host startup loads the file and pauses at the first guest instruction. -/
theorem run_bootstrap (filename : String) (program : ByteArray) (before after : Void IO.RealWorld)
    (filenameFits : filename.utf8ByteSize < 0x40) (noNul : 0 ∉ filename.toUTF8.data)
    (programFits : program.size ≤ ramSize - 0x100)
    (read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) before =
      .ok program after) :
    ∃ input final : Uxn.Host.State,
      Uxn.Host.run rom [filename] (some (32 + 12 * filename.utf8ByteSize)) before = .ok (0, final) after ∧
      input.vm.mem.ram = Function.update
        (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram) 0x13e
        (BitVec.ofNat 8 filename.utf8ByteSize) ∧
      final.fuel = some 0 ∧ final.read 0x0f = 0 ∧
      final.vm.pc = 0x16d ∧ final.consoleVector = 0 ∧
      final.vm.mem.ram = Function.update (Function.update
        (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
          (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} input.vm).mem.ram 0x45 1) 0x46 0 ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 4 ∧
      final.vm.mem.rstk.data 0 = 1 ∧ final.vm.mem.rstk.data 1 = 0x39 ∧
      final.vm.mem.rstk.data 2 = 1 ∧ final.vm.mem.rstk.data 3 = 0x54 := by
  obtain ⟨input, startup, inputFuel, inputVector, inputHalt, inputRAM, inputW, inputR⟩ :=
    run_filename filename filenameFits noNul
  have code : Code rom rom.size (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0
      (initialState rom).vm.mem.ram) :=
    writeName_code filename.toUTF8.data.toList 0 _ (by simpa using filenameFits)
      (Code.initial rom rom.size (by omega) (by decide))
  have zero : (initialState rom).vm.mem.ram (BitVec.ofNat 16 filename.utf8ByteSize) = 0 := by
    rw [initial_ram_eq]
    have small : (BitVec.ofNat 16 filename.utf8ByteSize).toNat < 0x100 := by bv_omega
    rw [if_neg (by omega)]
  have decode : Uxn.Host.fileName input.vm.mem 0 = some filename := by
    have name := (filename_memory filename (initialState rom).vm.mem.ram
      input.vm.mem.wstk input.vm.mem.rstk filenameFits noNul zero).2
    simpa only [Uxn.Host.fileName, inputRAM] using name
  obtain ⟨final, loaded, finalFuel, finalHalt, pc, vector, memory, wptr, rptr, frame0, frame1, frame2, frame3⟩ :=
    console_load (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram)
      code (BitVec.ofNat 8 filename.utf8ByteSize) input filename program before after programFits
      inputVector inputRAM inputW inputR decode read
  have finalHalt' : final.read 0x0f = 0 := finalHalt.trans inputHalt
  refine ⟨input, final, ?_, inputRAM, finalFuel, finalHalt', pc, vector, memory,
    wptr, rptr, frame0, frame1, frame2, frame3⟩
  rw [← inputFuel] at loaded
  rw [startup, ProgramProofs.Host.io_bind_apply, loaded]
  have idle : run.readConsole final = pure ((), final) := by
    rw [run.readConsole.eq_def]
    simp [uxn_state, finalFuel]
  have ignored : run.consoleInput 10 4 final = pure ((), final) := by
    simp [run.consoleInput, uxn_state, finalFuel]
  simp only [BitVec.ofNat_eq_ofNat] at ignored finalHalt'
  simp [idle, ignored, finalHalt', Port.System.state]
  rfl

end ProgramProofs.Uxnmin
