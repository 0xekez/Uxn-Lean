import ProgramProofs.Uxnmin.Loader.FileRead

set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private Uxn.Host.fileName Uxn.Host.readFile from Uxn.Host
open private ProgramProofs.Host.io_bind_apply from ProgramProofs.Host.IO

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- The loader's DEO2 reads the file and resumes at the following instruction,
with one fuel unit consumed and the returned bytes installed in guest RAM. -/
theorem file_deo_continue (vm : Uxn.State) (host : Uxn.Host.State)
    (filename : String) (program : ByteArray) (before after : Void IO.RealWorld) (fuel : Nat)
    (pc : vm.pc = 0x135) (instruction : vm.mem.ram 0x135 = 0x37)
    (working : vm.mem.wstk.ptr = 3)
    (high : vm.mem.wstk.data 0 = 0x09) (low : vm.mem.wstk.data 1 = 0x59)
    (port : vm.mem.wstk.data 2 = 0xac)
    (name : host.file.name = some 0) (length : host.file.length = 0xf6a7)
    (handle : host.file.handle = none)
    (decode : Uxn.Host.fileName vm.mem 0 = some filename)
    (read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) before =
      .ok program after) :
    ∃ final : Uxn.Host.State,
      evalLoop (.next vm) { host with fuel := some (fuel + 1) } before =
        evalLoop (.next (({ ramWrites := program.data.toList.zipIdx |>.map fun (byte, i) =>
          (0x0959 + BitVec.ofNat 16 i, byte.toBitVec) } : Patch).apply
          { vm with pc := 0x136, mem.wstk.ptr := 0 })) final after ∧
      final.fuel = some fuel ∧ final.read 0x0f = host.read 0x0f ∧
      final.consoleVector = host.consoleVector ∧ final.vm = host.vm := by
  simp only [BitVec.ofNat_eq_ofNat] at pc instruction working high low port
  have read_eq (state : Uxn.Host.State) (port : Byte) :
      state.read port = state.ports[port.toNat] := rfl
  have deo_read (memory : Memory) (value : Byte) :
      deo memory 0xad#8 value = (do
        modify (·.write 0xad value)
        Uxn.Host.readFile memory) := rfl
  let prepared : Uxn.Host.State := (({ host with fuel := some fuel }).write 0xac 0x09).write 0xad 0x59
  have hostStep : Uxn.Host.step vm = (do
      modify (·.write 0xac 0x09)
      let patch ← deo ({ vm with pc := 0x136, mem.wstk.ptr := 0 } : Uxn.State).mem 0xad 0x59
      pure (.next (patch.apply { vm with pc := 0x136, mem.wstk.ptr := 0 }))) := by
    funext state
    simp [Uxn.Host.step, uxn_state, uxn_step, pc, instruction, working, high, low, port,
      respond, Request.Result]
  obtain ⟨final, loaded, sameVM, sameFuel, sameVector, sameName, sameLength, sameHalt⟩ :=
    file_read_success ({ vm with pc := 0x136, mem.wstk.ptr := 0 } : Uxn.State).mem
      filename program prepared before after
      (by simpa [prepared, Uxn.Host.State.write] using name)
      (by simpa [prepared, Uxn.Host.State.write] using length)
      (by simpa [prepared, Uxn.Host.State.write] using handle)
      (by simp [prepared, Uxn.Host.State.readWord, read_eq,
        Uxn.Host.State.write, Port.File.read, Vector.getElem_set])
      decode read
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · rw [evalLoop.eq_def]
    simp [uxn_state, hostStep, Request.Result]
    rw [deo_read]
    simp [uxn_state, ProgramProofs.Host.io_bind_apply, prepared] at loaded ⊢
    rw [loaded]
  · simpa [prepared, Uxn.Host.State.write] using sameFuel
  · simpa [prepared, Uxn.Host.State.write, read_eq, Vector.getElem_set] using sameHalt
  · simpa [prepared, Uxn.Host.State.write] using sameVector
  · simpa [prepared, Uxn.Host.State.write] using sameVM

end ProgramProofs.Uxnmin
