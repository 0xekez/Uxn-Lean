import ProgramProofs.Uxnmin.Steps
import ProgramProofs.Uxnmin.Loader.FileRead

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private Uxn.Host.fileName Uxn.Host.readFile from Uxn.Host
open private ProgramProofs.Host.io_bind_apply from ProgramProofs.Host.IO
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- The file-device instruction performs the same successful open/read as direct loading. -/
theorem loader_file (host : Uxn.Host.State) (filename : String) (program : ByteArray)
    (before after : Void IO.RealWorld)
    (control : host.control = .evaluating (.console .input))
    (pc : host.vm.pc = 0x135) (instruction : host.vm.mem.ram 0x135 = 0x37)
    (working : host.vm.mem.wstk.ptr = 3)
    (high : host.vm.mem.wstk.data 0 = 0x09) (low : host.vm.mem.wstk.data 1 = 0x59)
    (port : host.vm.mem.wstk.data 2 = 0xac)
    (name : host.file.name = some 0) (length : host.file.length = 0xf6a7)
    (handle : host.file.handle = none)
    (decode : Uxn.Host.fileName host.vm.mem 0 = some filename)
    (read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) before = .ok program after) :
    ∃ final : Uxn.Host.State,
      Configuration.next (.running host before) = some (.running final after) ∧
      final.control = .evaluating (.console .input) ∧ final.read 0x0f = host.read 0x0f ∧
      final.consoleVector = host.consoleVector ∧
      final.vm = ({ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
        (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} : Patch).apply
          {host.vm with pc := 0x136, mem.wstk.ptr := 0} := by
  simp only [BitVec.ofNat_eq_ofNat] at pc instruction working high low port
  have read_eq (state : Uxn.Host.State) (port : Byte) : state.read port = state.ports[port.toNat] := rfl
  have deo_read (memory : Memory) (value : Byte) :
      deo memory 0xad#8 value = (do modify (·.write 0xad value); Uxn.Host.readFile memory) := rfl
  let prepared := (host.write 0xac 0x09).write 0xad 0x59
  have hostStep : Uxn.Host.step host.vm = (do
      modify (·.write 0xac 0x09)
      let patch ← deo ({host.vm with pc := 0x136, mem.wstk.ptr := 0} : Uxn.State).mem 0xad 0x59
      pure (.next (patch.apply {host.vm with pc := 0x136, mem.wstk.ptr := 0}))) := by
    funext state
    simp [Uxn.Host.step, uxn_state, uxn_step, pc, instruction, working, high, low, port, respond, Request.Result]
  obtain ⟨final, loaded, sameVM, sameControl, sameFuel, sameVector, sameName, sameLength, sameHalt⟩ :=
    file_read_success ({host.vm with pc := 0x136, mem.wstk.ptr := 0} : Uxn.State).mem
      filename program prepared before after name length handle
      (by simp [prepared, Uxn.Host.State.readWord, read_eq, Uxn.Host.State.write, Port.File.read, Vector.getElem_set]) decode read
  refine ⟨{final with
    vm := ({ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
    (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} : Patch).apply
      {host.vm with pc := 0x136, mem.wstk.ptr := 0}}, ?_, sameControl.trans control, ?_, sameVector, rfl⟩
  · simp only [Configuration.next, Uxn.Host.State.next, control, hostStep]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [deo_read]
    simp [uxn_state, ProgramProofs.Host.io_bind_apply, prepared] at loaded ⊢
    simp only [← bind_pure_comp, ProgramProofs.Host.io_bind_apply, loaded]
    rfl
  · simpa [prepared, Uxn.Host.State.write, read_eq, Vector.getElem_set] using sameHalt

end ProgramProofs.Uxnmin.Model
