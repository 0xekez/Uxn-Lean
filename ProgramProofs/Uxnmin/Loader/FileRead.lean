import ProgramProofs.Uxnmin.Rom
import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private Uxn.Host.fileName Uxn.Host.readFile from Uxn.Host

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- A successful open/read hypothesis supplies precisely the File device's RAM patch. -/
theorem file_read_success (mem : Memory) (filename : String) (program : ByteArray)
    (host : Uxn.Host.State) (before after : Void IO.RealWorld)
    (name : host.file.name = some 0) (length : host.file.length = 0xf6a7)
    (handle : host.file.handle = none) (destination : host.readWord Port.File.read = 0x0959)
    (decode : Uxn.Host.fileName mem 0 = some filename)
    (read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) before =
      .ok program after) :
    ∃ final : Uxn.Host.State,
      Uxn.Host.readFile mem host before =
        .ok ({ ramWrites := program.data.toList.zipIdx |>.map fun (byte, i) =>
          (0x0959 + BitVec.ofNat 16 i, byte.toBitVec) }, final) after ∧
      final.vm = host.vm ∧ final.control = host.control ∧ final.fuel = host.fuel ∧
      final.consoleVector = host.consoleVector ∧
      final.file.name = some 0 ∧ final.file.length = 0xf6a7 ∧
      final.read 0x0f = host.read 0x0f := by
  have bind_apply {α β} (action : IO α) (cont : α → IO β) (world : Void IO.RealWorld) :
      (action >>= cont) world = match action world with
        | .ok value world' => cont value world'
        | .error error world' => .error error world' := by
    change EST.bind action cont world = _
    exact (EST.bind.eq_def action cont world).trans (by cases action world <;> rfl)
  have pure_apply {α} (value : α) (world : Void IO.RealWorld) :
      (pure value : IO α) world = .ok value world := rfl
  have state_catch {α} (action : StateT Uxn.Host.State IO α)
      (handler : IO.Error → StateT Uxn.Host.State IO α) (state : Uxn.Host.State) :
      (tryCatch action handler) state = tryCatch (action state) (fun e => handler e state) := rfl
  have io_catch {α} (action : IO α) (handler : IO.Error → IO α) (world : Void IO.RealWorld) :
      (tryCatch action handler) world = match action world with
        | .ok value world' => .ok value world'
        | .error error world' => handler error world' := by
    change EST.tryCatch action handler world = _
    exact (EST.tryCatch.eq_def action handler world).trans (by cases action world <;> rfl)
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  change host.ports[172] ++ host.ports[173] = 0x959#16 at destination
  simp only [BitVec.ofNat_eq_ofNat] at name length decode
  cases opened : File.Handle.open filename before with
  | error error world =>
    simp only [bind_apply, opened] at read
    contradiction
  | ok file world =>
    have read' : file.read (ramSize - 0x100).toUSize world = .ok program after := by
      simpa only [bind_apply, opened] using read
    change file.read (USize.ofNat 63143) world = .ok program after at read'
    unfold Uxn.Host.readFile
    simp [uxn_state, name, length, handle, destination, decode, Uxn.Host.State.writeWord,
      Uxn.Host.State.write, Uxn.Host.State.readWord, read_eq,
      Port.File.success, Port.File.read, Port.File.name, Vector.getElem_set,
      state_catch, io_catch, bind_apply, pure_apply, opened, read', ramSize,
      EarlyReturnT.return, EarlyReturn.runK, ExceptT.pure, ExceptT.bind, ExceptT.lift,
      ExceptT.mk, ExceptT.run]
    cases empty : program.isEmpty <;>
      simp [empty, uxn_state, EarlyReturnT.return, throw, MonadExceptOf.throw,
        ExceptT.mk, ExceptT.run, bind_apply, pure_apply, EarlyReturn.runK]
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [read_eq, Vector.getElem_set]

end ProgramProofs.Uxnmin
