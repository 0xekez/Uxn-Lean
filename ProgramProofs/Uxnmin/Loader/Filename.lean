import ProgramProofs.Uxnmin.Loader.Character
import ProgramProofs.Uxnmin.Loader.ByteArray

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

private def writeName : List UInt8 → Nat → (Word → Byte) → Word → Byte
  | [], _, ram => ram
  | byte :: bytes, offset, ram =>
      writeName bytes (offset + 1) (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec)

private def argumentStep (byte : UInt8) (_ : PUnit) : StateT Uxn.Host.State IO (ForInStep PUnit) := do
  if (← get).fuel == some 0 || (← get).read Port.System.state != 0 || byte == 0 then
    return .done ()
  run.consoleInput byte.toBitVec 2
  return .yield ()

/-- Delivering argument bytes consumes twelve native instructions per byte. -/
theorem filename_loop (bytes : List UInt8) (offset : Nat) (ram : Word → Byte)
    (hc : Code rom rom.size ram) (host : Uxn.Host.State) (fuel : Nat)
    (fits : offset + bytes.length < 0x40) (noNul : 0 ∉ bytes)
    (vector : host.consoleVector = 0x118)
    (memory : host.vm.mem.ram = Function.update ram 0x13e (BitVec.ofNat 8 offset))
    (working : host.vm.mem.wstk.ptr = 0) (returning : host.vm.mem.rstk.ptr = 0)
    (halt : host.read 0x0f = 0) :
    ∃ final : Uxn.Host.State,
      forIn bytes PUnit.unit argumentStep { host with fuel := some (fuel + 12 * bytes.length) } = pure (PUnit.unit, final) ∧
      final.fuel = some fuel ∧ final.consoleVector = 0x118 ∧ final.read 0x0f = 0 ∧
      final.vm.mem.ram = Function.update (writeName bytes offset ram) 0x13e
        (BitVec.ofNat 8 (offset + bytes.length)) ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  induction bytes generalizing offset ram host fuel with
  | nil =>
    refine ⟨{host with fuel := some fuel}, ?_, rfl, vector, halt, ?_, working, returning⟩
    · simp [List.forIn_nil, uxn_state]
    · simpa [writeName] using memory
  | cons byte bytes ih =>
    have parts : byte ≠ 0 ∧ 0 ∉ bytes := by simpa [eq_comm] using noNul
    have address : (BitVec.ofNat 8 offset).setWidth 16 = BitVec.ofNat 16 offset := by
      have : offset < 0x40 := by simp at fits; omega
      bv_omega
    have distinct : 0x13e#16 ≠ BitVec.ofNat 16 offset := by
      have : offset < 0x40 := by simp at fits; omega
      bv_omega
    have nextIndex : BitVec.ofNat 8 offset + 1 = BitVec.ofNat 8 (offset + 1) := by bv_omega
    obtain ⟨middle, executed, budget, pc, ports, callback, file, ram', wptr, rptr⟩ :=
      console_filename_byte ram hc (BitVec.ofNat 8 offset) byte.toBitVec host
        (fuel + 12 * bytes.length) vector memory working returning
    have code : Code rom rom.size (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec) := by
      intro i
      have different : 0x100 + BitVec.ofNat 16 i.val ≠ BitVec.ofNat 16 offset := by
        have small : offset < 0x40 := by simp at fits; omega
        have bound : i.val < 0x456 := i.isLt
        bv_omega
      rw [Function.update_of_ne different]
      exact hc i
    have middleMemory : middle.vm.mem.ram =
        Function.update (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec) 0x13e
          (BitVec.ofNat 8 (offset + 1)) := by
      rw [ram', address, nextIndex]
      exact Function.update_comm distinct _ _ _
    have middleHalt : middle.read 0x0f = 0 := by
      rw [read_eq, ports]
      simpa [Host.State.write, Vector.getElem_set, read_eq] using halt
    obtain ⟨final, executed', budget', callback', halt', ram'', wptr', rptr'⟩ :=
      ih (offset + 1) (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec)
        code middle fuel (by simp at fits; omega) parts.2 callback middleMemory wptr rptr middleHalt read_eq
    refine ⟨final, ?_, budget', callback', halt', ?_, wptr', rptr'⟩
    · rw [List.forIn_cons]
      have running : host.ports[15] = 0#8 := halt
      simp only [BitVec.ofNat_eq_ofNat, Nat.add_assoc] at executed
      simp [argumentStep, uxn_state, read_eq, running, parts.1, Port.System.state,
        Nat.mul_add, executed]
      rw [← budget] at executed'
      simpa using executed'
    · simpa [writeName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ram''

/-- Argument delivery consists of the verified filename loop followed by its final callback. -/
theorem console_filename (filename : String) (ram : Word → Byte)
    (hc : Code rom rom.size ram) (host : Uxn.Host.State) (fuel : Nat) (positive : 0 < fuel)
    (fits : filename.utf8ByteSize < 0x40) (noNul : 0 ∉ filename.toUTF8.data)
    (vector : host.consoleVector = 0x118)
    (memory : host.vm.mem.ram = Function.update ram 0x13e 0)
    (working : host.vm.mem.wstk.ptr = 0) (returning : host.vm.mem.rstk.ptr = 0)
    (halt : host.read 0x0f = 0) :
    ∃ middle : Uxn.Host.State,
      run.consoleArgs [filename] { host with fuel := some (fuel + 12 * filename.utf8ByteSize) } =
        run.consoleInput 10 4 middle ∧
      middle.fuel = some fuel ∧ middle.consoleVector = 0x118 ∧ middle.read 0x0f = 0 ∧
      middle.vm.mem.ram = Function.update (writeName filename.toUTF8.data.toList 0 ram) 0x13e
        (BitVec.ofNat 8 filename.utf8ByteSize) ∧
      middle.vm.mem.wstk.ptr = 0 ∧ middle.vm.mem.rstk.ptr = 0 := by
  have length : filename.toUTF8.data.toList.length = filename.utf8ByteSize := by
    simp only [Array.length_toList]
    rfl
  obtain ⟨middle, loop, budget, callback, running, ram', wptr, rptr⟩ :=
    filename_loop filename.toUTF8.data.toList 0 ram hc host fuel (by simpa only [Nat.zero_add, length] using fits) (by simpa using noNul)
      vector memory working returning halt
  refine ⟨middle, ?_, budget, callback, running, ?_, wptr, rptr⟩
  ·
    unfold run.consoleArgs
    simp only [ByteArray.forIn_data_toList]
    simp [uxn_state, Nat.ne_of_gt positive, -Array.forIn_toList]
    have loop' := loop
    simp only [length] at loop'
    unfold argumentStep at loop'
    simp [uxn_state, Port.System.state, -Array.forIn_toList] at loop'
    rw [loop']
    simp [uxn_state, run.consoleArgs]
  · simpa only [Nat.zero_add, length] using ram'

end ProgramProofs.Uxnmin
