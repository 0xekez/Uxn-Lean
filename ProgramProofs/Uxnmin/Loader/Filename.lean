import ProgramProofs.Uxnmin.Loader.Character
import ProgramProofs.Uxnmin.DeliveryBlock
import ProgramProofs.Uxnmin.Loader.FilenameMemory

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.NameBytes
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem next_argument_byte {host : Uxn.Host.State} (byte : UInt8) (bytes : List UInt8)
    (control : host.control = .console (.argument (byte :: bytes) []))
    (running : host.read Port.System.state = 0) (nonzero : byte ≠ 0) :
    host.next = some (pure {host with control := .delivering byte.toBitVec 2 (.argument bytes [])}) := by
  simp only [Uxn.Host.State.next, control]
  simp [running, nonzero]

theorem filename_loop (bytes : List UInt8) (offset : Nat) (ram : Word → Byte)
    (hc : Code rom rom.size ram) (host : Uxn.Host.State)
    (fits : offset + bytes.length < 0x40) (noNul : 0 ∉ bytes)
    (control : host.control = .console (.argument bytes []))
    (vector : host.consoleVector = 0x118)
    (memory : host.vm.mem.ram = Function.update ram 0x13e (BitVec.ofNat 8 offset))
    (working : host.vm.mem.wstk.ptr = 0) (returning : host.vm.mem.rstk.ptr = 0)
    (halt : host.read 0x0f = 0) :
    ∃ final : Uxn.Host.State, PureReaches host final ∧
      final.control = .console (.argument [] []) ∧
      final.consoleVector = 0x118 ∧ final.read 0x0f = 0 ∧
      final.vm.mem.ram = Function.update (ProgramProofs.Uxnmin.writeName bytes offset ram) 0x13e
        (BitVec.ofNat 8 (offset + bytes.length)) ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  induction bytes generalizing offset ram host with
  | nil => exact ⟨host, .refl _, control, vector, halt, by simpa [ProgramProofs.Uxnmin.writeName] using memory, working, returning⟩
  | cons byte bytes ih =>
    have parts : byte ≠ 0 ∧ 0 ∉ bytes := by simpa [eq_comm] using noNul
    have address : (BitVec.ofNat 8 offset).setWidth 16 = BitVec.ofNat 16 offset := by
      have : offset < 0x40 := by simp at fits; omega
      bv_omega
    have distinct : 0x13e#16 ≠ BitVec.ofNat 16 offset := by
      have : offset < 0x40 := by simp at fits; omega
      bv_omega
    have nextIndex : BitVec.ofNat 8 offset + 1 = BitVec.ofNat 8 (offset + 1) := by bv_omega
    obtain ⟨middle, executed, middleControl, _, ports, callback, _, ram', wptr, rptr⟩ :=
      loader_character ram hc (BitVec.ofNat 8 offset) byte.toBitVec host.vm.mem.wstk.data host.vm.mem.rstk.data
        (deliver host byte.toBitVec 2) (.argument bytes [])
        (by simp [deliver, host_write_read, Port.Console.read, Port.Console.type])
        (by simp [deliver, host_write_read, Port.Console.type])
    have shape : machine (Function.update ram 0x13e (BitVec.ofNat 8 offset)) 0x118
        ⟨host.vm.mem.wstk.data, 0⟩ ⟨host.vm.mem.rstk.data, 0⟩ = {host.vm with pc := host.consoleVector} := by
      rw [← memory, stack_zero _ working, stack_zero _ returning, vector]
      rfl
    rw [shape] at executed
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
      rw [host_read, ports]
      simpa [deliver, Uxn.Host.State.write, Vector.getElem_set, host_read, Port.Console.read, Port.Console.type] using halt
    have middleVector : middle.consoleVector = 0x118 := callback.trans vector
    obtain ⟨final, tail, finalControl, callback', halt', ram'', wptr', rptr'⟩ :=
      ih (offset + 1) (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec) code middle
        (by simp at fits; omega) parts.2 middleControl middleVector middleMemory wptr rptr middleHalt
    refine ⟨final, ?_, finalControl, callback', halt', ?_, wptr', rptr'⟩
    · apply PureReaches.head (next_argument_byte byte bytes control halt parts.1)
      apply PureReaches.head (next_delivery_vector (state := {host with control := .delivering byte.toBitVec 2 (.argument bytes [])}) byte.toBitVec 2 (.argument bytes []) rfl
        (show host.consoleVector ≠ 0 by rw [vector]; decide))
      exact executed.trans tail
    · simpa [ProgramProofs.Uxnmin.writeName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ram''

end ProgramProofs.Uxnmin.Model
