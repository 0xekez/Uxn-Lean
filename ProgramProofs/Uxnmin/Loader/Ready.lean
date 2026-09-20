import ProgramProofs.Uxnmin.Loader.Reset
import ProgramProofs.Uxnmin.Loader.Filename
import ProgramProofs.Uxnmin.Loader.Prefix

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.NameBytes
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Startup and filename delivery form a finite pure path to the real file action. -/
theorem loader_ready (filename : String) (fits : filename.utf8ByteSize < 0x40)
    (noNul : 0 ∉ filename.toUTF8.data) :
    ∃ ready : Uxn.Host.State,
      PureReaches (initialState rom [filename]) ready ∧
      ready.control = .evaluating (.console .input) ∧ ready.read 0x0f = 0 ∧
      ready.vm.pc = 0x135 ∧ ready.file.name = some 0 ∧ ready.file.length = 0xf6a7 ∧ ready.file.handle = none ∧
      ready.vm.mem.ram = Function.update
        (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram)
        0x13e (BitVec.ofNat 8 filename.utf8ByteSize) ∧
      ready.vm.mem.wstk.ptr = 3 ∧ ready.vm.mem.rstk.ptr = 0 ∧
      ready.vm.mem.wstk.data 0 = 0x09 ∧ ready.vm.mem.wstk.data 1 = 0x59 ∧ ready.vm.mem.wstk.data 2 = 0xac := by
  have code := Code.initial rom rom.size (Nat.le_refl _) (by decide)
  have length : filename.toUTF8.data.toList.length = filename.utf8ByteSize := rfl
  obtain ⟨reset, resetRun, resetControl, resetVector, resetHalt, _, resetRAM, resetWP, resetRP⟩ :=
    loader_reset (initialState rom).vm.mem.ram code filename
  have restore (ram : Word → Byte) (code : Code rom rom.size ram) : ram = Function.update ram 0x13e 0 := by
    have cursor : ram 0x13e = 0 := code ⟨62, by decide⟩
    rw [← cursor]
    simp
  have resetMemory := resetRAM.trans (restore _ code)
  obtain ⟨input, filenameRun, inputControl, inputVector, inputHalt, inputRAM, inputWP, inputRP⟩ :=
    filename_loop filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram code reset
      (by simpa only [Nat.zero_add, length] using fits) (by simpa using noNul)
      resetControl resetVector resetMemory resetWP resetRP resetHalt
  simp only [Nat.zero_add, length] at inputRAM
  obtain ⟨ready, prefixRun, control, halt, _, pc, name, fileLength, handle, memory, wp, rp, high, low, port⟩ :=
    loader_prefix (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram)
      (writeName_code _ _ _ (by simpa only [Nat.zero_add, length] using fits) code)
      (BitVec.ofNat 8 filename.utf8ByteSize) input.vm.mem.wstk.data input.vm.mem.rstk.data
      (deliver input 10 4) (by simp [deliver, host_write_read, Port.Console.type])
  have inputShape : machine
      (Function.update (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram)
        0x13e (BitVec.ofNat 8 filename.utf8ByteSize)) 0x118
      ⟨input.vm.mem.wstk.data, 0⟩ ⟨input.vm.mem.rstk.data, 0⟩ = {input.vm with pc := input.consoleVector} := by
    rw [← inputRAM, stack_zero _ inputWP, stack_zero _ inputRP, inputVector]
    rfl
  rw [inputShape] at prefixRun
  refine ⟨ready, ?_, control, ?_, pc, name, fileLength, handle, memory, wp, rp, high, low, port⟩
  · have initialShape (program : ByteArray) : initialState program [filename] =
        {vm := machine (initialState program).vm.mem.ram 0x100 Stack.empty Stack.empty,
          control := .evaluating (.arguments [filename]), ports := (Vector.replicate 256 0).set 0x17 1} := by
      dsimp only [initialState, Uxn.Host.State.write, machine, Stack.empty]
      rfl
    rw [initialShape]
    apply resetRun.trans (filenameRun.trans _)
    apply PureReaches.head (middle := {input with control := .delivering 10 4 .input})
    · simp [Uxn.Host.State.next, inputControl, Console.arguments]
    · apply PureReaches.head (next_delivery_vector
        (state := {input with control := .delivering 10 4 .input}) 10 4 .input rfl
        (show input.consoleVector ≠ 0 by rw [inputVector]; decide))
      exact prefixRun
  · have halt' : ready.read 0x0f = input.read 0x0f := by
      simpa [deliver, host_write_read, Port.Console.type, Port.Console.read] using halt
    exact halt'.trans inputHalt

end ProgramProofs.Uxnmin.Model
