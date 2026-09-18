import ProgramProofs.Uxnmin.DeviceRead
import ProgramProofs.Uxnmin.PushOperand

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Word-mode DEI saves its first device byte while retaining the input port. -/
theorem device_reader_high (ram : Word → Byte) (softwareStack : Word) (pointer port : Byte)
    (working returning : Uxn.Stack)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage ram)
    (high : ram 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : ram 0x41#16 = softwareStack.setWidth 8) (ptr : ram (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 246) (returnSpace : returning.ptr.toNat ≤ 251) :
    ∃ final, Reaches (machine ram 0x33f (Stack.pushWord working (port.setWidth 16)) returning) final ∧
      final.pc = 0x346 ∧ final.mem.wstk.ptr = working.ptr + 2 ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.wstk.data working.ptr = 0 ∧ final.mem.wstk.data (working.ptr + 1) = port ∧
      final.mem.ram = Function.update (Function.update ram (softwareStack + 0x100) (pointer + 1))
        (softwareStack + pointer.setWidth 16)
        (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16)) ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have h33f : ram 0x33f#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h340 : ram 0x340#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h341 : ram 0x341#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h342 : ram 0x342#16 = 0x4d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h343 : ram 0x343#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h344 : ram 0x344#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h345 : ram 0x345#16 = 0x4d#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have header : Reaches (machine ram 0x33f (Stack.pushWord working (port.setWidth 16)) returning)
      (machine ram 0x190 (Stack.push (Stack.pushWord working (port.setWidth 16)) port)
        (Stack.pushWord returning 0x343)) := by
    iterate 2
      apply Reaches.next
      · simp [uxn_state, uxn_step, h33f, h340, h341, h342]
        rfl
    simp [machine, Stack.pushWord, Stack.push, BitVec.add_assoc]
    exact .refl _
  obtain ⟨readVM, readRun, readPC, readRAM, readWP, readValue, readRP, readWF, readRF⟩ :=
    device_read ram code port (Stack.pushWord working (port.setWidth 16)) returning 0x343
      (by simp only [Stack.pushWord, Stack.push]; bv_omega) (by omega)
  have readPointer : readVM.mem.wstk.ptr = working.ptr + 3#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using readWP
  have readValue' : readVM.mem.wstk.data (working.ptr + 2#8) =
      if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16) := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using readValue
  have readEta : Stack.push {readVM.mem.wstk with ptr := working.ptr + 2#8}
      (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16)) = readVM.mem.wstk := by
    have update := Function.update_eq_self (working.ptr + 2#8) readVM.mem.wstk.data
    rw [readValue'] at update
    cases hstack : readVM.mem.wstk
    simp_all [Stack.push, BitVec.add_assoc]
  obtain ⟨final, pushRun, finalPC, finalWP, finalRP, finalRAM, finalWF, finalRF⟩ :=
    push_byte ram softwareStack pointer
      (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16))
      {readVM.mem.wstk with ptr := working.ptr + 2#8} readVM.mem.rstk 0x346 selected code high low ptr
      (by dsimp; bv_omega) (by rw [readRP]; exact returnSpace)
  have call : Uxn.step readVM = .done (.next (machine ram 0x293 readVM.mem.wstk
      (Stack.pushWord readVM.mem.rstk 0x346))) := by
    simp [uxn_state, uxn_step, readPC, readRAM, h343, h344, h345]
  have suffix : Reaches readVM final := by
    apply Reaches.next call
    simpa only [readEta] using pushRun
  refine ⟨final, header.trans (readRun.trans suffix), finalPC, finalWP, finalRP.trans readRP, ?_, ?_, finalRAM, ?_, ?_⟩
  · rw [finalWF _ (by dsimp; bv_omega), readWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
    bv_omega
  · rw [finalWF _ (by dsimp; bv_omega), readWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  · intro index before
    rw [finalWF _ (by dsimp; bv_omega), readWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  · intro index before
    rw [finalRF _ (by rw [readRP]; exact before), readRF _ before]

end ProgramProofs.Uxnmin
