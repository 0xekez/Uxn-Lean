import ProgramProofs.Uxnmin.DeviceRead
import ProgramProofs.Uxnmin.PushOperand

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Byte-mode device input pushes the selected cached port value onto the guest stack. -/
theorem device_reader_byte (ram : Word → Byte) (softwareStack : Word) (pointer port : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage ram)
    (high : ram 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : ram 0x41#16 = softwareStack.setWidth 8)
    (mode : ram 0x44#16 = 0#8) (ptr : ram (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 248) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches (machine ram 0x332 (Stack.pushWord working (port.setWidth 16))
      (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update ram (softwareStack + 0x100) (pointer + 1))
        (softwareStack + pointer.setWidth 16)
        (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16)) ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have asPush (stack : Uxn.Stack) (ptr : Byte) (value : Byte)
      (pointer : stack.ptr = ptr + 1) (top : stack.data ptr = value) :
      Stack.push {stack with ptr} value = stack := by
    have update := Function.update_eq_self ptr stack.data
    rw [top] at update
    cases stack
    simp_all [Stack.push]
  have h332 : ram 0x332#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h333 : ram 0x333#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h334 : ram 0x334#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h335 : ram 0x335#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h336 : ram 0x336#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h337 : ram 0x337#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h338 : ram 0x338#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h339 : ram 0x339#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h33a : ram 0x33a#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h33b : ram 0x33b#16 = 0x54#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h33c : ram 0x33c#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h33d : ram 0x33d#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h33e : ram 0x33e#16 = 0x54#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have header : ∃ middle, Reaches (machine ram 0x332 (Stack.pushWord working (port.setWidth 16))
      (Stack.pushWord returning returnAddress)) middle ∧ middle.pc = 0x190 ∧
      middle.mem.ram = ram ∧ middle.mem.wstk.ptr = working.ptr + 1 ∧
      middle.mem.wstk.data working.ptr = port ∧
      middle.mem.rstk = Stack.pushWord (Stack.pushWord returning returnAddress) 0x33c ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → middle.mem.wstk.data index = working.data index) := by
    iterate 5
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, h332, h333, h334, h335, h336, h337, h338, h339, h33a, h33b, mode]
        rfl
    refine ⟨_, .refl _, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp
    · simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  obtain ⟨middle, before, middlePC, middleRAM, middleWP, middleValue, middleRS, middleWF⟩ := header
  have middleShape : middle = machine ram 0x190
      (Stack.push {middle.mem.wstk with ptr := working.ptr} port)
      (Stack.pushWord (Stack.pushWord returning returnAddress) 0x33c) := by
    rw [asPush _ _ _ middleWP middleValue, ← middleRS, ← middleRAM, ← middlePC]
    rfl
  obtain ⟨readVM, readRun, readPC, readRAM, readWP, readValue, readRP, readWF, readRF⟩ :=
    device_read ram code port {middle.mem.wstk with ptr := working.ptr}
      (Stack.pushWord returning returnAddress) 0x33c (by dsimp; omega)
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have readEta : Stack.push {readVM.mem.wstk with ptr := working.ptr}
      (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16)) = readVM.mem.wstk :=
    asPush _ _ _ readWP readValue
  have readPointer : readVM.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using readRP
  have frameHigh : readVM.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [readRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have frameLow : readVM.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [readRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnEta : Stack.pushWord {readVM.mem.rstk with ptr := returning.ptr} returnAddress = readVM.mem.rstk := by
    simpa [readPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, frameHigh, frameLow, append_split]
      using Stack.asPushWord readVM.mem.rstk
  obtain ⟨final, pushRun, finalPC, finalWP, finalRP, finalRAM, finalWF, finalRF⟩ :=
    push_byte ram softwareStack pointer
      (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16))
      {readVM.mem.wstk with ptr := working.ptr} {readVM.mem.rstk with ptr := returning.ptr} returnAddress
      selected code high low ptr workingSpace (by dsimp; omega)
  have jump : Uxn.step readVM = .done (.next {readVM with pc := 0x293}) := by
    simp [uxn_state, uxn_step, readPC, readRAM, h33c, h33d, h33e]
  have suffix : Reaches readVM final := by
    apply Reaches.next jump
    change Reaches (machine readVM.mem.ram 0x293 readVM.mem.wstk readVM.mem.rstk) final
    rw [readRAM]
    simpa only [readEta, returnEta] using pushRun
  refine ⟨final, before.trans ?_, finalPC, finalWP, finalRP, finalRAM, ?_, ?_⟩
  · rw [middleShape]
    exact readRun.trans suffix
  · intro index below
    rw [finalWF _ below, readWF _ below, middleWF _ below]
  · intro index below
    rw [finalRF _ below, readRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
