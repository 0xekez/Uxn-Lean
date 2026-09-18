import ProgramProofs.Uxnmin.DeviceReaderWordStages
import ProgramProofs.Uxnmin.DeviceReaderLow

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Word-mode device input pushes the cached first byte and the next shadow byte. -/
theorem device_reader_word (ram : Word → Byte) (softwareStack : Word) (pointer port : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage ram)
    (high : ram 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : ram 0x41#16 = softwareStack.setWidth 8)
    (mode : ram 0x44#16 = 1#8) (ptr : ram (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 246) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches (machine ram 0x332 (Stack.pushWord working (port.setWidth 16))
      (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update
        (Function.update (Function.update ram (softwareStack + 0x100) (pointer + 1))
          (softwareStack + pointer.setWidth 16)
          (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16)))
        (softwareStack + 0x100) (pointer + 2))
        (softwareStack + (pointer + 1).setWidth 16) (ram (0x759 + (port + 1).setWidth 16)) ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
  have padHigh : (port.setWidth 16 >>> 8).setWidth 8 = 0#8 := by bv_omega
  have joined (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by simpa using (join_bytes 0#8 byte).symm
  have h332 : ram 0x332#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h333 : ram 0x333#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h334 : ram 0x334#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h335 : ram 0x335#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h336 : ram 0x336#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h337 : ram 0x337#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have header : ∃ middle, Reaches (machine ram 0x332 (Stack.pushWord working (port.setWidth 16))
      (Stack.pushWord returning returnAddress)) middle ∧ middle.pc = 0x33f ∧ middle.mem.ram = ram ∧
      middle.mem.wstk.ptr = working.ptr + 2 ∧ middle.mem.wstk.data working.ptr = 0 ∧
      middle.mem.wstk.data (working.ptr + 1) = port ∧ middle.mem.rstk = Stack.pushWord returning returnAddress ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → middle.mem.wstk.data index = working.data index) := by
    iterate 3
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, h332, h333, h334, h335, h336, h337, mode]
        rfl
    refine ⟨_, .refl _, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [padHigh]
    · simp
    · simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
    · intro index before
      simp (disch := bv_omega) only [Function.update_of_ne]
  obtain ⟨middle, before, middlePC, middleRAM, middleWP, middleHigh, middleLow, middleRS, middleWF⟩ := header
  simp only [BitVec.ofNat_eq_ofNat] at middleWP middleHigh middleLow
  have middleEta : Stack.pushWord {middle.mem.wstk with ptr := working.ptr} (port.setWidth 16) = middle.mem.wstk := by
    simpa [middleWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, middleHigh, middleLow, joined]
      using Stack.asPushWord middle.mem.wstk
  obtain ⟨first, firstRun, firstPC, firstWP, firstRP, firstHigh, firstLow, firstRAM, firstWF, firstRF⟩ :=
    device_reader_high ram softwareStack pointer port {middle.mem.wstk with ptr := working.ptr}
      (Stack.pushWord returning returnAddress) selected code high low ptr workingSpace
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have firstPrefix : Reaches middle first := by
    have shape : middle = machine middle.mem.ram middle.pc middle.mem.wstk middle.mem.rstk := rfl
    rw [middleRAM, middlePC] at shape
    rw [shape, middleRS]
    simpa only [middleEta] using firstRun
  have firstCode : CodeImage first.mem.ram := by
    rw [firstRAM]
    exact (code.write _ _ (.inr (.inl (by bv_omega)))).write _ _ (.inr (.inl (by bv_omega)))
  have unchanged (address : Word) (available : address.toNat < 0x555 ∨ 0x759 ≤ address.toNat) :
      first.mem.ram address = ram address := by
    rw [firstRAM]
    simp (disch := rcases available with before | after <;> bv_omega) only [Function.update_of_ne]
  have firstPointer : first.mem.ram (softwareStack + 0x100#16) = pointer + 1#8 := by
    rw [firstRAM]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [Function.update_of_ne (by bv_omega), Function.update_self]
  simp only [BitVec.ofNat_eq_ofNat] at firstWP firstHigh firstLow
  have firstEta : Stack.pushWord {first.mem.wstk with ptr := working.ptr} (port.setWidth 16) = first.mem.wstk := by
    simpa [firstWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, firstHigh, firstLow, joined]
      using Stack.asPushWord first.mem.wstk
  obtain ⟨second, secondRun, secondPC, secondRAM, secondRS, secondWP, secondValue, secondWF⟩ :=
    device_reader_low first.mem.ram firstCode port {first.mem.wstk with ptr := working.ptr} first.mem.rstk (by dsimp; omega)
  have continuation : Reaches first second := by
    have shape : first = machine first.mem.ram first.pc first.mem.wstk first.mem.rstk := rfl
    rw [firstPC] at shape
    rw [shape]
    simpa only [firstEta] using secondRun
  have secondValue' : second.mem.wstk.data working.ptr = ram (0x759 + (port + 1).setWidth 16) := by
    rw [secondValue, unchanged _ (.inr (by bv_omega))]
  have secondEta : Stack.push {second.mem.wstk with ptr := working.ptr}
      (ram (0x759 + (port + 1).setWidth 16)) = second.mem.wstk := by
    have update := Function.update_eq_self working.ptr second.mem.wstk.data
    rw [secondValue'] at update
    cases hstack : second.mem.wstk
    simp_all [Stack.push]
  have returnPointer : second.mem.rstk.ptr = returning.ptr + 2#8 := by
    rw [secondRS, firstRP]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have frameHigh : second.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [secondRS, firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have frameLow : second.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [secondRS, firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnEta : Stack.pushWord {second.mem.rstk with ptr := returning.ptr} returnAddress = second.mem.rstk := by
    simpa [returnPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, frameHigh, frameLow, append_split]
      using Stack.asPushWord second.mem.rstk
  obtain ⟨final, pushRun, finalPC, finalWP, finalRP, finalRAM, finalWF, finalRF⟩ :=
    push_byte first.mem.ram softwareStack (pointer + 1) (ram (0x759 + (port + 1).setWidth 16))
      {second.mem.wstk with ptr := working.ptr} {second.mem.rstk with ptr := returning.ptr} returnAddress selected firstCode
      (by rw [unchanged _ (.inl (by decide))]; exact high)
      (by rw [unchanged _ (.inl (by decide))]; exact low) firstPointer (by dsimp; omega) (by dsimp; omega)
  have suffix : Reaches second final := by
    have shape : second = machine second.mem.ram second.pc second.mem.wstk second.mem.rstk := rfl
    rw [secondRAM, secondPC] at shape
    rw [shape]
    simpa only [secondEta, returnEta] using pushRun
  refine ⟨final, before.trans (firstPrefix.trans (continuation.trans suffix)), finalPC, finalWP, finalRP, ?_, ?_, ?_⟩
  · rw [finalRAM, firstRAM]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  · intro index before
    rw [finalWF _ before, secondWF _ before, firstWF _ before, middleWF _ before]
  · intro index before
    rw [finalRF _ before, secondRS, firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
