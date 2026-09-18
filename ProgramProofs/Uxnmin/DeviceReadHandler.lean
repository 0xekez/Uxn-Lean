import ProgramProofs.Uxnmin.DeviceReaderByte
import ProgramProofs.Uxnmin.OperandPair

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The native byte-mode DEI handler pops its port and pushes the corresponding device byte. -/
theorem handler_device_read_byte (ram : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage ram)
    (high : ram 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : ram 0x41#16 = softwareStack.setWidth 8)
    (mode : ram 0x44#16 = 0#8) (kept : ram 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : ram (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (ptr : ram (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 248) (returnSpace : returning.ptr.toNat ≤ 247) :
    let port := ram (softwareStack + (pointer - 1#8).setWidth 16)
    let value := if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4 else ram (0x759 + port.setWidth 16)
    ∃ final, Reaches (machine ram 0x4b1 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update
        (Function.update ram (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - 1#8))
        (softwareStack + 0x100#16) ((if keep = 0 then pointer - 1#8 else pointer) + 1#8))
        (softwareStack + (if keep = 0 then pointer - 1#8 else pointer).setWidth 16) value ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  dsimp only
  let port := ram (softwareStack + (pointer - 1#8).setWidth 16)
  have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
  have h4b1 : ram 0x4b1#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h4b2 : ram 0x4b2#16 = 0xfd#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h4b3 : ram 0x4b3#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h4b4 : ram 0x4b4#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h4b5 : ram 0x4b5#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h4b6 : ram 0x4b6#16 = 0x7b#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have call : Uxn.step (machine ram 0x4b1 working (Stack.pushWord returning returnAddress)) =
      .done (.next (machine ram 0x2b3 working (Stack.pushWord (Stack.pushWord returning returnAddress) 0x4b4))) := by
    simp [uxn_state, uxn_step, h4b1, h4b2, h4b3]
  obtain ⟨popped, popRun, popPC, popWP, popHigh, popLow, popRP, popRAM, popWF, popRF⟩ :=
    pop_byte_operand ram softwareStack pointer keep working (Stack.pushWord returning returnAddress) 0x4b4
      selected code high low kept keepBound cursor (by omega)
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have outside (address : Word) (available : address.toNat < 0x555 ∨ 0x759 ≤ address.toNat) :
      popped.mem.ram address = ram address := by
    rw [popRAM, Function.update_of_ne]
    rcases available with before | after <;> bv_omega
  have popCode : CodeImage popped.mem.ram := by
    rw [popRAM]
    apply code.write
    right; left
    bv_omega
  have popPointer : popped.mem.ram (softwareStack + 0x100#16) =
      if keep = 0 then pointer - 1#8 else pointer := by
    rw [popRAM]
    by_cases zero : keep = 0
    · simp [zero]
    · rw [Function.update_of_ne (by bv_omega), ptr, if_neg zero]
  have popEta : Stack.pushWord {popped.mem.wstk with ptr := working.ptr} (port.setWidth 16) = popped.mem.wstk := by
    have joined (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by simpa using (join_bytes 0#8 byte).symm
    simpa [popWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, popHigh, popLow, port, joined]
      using Stack.asPushWord popped.mem.wstk
  have returnPointer : popped.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using popRP
  have frameHigh : popped.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [popRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have frameLow : popped.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [popRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnEta : Stack.pushWord {popped.mem.rstk with ptr := returning.ptr} returnAddress = popped.mem.rstk := by
    simpa [returnPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, frameHigh, frameLow, append_split]
      using Stack.asPushWord popped.mem.rstk
  obtain ⟨final, readRun, finalPC, finalWP, finalRP, finalRAM, finalWF, finalRF⟩ :=
    device_reader_byte popped.mem.ram softwareStack (if keep = 0 then pointer - 1#8 else pointer)
      port {popped.mem.wstk with ptr := working.ptr} {popped.mem.rstk with ptr := returning.ptr} returnAddress
      selected popCode (by rw [outside _ (.inl (by decide))]; exact high)
      (by rw [outside _ (.inl (by decide))]; exact low)
      (by rw [outside _ (.inl (by decide))]; exact mode) popPointer workingSpace (by dsimp; omega)
  have jump : Uxn.step popped = .done (.next {popped with pc := 0x332}) := by
    have h4b4' := (outside 0x4b4 (.inl (by decide))).trans h4b4
    have h4b5' := (outside 0x4b5 (.inl (by decide))).trans h4b5
    have h4b6' := (outside 0x4b6 (.inl (by decide))).trans h4b6
    simp only [BitVec.ofNat_eq_ofNat] at popPC h4b4' h4b5' h4b6'
    simp [uxn_state, uxn_step, popPC, h4b4', h4b5', h4b6']
  have tail : Reaches popped final := by
    apply Reaches.next jump
    change Reaches (machine popped.mem.ram 0x332 popped.mem.wstk popped.mem.rstk) final
    simpa only [popEta, returnEta] using readRun
  refine ⟨final, .next call (popRun.trans tail), finalPC, finalWP, finalRP, ?_, ?_, ?_⟩
  · rw [finalRAM, outside _ (.inl (by decide)), outside _ (.inl (by decide)),
      outside _ (.inr (by bv_omega)), popRAM]
    rfl
  · intro index below
    rw [finalWF _ below, popWF _ below]
  · intro index before
    rw [finalRF _ before, popRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
