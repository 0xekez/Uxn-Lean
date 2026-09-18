import ProgramProofs.Uxnmin.DeviceWriter

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- All DEO modes prepare the output value and port, including DEO2's first shadow byte. -/
theorem handler_device_write (ram : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage ram)
    (high : ram 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : ram 0x41#16 = softwareStack.setWidth 8)
    (mode : ram 0x44#16 = if short then 1 else 0) (kept : ram 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : ram (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 247) :
    let port := ram (softwareStack + (pointer - 1#8).setWidth 16)
    let value := stackOperand ram softwareStack (pointer - 1#8) short
    let popped := Function.update ram (softwareStack + (0x100#16 + keep.setWidth 16))
      (pointer - 1#8 - (if short then 2#8 else 1#8))
    ∃ final, Reaches (machine ram 0x4b7 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = 0x1af ∧
      final.mem.ram = (if short then Function.update popped (0x759 + port.setWidth 16) ((value >>> 8).setWidth 8) else popped) ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      final.mem.wstk.data working.ptr = value.setWidth 8 ∧
      final.mem.wstk.data (working.ptr + 1) = port + (if short then 1 else 0) ∧
      final.mem.rstk.ptr = returning.ptr + 2 ∧
      Stack.pushWord {final.mem.rstk with ptr := returning.ptr} returnAddress = final.mem.rstk ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  dsimp only
  have calls : OperandPairCode 0x4b7 .byte .mode := by
    intro memory working returning offset image choice
    have h4b7 : memory 0x4b7#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
    have h4b8 : memory 0x4b8#16 = 0xfd#8 := image _ (by decide) (by decide) (by simp [MutableCode])
    have h4b9 : memory 0x4b9#16 = 0xf9#8 := image _ (by decide) (by decide) (by simp [MutableCode])
    have h4ba : memory 0x4ba#16 = 0x60#8 := image _ (by decide) (by decide) (by simp [MutableCode])
    have h4bb : memory 0x4bb#16 = 0xfd#8 := image _ (by decide) (by decide) (by simp [MutableCode])
    have h4bc : memory 0x4bc#16 = 0xf0#8 := image _ (by decide) (by decide) (by simp [MutableCode])
    rcases choice with rfl | rfl <;>
      simp [uxn_state, uxn_step, OperandKind.entry, h4b7, h4b8, h4b9, h4ba, h4bb, h4bc]
  obtain ⟨popped, popRun, popPC, popRAM, popCode, popWP, popRP, popEta, returnEta, popWF, popRF⟩ :=
    pop_operand_pair .byte .mode 0x4b7 calls ram softwareStack pointer keep short working returning returnAddress
      selected code high low mode kept keepBound cursor workingSpace returnSpace
  simp only [OperandKind.short, Bool.false_eq_true, if_false, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at popPC popRAM popWP popRP popEta
  let port := ram (softwareStack + (pointer - 1#8).setWidth 16)
  let value := stackOperand ram softwareStack (pointer - 1#8) short
  have joined (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by simpa using (join_bytes 0#8 byte).symm
  have portOperand : stackOperand ram softwareStack pointer false = port.setWidth 16 := by simp [stackOperand, port, joined]
  rw [portOperand] at popEta
  change Stack.pushWord (Stack.pushWord {popped.mem.wstk with ptr := working.ptr} (port.setWidth 16)) value = popped.mem.wstk at popEta
  have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
  have poppedMode : popped.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [popRAM, Function.update_of_ne (by bv_omega), mode]
  have h4bd : popped.mem.ram 0x4bd#16 = 0x24#8 := popCode _ (by decide) (by decide) (by simp [MutableCode])
  have h4be : popped.mem.ram 0x4be#16 = 0x40#8 := popCode _ (by decide) (by decide) (by simp [MutableCode])
  have h4bf : popped.mem.ram 0x4bf#16 = 0xfe#8 := popCode _ (by decide) (by decide) (by simp [MutableCode])
  have h4c0 : popped.mem.ram 0x4c0#16 = 0x57#8 := popCode _ (by decide) (by decide) (by simp [MutableCode])
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  have padHigh : (port.setWidth 16 >>> 8).setWidth 8 = 0#8 := by bv_omega
  have swapped : ∃ middle, Reaches
      (machine popped.mem.ram 0x4bd
        (Stack.pushWord (Stack.pushWord {popped.mem.wstk with ptr := working.ptr} (port.setWidth 16)) value)
        popped.mem.rstk) middle ∧
      middle.pc = 0x318 ∧ middle.mem.ram = popped.mem.ram ∧ middle.mem.rstk = popped.mem.rstk ∧
      middle.mem.wstk.ptr = working.ptr + 4 ∧
      middle.mem.wstk.data working.ptr = (value >>> 8).setWidth 8 ∧
      middle.mem.wstk.data (working.ptr + 1) = value.setWidth 8 ∧
      middle.mem.wstk.data (working.ptr + 2) = 0 ∧ middle.mem.wstk.data (working.ptr + 3) = port ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → middle.mem.wstk.data index = popped.mem.wstk.data index) := by
    iterate 2
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, h4bd, h4be, h4bf, h4c0, byteHigh, byteLow, padHigh]
        rfl
    refine ⟨_, .refl _, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [byteHigh, byteLow, padHigh]
    · simp [byteHigh, byteLow, padHigh]
    · simp [byteHigh, byteLow, padHigh]
    · simp [byteHigh, byteLow, padHigh]
    · intro index before
      simp (disch := bv_omega) only [Function.update_of_ne]
  obtain ⟨middle, swapRun, middlePC, middleRAM, middleRS, middleWP, middleVH, middleVL, middlePH, middlePL, middleWF⟩ := swapped
  simp only [BitVec.ofNat_eq_ofNat] at middleWP middleVH middleVL middlePH middlePL
  have middleEta : Stack.pushWord (Stack.pushWord {middle.mem.wstk with ptr := working.ptr} value)
      (port.setWidth 16) = middle.mem.wstk := by
    simpa [middleWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, middleVH, middleVL, middlePH, middlePL, joined, append_split]
      using Stack.asPushPair middle.mem.wstk
  have runSwap : Reaches popped middle := by
    have shape : popped = machine popped.mem.ram popped.pc popped.mem.wstk popped.mem.rstk := rfl
    rw [popPC] at shape
    rw [shape]
    have swapRun' := swapRun
    simp only [popEta] at swapRun'
    simpa only [BitVec.ofNat_eq_ofNat] using swapRun'
  obtain ⟨final, writerRun, finalPC, finalRAM, finalWP, finalValue, finalPort, finalRP, finalWF, finalRF⟩ :=
    device_writer popped.mem.ram popCode short port value {middle.mem.wstk with ptr := working.ptr} middle.mem.rstk
      poppedMode workingSpace (by rw [middleRS, popRP]; bv_omega)
  have runWriter : Reaches middle final := by
    have shape : middle = machine middle.mem.ram middle.pc middle.mem.wstk middle.mem.rstk := rfl
    rw [middleRAM, middlePC] at shape
    rw [shape]
    simpa only [middleEta] using writerRun
  have finalPointer : final.mem.rstk.ptr = returning.ptr + 2#8 := by rw [finalRP, middleRS, popRP]
  have finalFrame (index : Byte) (before : index.toNat < (returning.ptr + 2#8).toNat) :
      final.mem.rstk.data index = popped.mem.rstk.data index := by
    rw [finalRF _ (by rw [middleRS, popRP]; exact before), middleRS]
  have returnHigh : final.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [finalFrame _ (by bv_omega), ← returnEta]
    simp [Stack.pushWord, Stack.push]
  have returnLow : final.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [finalFrame _ (by bv_omega), ← returnEta]
    simp [Stack.pushWord, Stack.push]
  refine ⟨final, popRun.trans (runSwap.trans runWriter), finalPC, ?_, finalWP, finalValue, finalPort, finalPointer, ?_, ?_, ?_⟩
  · rw [finalRAM, popRAM]
  · simpa [finalPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, returnHigh, returnLow, append_split]
      using Stack.asPushWord final.mem.rstk
  · intro index before
    rw [finalWF _ before, middleWF _ before, popWF _ before]
  · intro index before
    rw [finalFrame _ (by bv_omega), popRF _ before]

end ProgramProofs.Uxnmin
