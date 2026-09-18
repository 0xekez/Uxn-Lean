import ProgramProofs.Uxnmin.OperandCall
import ProgramProofs.Uxnmin.PcSet

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem handler_jmp (memory : Word → Byte) (softwareStack pc : Word) (pointer keep : Byte)
    (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x42e working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update
        (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
          (pointer - (if short then 2#8 else 1#8)))
        0x45 ((jumpTarget pc (stackOperand memory softwareStack pointer short) short >>> 8).setWidth 8))
        0x46 ((jumpTarget pc (stackOperand memory softwareStack pointer short) short).setWidth 8) ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have jump_call : OperandCallCode 0x42e .mode := by
    intro memory working returning code
    apply jsi_call
    · exact code _ (by decide) (by decide) (by simp [MutableCode])
    · have a : memory 0x42f#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have b : memory 0x430#16 = 0x7c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      simp [OperandKind.entry, a, b]
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by
    rcases selected with rfl | rfl <;> bv_omega
  obtain ⟨popped, before, poppedPC, poppedMem, poppedCode, poppedWP,
      poppedRP, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_call_operand .mode 0x42e jump_call memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor workingSpace returnSpace
  simp only [OperandKind.short] at workingEta poppedMem
  have poppedMode : popped.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [poppedMem, Function.update_of_ne (separate _ (by decide)), mode]
  have poppedHigh : popped.mem.ram 0x45#16 = (pc >>> 8).setWidth 8 := by
    rw [poppedMem, Function.update_of_ne (separate _ (by decide)), pcHigh]
  have poppedLow : popped.mem.ram 0x46#16 = pc.setWidth 8 := by
    rw [poppedMem, Function.update_of_ne (separate _ (by decide)), pcLow]
  have code431 : popped.mem.ram 0x431#16 = 0x40#8 := poppedCode _ (by decide) (by decide) (by simp [MutableCode])
  have code432 : popped.mem.ram 0x432#16 = 0xfe#8 := poppedCode _ (by decide) (by decide) (by simp [MutableCode])
  have code433 : popped.mem.ram 0x433#16 = 0x4a#8 := poppedCode _ (by decide) (by decide) (by simp [MutableCode])
  obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalCode, finalWF, finalRF⟩ :=
    pc_set popped.mem.ram pc (stackOperand memory softwareStack pointer short) returnAddress short
      { popped.mem.wstk with ptr := working.ptr } { popped.mem.rstk with ptr := returning.ptr }
      poppedCode poppedMode poppedHigh poppedLow (by dsimp; omega) (by dsimp; omega)
  have poppedShape : popped = machine popped.mem.ram 0x431 popped.mem.wstk popped.mem.rstk := by
    cases popped
    simpa [machine] using poppedPC
  have after : Reaches popped final := by
    rw [poppedShape]
    apply Reaches.next
    · simp [uxn_state, uxn_step, code431, code432, code433]
      rfl
    simpa [OperandKind.short, workingEta, returningEta, machine] using finalSteps
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, poppedMem]
  · intro address bound
    rw [finalWF _ bound, workingFrame _ bound]
  · intro address bound
    rw [finalRF _ bound, returningFrame _ bound]

end ProgramProofs.Uxnmin
