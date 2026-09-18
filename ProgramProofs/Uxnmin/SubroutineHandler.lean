import ProgramProofs.Uxnmin.SaveReturn
import ProgramProofs.Uxnmin.PcSet
import ProgramProofs.Host.StackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JSR transfers the return PC to the other stack, then installs the jump target. -/
theorem handler_jsr (memory : Word → Byte) (source destination pc : Word)
    (pointer destinationPointer keep : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (sourceSelected : source = 0x555 ∨ source = 0x657)
    (destinationSelected : destination = 0x555 ∨ destination = 0x657)
    (different : source ≠ destination) (code : CodeImage memory)
    (sourceHigh : memory 0x40#16 = (source >>> 8).setWidth 8)
    (sourceLow : memory 0x41#16 = source.setWidth 8)
    (destinationHigh : memory 0x42#16 = (destination >>> 8).setWidth 8)
    (destinationLow : memory 0x43#16 = destination.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (source + (0x100#16 + keep.setWidth 16)) = pointer)
    (destinationPtr : memory (destination + 0x100#16) = destinationPointer)
    (workingSpace : working.ptr.toNat ≤ 245) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x440 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update
        (storeStackOperand
          (Function.update (Function.update
            (Function.update memory (source + (0x100#16 + keep.setWidth 16))
              (pointer - (if short then 2#8 else 1#8)))
            0x40 ((destination >>> 8).setWidth 8)) 0x41 (destination.setWidth 8))
          destination destinationPointer pc true)
        0x45 ((jumpTarget pc (stackOperand memory source pointer short) short >>> 8).setWidth 8))
        0x46 ((jumpTarget pc (stackOperand memory source pointer short) short).setWidth 8) ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have call : OperandCallCode 0x440 .mode := by
    intro memory working returning code
    apply jsi_call
    · exact code _ (by decide) (by decide) (by simp [MutableCode])
    · have high : memory 0x441#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have low : memory 0x442#16 = 0x6a#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      simp [OperandKind.entry, high, low]
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ source + (0x100#16 + keep.setWidth 16) := by
    rcases sourceSelected with rfl | rfl <;> bv_omega
  obtain ⟨popped, before, poppedPC, poppedMemory, poppedCode, poppedWorking,
    poppedReturning, operandShape, returnShape, workingFrame, returningFrame⟩ :=
    pop_call_operand .mode 0x440 call memory source pointer keep short working returning returnAddress
      sourceSelected code sourceHigh sourceLow mode kept keepBound cursor (by omega) returnSpace
  simp only [OperandKind.short] at operandShape
  have poppedPtr : popped.mem.ram (destination + 0x100#16) = destinationPointer := by
    rw [poppedMemory]
    rcases sourceSelected with rfl | rfl <;> rcases destinationSelected with rfl | rfl
    all_goals first | exact False.elim (different rfl) | simpa (disch := bv_omega) [Function.update_of_ne] using destinationPtr
  obtain ⟨saved, saving, savedPC, savedWorking, savedReturning, savedMemory, savedCode, savedWF, savedRF⟩ :=
    save_return_address popped.mem.ram pc destination destinationPointer popped.mem.wstk popped.mem.rstk
      destinationSelected poppedCode
      (by rw [poppedMemory, Function.update_of_ne (separate _ (by decide)), destinationHigh])
      (by rw [poppedMemory, Function.update_of_ne (separate _ (by decide)), destinationLow])
      (by rw [poppedMemory, Function.update_of_ne (separate _ (by decide)), pcHigh])
      (by rw [poppedMemory, Function.update_of_ne (separate _ (by decide)), pcLow]) poppedPtr
      (by rw [poppedWorking]; bv_omega) (by rw [poppedReturning]; bv_omega)
  have savedStable (address : Word) (above : 0x41 < address.toNat) (below : address.toNat < 0x555) :
      saved.mem.ram address = memory address := by
    have highNe : address ≠ 0x40 := by bv_omega
    have lowNe : address ≠ 0x41 := by bv_omega
    have pointerNe : address ≠ destination + 0x100#16 := by
      rcases destinationSelected with rfl | rfl <;> bv_omega
    have dataNe (index : Byte) : address ≠ destination + index.setWidth 16 := by
      rcases destinationSelected with rfl | rfl <;> bv_omega
    have unchanged : saved.mem.ram address = popped.mem.ram address := by
      rw [savedMemory]
      simp only [storeStackOperand, if_true,
        Function.update_of_ne pointerNe, Function.update_of_ne (dataNe destinationPointer),
        Function.update_of_ne (dataNe (destinationPointer + 1#8)),
        Function.update_of_ne lowNe, Function.update_of_ne highNe]
    rw [unchanged, poppedMemory, Function.update_of_ne (separate address below)]
  have savedOperand := Stack.asPushWord_of_frame popped.mem.wstk saved.mem.wstk working.ptr
    (stackOperand memory source pointer short) operandShape (by omega) savedWorking savedWF
  have savedReturn := Stack.asPushWord_of_frame popped.mem.rstk saved.mem.rstk returning.ptr
    returnAddress returnShape (by omega) savedReturning savedRF
  obtain ⟨final, finishing, finalPC, finalWorking, finalReturning, finalMemory, finalCode, finalWF, finalRF⟩ :=
    pc_set saved.mem.ram pc (stackOperand memory source pointer short) returnAddress short
      { saved.mem.wstk with ptr := working.ptr } { saved.mem.rstk with ptr := returning.ptr }
      savedCode
      (by rw [savedStable _ (by decide) (by decide), mode])
      (by rw [savedStable _ (by decide) (by decide), pcHigh])
      (by rw [savedStable _ (by decide) (by decide), pcLow]) (by dsimp; omega) (by dsimp; omega)
  have poppedShape : popped = machine popped.mem.ram 0x443 popped.mem.wstk popped.mem.rstk := by
    cases popped
    simpa [machine] using poppedPC
  have savedShape : saved = machine saved.mem.ram 0x44f saved.mem.wstk saved.mem.rstk := by
    cases saved
    simpa [machine] using savedPC
  have tail : Reaches saved final := by
    have byte0 : saved.mem.ram 0x44f#16 = 0x40#8 := savedCode _ (by decide) (by decide) (by simp [MutableCode])
    have byte1 : saved.mem.ram 0x450#16 = 0xfe#8 := savedCode _ (by decide) (by decide) (by simp [MutableCode])
    have byte2 : saved.mem.ram 0x451#16 = 0x2c#8 := savedCode _ (by decide) (by decide) (by simp [MutableCode])
    rw [savedShape]
    apply Reaches.next
    · simp [uxn_state, uxn_step, byte0, byte1, byte2]
      rfl
    simpa [savedOperand, savedReturn, machine] using finishing
  refine ⟨final, before.trans ?_, finalPC, finalWorking, finalReturning, ?_, finalCode, ?_, ?_⟩
  · rw [poppedShape]
    exact saving.trans tail
  · rw [finalMemory, savedMemory, poppedMemory]
    rfl
  · intro index smaller
    rw [finalWF _ smaller, savedWF _ (by rw [poppedWorking]; bv_omega), workingFrame _ smaller]
  · intro index smaller
    rw [finalRF _ smaller, savedRF _ (by rw [poppedReturning]; bv_omega), returningFrame _ smaller]

end ProgramProofs.Uxnmin
