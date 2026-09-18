import ProgramProofs.Uxnmin.OperandCall
import ProgramProofs.Uxnmin.Destination
import ProgramProofs.Host.StackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Transfer one byte or word to the other guest stack, honoring keep mode. -/
theorem handler_sth (memory : Word → Byte) (source destination : Word)
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
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (source + (0x100#16 + keep.setWidth 16)) = pointer)
    (destinationPtr : memory (destination + 0x100#16) = destinationPointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x452 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (Function.update (Function.update
          (Function.update memory (source + (0x100#16 + keep.setWidth 16))
            (pointer - (if short then 2#8 else 1#8)))
          0x40 ((destination >>> 8).setWidth 8)) 0x41 (destination.setWidth 8))
        destination destinationPointer (stackOperand memory source pointer short) short ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have call : OperandCallCode 0x452 .mode := by
    intro memory working returning code
    apply jsi_call
    · exact code _ (by decide) (by decide) (by simp [MutableCode])
    · have high : memory 0x453#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have low : memory 0x454#16 = 0x58#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      simp [OperandKind.entry, high, low]
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ source + (0x100#16 + keep.setWidth 16) := by
    rcases sourceSelected with rfl | rfl <;> bv_omega
  obtain ⟨popped, before, poppedPC, poppedMemory, poppedCode, poppedWorking,
    poppedReturning, operandShape, returnShape, workingFrame, returningFrame⟩ :=
    pop_call_operand .mode 0x452 call memory source pointer keep short working returning returnAddress
      sourceSelected code sourceHigh sourceLow mode kept keepBound cursor (by omega) returnSpace
  obtain ⟨selected, selection, selectedPC, selectedMemory, selectedWorking, selectedReturning, selectedFrame⟩ :=
    select_destination popped.mem.ram 0x455 destination popped.mem.wstk popped.mem.rstk poppedCode
      (.inr rfl)
      (by rw [poppedMemory, Function.update_of_ne (separate _ (by decide)), destinationHigh])
      (by rw [poppedMemory, Function.update_of_ne (separate _ (by decide)), destinationLow])
      (by rw [poppedWorking]; bv_omega)
  have selectedCode : CodeImage selected.mem.ram := by
    rw [selectedMemory]
    exact (poppedCode.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  have selectedMode : selected.mem.ram 0x44#16 = if short then 1 else 0 := by
    rw [selectedMemory, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      poppedMemory, Function.update_of_ne (separate _ (by decide)), mode]
  have selectedPtr : selected.mem.ram (destination + 0x100#16) = destinationPointer := by
    rw [selectedMemory, poppedMemory]
    rcases sourceSelected with rfl | rfl <;> rcases destinationSelected with rfl | rfl
    all_goals first | exact False.elim (different rfl) | simpa (disch := bv_omega) [Function.update_of_ne] using destinationPtr
  have selectedOperand : Stack.pushWord { selected.mem.wstk with ptr := working.ptr }
      (stackOperand memory source pointer short) = selected.mem.wstk :=
    Stack.asPushWord_of_frame popped.mem.wstk selected.mem.wstk working.ptr
      (stackOperand memory source pointer short) operandShape (by omega) selectedWorking selectedFrame
  obtain ⟨final, pushed, finalPC, finalWorking, finalReturning, finalMemory, finalWF, finalRF⟩ :=
    push_operand selected.mem.ram destination destinationPointer (stackOperand memory source pointer short) short
      { selected.mem.wstk with ptr := working.ptr } { popped.mem.rstk with ptr := returning.ptr } returnAddress
      destinationSelected selectedCode
      (by rw [selectedMemory]; simp) (by rw [selectedMemory]; simp) selectedMode selectedPtr workingSpace
      (by dsimp; omega)
  have poppedShape : popped = machine popped.mem.ram 0x455 popped.mem.wstk popped.mem.rstk := by
    cases popped
    simpa [machine] using poppedPC
  have selectedShape : selected = machine selected.mem.ram 0x45b selected.mem.wstk selected.mem.rstk := by
    cases selected
    simpa [machine] using selectedPC
  have tail : Reaches selected final := by
    have byte0 : selected.mem.ram 0x45b#16 = 0x40#8 := selectedCode _ (by decide) (by decide) (by simp [MutableCode])
    have byte1 : selected.mem.ram 0x45c#16 = 0xfe#8 := selectedCode _ (by decide) (by decide) (by simp [MutableCode])
    have byte2 : selected.mem.ram 0x45d#16 = 0x2e#8 := selectedCode _ (by decide) (by decide) (by simp [MutableCode])
    rw [selectedShape]
    apply Reaches.next
    · simp [uxn_state, uxn_step, byte0, byte1, byte2]
      rfl
    simpa [selectedOperand, returnShape, selectedReturning, machine] using pushed
  refine ⟨final, before.trans ?_, finalPC, finalWorking, finalReturning, ?_, ?_, ?_, ?_⟩
  · rw [poppedShape]
    exact selection.trans tail
  · rw [finalMemory, selectedMemory, poppedMemory]
    rfl
  · rw [finalMemory]
    have pointerAfter : 0x555 ≤ (destination + 0x100#16).toNat := by
      rcases destinationSelected with rfl | rfl <;> decide
    have dataAfter (index : Byte) : 0x555 ≤ (destination + index.setWidth 16).toNat := by
      rcases destinationSelected with rfl | rfl <;> bv_omega
    split <;> first
      | exact ((selectedCode.write _ _ (.inr (.inl pointerAfter))).write _ _ (.inr (.inl (dataAfter _)))).write _ _ (.inr (.inl (dataAfter _)))
      | exact (selectedCode.write _ _ (.inr (.inl pointerAfter))).write _ _ (.inr (.inl (dataAfter _)))
  · intro index smaller
    rw [finalWF _ smaller, selectedFrame _ (by rw [poppedWorking]; bv_omega), workingFrame _ smaller]
  · intro index smaller
    rw [finalRF _ smaller, returningFrame _ smaller]

end ProgramProofs.Uxnmin
