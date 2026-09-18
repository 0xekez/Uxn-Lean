import ProgramProofs.Uxnmin.Destination
import ProgramProofs.Uxnmin.OperandCall
import ProgramProofs.Host.StackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The middle of JSR saves the guest PC on the destination software stack. -/
theorem save_return_address (memory : Word → Byte) (pc destination : Word) (pointer : Byte)
    (working returning : Uxn.Stack) (selected : destination = 0x555 ∨ destination = 0x657)
    (code : CodeImage memory)
    (destinationHigh : memory 0x42#16 = (destination >>> 8).setWidth 8)
    (destinationLow : memory 0x43#16 = destination.setWidth 8)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (ptr : memory (destination + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches (machine memory 0x443 working returning) final ∧
      final.pc = 0x44f ∧ final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (Function.update (Function.update memory 0x40 ((destination >>> 8).setWidth 8)) 0x41 (destination.setWidth 8))
        destination pointer pc true ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have loadPC : Reaches (machine memory 0x443 working returning)
      (machine memory 0x446 (Stack.pushWord working pc) returning) := by
    have byte0 : memory 0x443#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have byte1 : memory 0x444#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have byte2 : memory 0x445#16 = 0x30#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have first : Uxn.step (machine memory 0x443 working returning) =
        .done (.next (machine memory 0x445 (Stack.push working 0x45) returning)) := by
      simp [uxn_state, uxn_step, byte0, byte1]
    have second : Uxn.step (machine memory 0x445 (Stack.push working 0x45) returning) =
        .done (.next (machine memory 0x446 (Stack.pushWord working pc) returning)) := by
      simp [uxn_state, uxn_step, byte2, pcHigh, pcLow]
    exact .next first (.next second (.refl _))
  obtain ⟨selectedState, selection, selectedPC, selectedMemory, selectedWorking, selectedReturning, selectedFrame⟩ :=
    select_destination memory 0x446 destination (Stack.pushWord working pc) returning code (.inl rfl)
      destinationHigh destinationLow (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have selectedCode : CodeImage selectedState.mem.ram := by
    rw [selectedMemory]
    exact (code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  have selectedPtr : selectedState.mem.ram (destination + 0x100#16) = pointer := by
    rw [selectedMemory]
    rcases selected with rfl | rfl <;> simpa using ptr
  have selectedOperand : Stack.pushWord { selectedState.mem.wstk with ptr := working.ptr } pc =
      selectedState.mem.wstk := by
    apply Stack.asPushWord_of_frame (Stack.pushWord working pc) selectedState.mem.wstk
      working.ptr pc (by
        simp only [Stack.pushWord, Stack.push]
        congr 1
        funext index
        by_cases high : index = working.ptr <;>
          by_cases low : index = working.ptr + 1#8 <;> simp [high, low]) (by omega) selectedWorking selectedFrame
  obtain ⟨final, pushed, finalPC, finalWorking, finalReturning, finalMemory, finalWF, finalRF⟩ :=
    push_word selectedState.mem.ram destination pointer pc
      { selectedState.mem.wstk with ptr := working.ptr } returning 0x44f selected selectedCode
      (by rw [selectedMemory]; simp) (by rw [selectedMemory]; simp) selectedPtr workingSpace returnSpace
  have selectedShape : selectedState =
      machine selectedState.mem.ram 0x44c selectedState.mem.wstk selectedState.mem.rstk := by
    cases selectedState
    simpa [machine] using selectedPC
  have tail : Reaches selectedState final := by
    have call : Uxn.step (machine selectedState.mem.ram 0x44c selectedState.mem.wstk selectedState.mem.rstk) =
        .done (.next (machine selectedState.mem.ram 0x2a6 selectedState.mem.wstk
          (Stack.pushWord selectedState.mem.rstk 0x44f))) := by
      apply jsi_call
      · exact selectedCode _ (by decide) (by decide) (by simp [MutableCode])
      · have high : selectedState.mem.ram 0x44d#16 = 0xfe#8 := selectedCode _ (by decide) (by decide) (by simp [MutableCode])
        have low : selectedState.mem.ram 0x44e#16 = 0x57#8 := selectedCode _ (by decide) (by decide) (by simp [MutableCode])
        simp [high, low]
    rw [selectedShape]
    apply Reaches.next call
    simpa only [selectedOperand, selectedReturning] using pushed
  refine ⟨final, loadPC.trans (selection.trans tail), finalPC, finalWorking, finalReturning, ?_, ?_, ?_, finalRF⟩
  · rw [finalMemory, selectedMemory]
    rfl
  · rw [finalMemory]
    have pointerAfter : 0x555 ≤ (destination + 0x100#16).toNat := by
      rcases selected with rfl | rfl <;> decide
    have dataAfter (index : Byte) : 0x555 ≤ (destination + index.setWidth 16).toNat := by
      rcases selected with rfl | rfl <;> bv_omega
    exact ((selectedCode.write _ _ (.inr (.inl pointerAfter))).write _ _ (.inr (.inl (dataAfter _)))).write _ _ (.inr (.inl (dataAfter _)))
  · intro index smaller
    rw [finalWF _ smaller, selectedFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
