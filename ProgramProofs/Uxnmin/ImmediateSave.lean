import ProgramProofs.Uxnmin.PushOperand
import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Reaches

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JSI saves the immediate instruction's return PC before its shared JMI suffix. -/
theorem immediate_save_return (memory : Word → Byte) (pc : Word) (pointer : Byte)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (pcHigh : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (pcLow : memory 0x46#16 = pc.setWidth 8)
    (stackPointer : memory 0x757#16 = pointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches (machine memory 0x396 working returning) final ∧
      final.pc = 0x3a4 ∧ final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand (Function.update (Function.update memory 0x40 6) 0x41 0x57)
        0x657 pointer (pc + 2) true ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  let scratch : Uxn.Stack := { working with data := Function.update working.data (working.ptr + 2#8) 0x40#8 }
  let selected := Function.update (Function.update memory 0x40 6) 0x41 0x57
  have selectedCode : CodeImage selected := (code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  obtain ⟨final, push, finalPC, finalWorking, finalReturning, finalMemory, finalWF, finalRF⟩ :=
    push_word selected 0x657 pointer (pc + 2) scratch returning 0x3a4 (.inr rfl) selectedCode
      (by simp [selected]) (by simp [selected]) (by simpa [selected] using stackPointer)
      workingSpace returnSpace
  have initial : Reaches (machine memory 0x396 working returning)
      (machine selected 0x2a6 (Stack.pushWord scratch (pc + 2)) (Stack.pushWord returning 0x3a4)) := by
    have code396 : memory 0x396#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code397 : memory 0x397#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code398 : memory 0x398#16 = 0x57#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code399 : memory 0x399#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code39a : memory 0x39a#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code39b : memory 0x39b#16 = 0x31#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code39c : memory 0x39c#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code39d : memory 0x39d#16 = 0x45#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code39e : memory 0x39e#16 = 0x30#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code39f : memory 0x39f#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code3a0 : memory 0x3a0#16 = 0x21#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code3a1 : memory 0x3a1#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code3a2 : memory 0x3a2#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    have code3a3 : memory 0x3a3#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
    iterate 8
      apply Reaches.next
      · simp [uxn_state, uxn_step, code396, code397, code398, code399, code39a, code39b, code39c, code39d, code39e, code39f, code3a0, code3a1, code3a2, code3a3, pcHigh, pcLow]
        rfl
    convert Reaches.refl (machine selected 0x2a6 (Stack.pushWord scratch (pc + 2))
      (Stack.pushWord returning 0x3a4)) using 1
    simp only [selected, scratch, machine, Stack.pushWord, Stack.push,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
    congr 3
    funext index
    simp only [Function.update_apply]
    split_ifs <;> rfl
  refine ⟨final, initial.trans push, finalPC, finalWorking, finalReturning, ?_, ?_, ?_, finalRF⟩
  · simpa [storeStackOperand, selected] using finalMemory
  · rw [finalMemory]
    exact ((selectedCode.write _ _ (.inr (.inl (by decide)))).write _ _ (.inr (.inl (by bv_omega)))).write _ _ (.inr (.inl (by bv_omega)))

  · intro index below
    rw [finalWF _ below]
    simp (disch := bv_omega) only [scratch, Function.update_of_ne]

end ProgramProofs.Uxnmin
