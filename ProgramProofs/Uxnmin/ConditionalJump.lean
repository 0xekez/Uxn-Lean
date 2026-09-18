import ProgramProofs.Uxnmin.JumpHandlers

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem jcn_taken (memory : Word → Byte) (offset condition : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (nonzero : condition.setWidth 8 ≠ 0#8) (workingSpace : working.ptr.toNat ≤ 251) :
    ∃ final, Reaches
      (machine memory 0x43a (Stack.pushWord (Stack.pushWord working offset) condition) returning) final ∧
      final.pc = 0x27e ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.wstk.data working.ptr = (offset >>> 8).setWidth 8 ∧
      final.mem.wstk.data (working.ptr + 1#8) = offset.setWidth 8 ∧
      final.mem.rstk = returning ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) := by
  have code43a : memory 0x43a#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43b : memory 0x43b#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43c : memory 0x43c#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43d : memory 0x43d#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 2
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, code43a, code43b, code43c, code43d, nonzero]
      rfl
  refine ⟨_, .refl _, rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · simp
  · simp
  · intro address bound
    simp (disch := bv_omega) only [Function.update_of_ne]

theorem jcn_not_taken (memory : Word → Byte) (offset condition returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (zero : condition.setWidth 8 = 0#8) (workingSpace : working.ptr.toNat ≤ 251)
    (returnSpace : returning.ptr.toNat ≤ 253) :
    ∃ final, Reaches
      (machine memory 0x43a (Stack.pushWord (Stack.pushWord working offset) condition)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code43a : memory 0x43a#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43b : memory 0x43b#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43c : memory 0x43c#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43d : memory 0x43d#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43e : memory 0x43e#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code43f : memory 0x43f#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  iterate 4
    apply Reaches.prepend
    · simp [uxn_state, uxn_step, code43a, code43b, code43c, code43d, code43e, code43f, zero]
      rfl
  refine ⟨_, .refl _, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals
    intro address bound
    simp (disch := bv_omega) only [Function.update_of_ne]

theorem jcn_calls : OperandPairCode 0x434 .mode .byte := by
  intro memory working returning offset code position
  apply jsi_call
  · rcases position with rfl | rfl <;>
      exact code _ (by decide) (by decide) (by simp [MutableCode])
  · have high : memory (0x434 + offset + 1) =
        (((if offset = 0 then 0x2ad else 0x2b3) - (0x434 + offset + 3)) >>> 8).setWidth 8 := by
      rcases position with rfl | rfl <;>
        exact code _ (by decide) (by decide) (by simp [MutableCode])
    have low : memory (0x434 + offset + 2) =
        ((if offset = 0 then 0x2ad else 0x2b3) - (0x434 + offset + 3)).setWidth 8 := by
      rcases position with rfl | rfl <;>
        exact code _ (by decide) (by decide) (by simp [MutableCode])
    rw [high, low, append_split]
    rfl


theorem handler_jcn (memory : Word → Byte) (softwareStack pc : Word) (pointer keep : Byte)
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
    (workingSpace : working.ptr.toNat ≤ 247)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory 0x434 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram =
        (if memory (softwareStack + (pointer - (if short then 2#8 else 1#8) - 1#8).setWidth 16) = 0 then
          Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
            (pointer - (if short then 2#8 else 1#8) - 1#8)
        else Function.update (Function.update
          (Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
            (pointer - (if short then 2#8 else 1#8) - 1#8))
          0x45 ((jumpTarget pc (stackOperand memory softwareStack pointer short) short >>> 8).setWidth 8))
          0x46 ((jumpTarget pc (stackOperand memory softwareStack pointer short) short).setWidth 8)) ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + (0x100#16 + keep.setWidth 16) := by
    rcases selected with rfl | rfl <;> bv_omega
  obtain ⟨popped, before, poppedPC, poppedMem, poppedCode, poppedWP,
      poppedRP, workingEta, returningEta, workingFrame, returningFrame⟩ :=
    pop_operand_pair .mode .byte 0x434 jcn_calls memory softwareStack pointer keep short
      working returning returnAddress selected code high low mode kept keepBound cursor workingSpace returnSpace
  simp only [OperandKind.short, Bool.false_eq_true, if_false] at workingEta poppedMem
  have poppedShape : popped = machine popped.mem.ram 0x43a popped.mem.wstk popped.mem.rstk := by
    cases popped
    simpa [machine] using poppedPC
  by_cases zero : memory (softwareStack + (pointer - (if short then 2#8 else 1#8) - 1#8).setWidth 16) = 0
  · obtain ⟨final, steps, finalPC, finalMem, finalWP, finalRP, finalWF, finalRF⟩ :=
      jcn_not_taken popped.mem.ram (stackOperand memory softwareStack pointer short)
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) false) returnAddress
        { popped.mem.wstk with ptr := working.ptr } { popped.mem.rstk with ptr := returning.ptr }
        poppedCode (by
          simp only [stackOperand, Bool.false_eq_true, if_false]
          rw [BitVec.setWidth_append_eq_right]
          exact zero) (by dsimp; omega) (by dsimp; omega)
    have after : Reaches popped final := by
      rw [poppedShape]
      simpa only [workingEta, returningEta] using steps
    refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, ?_, ?_, ?_⟩
    · rw [if_pos zero, finalMem, poppedMem]
    · rw [finalMem]; exact poppedCode
    · intro address bound
      rw [finalWF _ bound, workingFrame _ bound]
    · intro address bound
      rw [finalRF _ bound, returningFrame _ bound]
  · obtain ⟨branch, branchSteps, branchPC, branchMem, branchWP, branchVH, branchVL,
        branchRP, branchWF⟩ :=
      jcn_taken popped.mem.ram (stackOperand memory softwareStack pointer short)
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) false)
        { popped.mem.wstk with ptr := working.ptr } popped.mem.rstk
        poppedCode (by
          simp only [stackOperand, Bool.false_eq_true, if_false]
          rw [BitVec.setWidth_append_eq_right]
          exact zero) (by dsimp; omega)
    have takeBranch : Reaches popped branch := by
      rw [poppedShape]
      simpa only [workingEta] using branchSteps
    have branchCode : CodeImage branch.mem.ram := by rw [branchMem]; exact poppedCode
    have branchMode : branch.mem.ram 0x44#16 = if short then 1 else 0 := by
      rw [branchMem, poppedMem, Function.update_of_ne (separate _ (by decide)), mode]
    have branchHigh : branch.mem.ram 0x45#16 = (pc >>> 8).setWidth 8 := by
      rw [branchMem, poppedMem, Function.update_of_ne (separate _ (by decide)), pcHigh]
    have branchLow : branch.mem.ram 0x46#16 = pc.setWidth 8 := by
      rw [branchMem, poppedMem, Function.update_of_ne (separate _ (by decide)), pcLow]
    have branchEta : Stack.pushWord { branch.mem.wstk with ptr := working.ptr }
        (stackOperand memory softwareStack pointer short) = branch.mem.wstk := by
      simpa [branchWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, branchVH, branchVL, append_split]
        using Stack.asPushWord branch.mem.wstk
    obtain ⟨final, finalSteps, finalPC, finalWP, finalRP, finalMem, finalCode, finalWF, finalRF⟩ :=
      pc_set branch.mem.ram pc (stackOperand memory softwareStack pointer short) returnAddress short
        { branch.mem.wstk with ptr := working.ptr } { popped.mem.rstk with ptr := returning.ptr }
        branchCode branchMode branchHigh branchLow (by dsimp; omega) (by dsimp; omega)
    have branchShape : branch = machine branch.mem.ram 0x27e branch.mem.wstk branch.mem.rstk := by
      cases branch
      simpa [machine] using branchPC
    have after : Reaches branch final := by
      rw [branchShape, branchRP]
      simpa only [branchEta, returningEta] using finalSteps
    refine ⟨final, before.trans (takeBranch.trans after), finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
    · rw [if_neg zero, finalMem, branchMem, poppedMem]
    · intro address bound
      rw [finalWF _ bound, branchWF _ bound, workingFrame _ bound]
    · intro address bound
      rw [finalRF _ bound, returningFrame _ bound]

end ProgramProofs.Uxnmin
