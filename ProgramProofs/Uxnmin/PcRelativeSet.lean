import Mathlib.Tactic.Convert
import Mathlib.Tactic.SplitIfs
import ProgramProofs.Uxnmin.Pc
import ProgramProofs.Uxnmin.StackView

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem pc_set_relative (memory : Word → Byte) (pc offset returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (high : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (low : memory 0x46#16 = pc.setWidth 8)
    (workingSpace : working.ptr.toNat ≤ 252)
    (returnSpace : returning.ptr.toNat ≤ 252) :
    ∃ final, Reaches
      (machine memory 0x284 (Stack.pushWord working offset)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update
        (Function.update memory 0x45 (((pc + (offset.setWidth 8).signExtend 16) >>> 8).setWidth 8))
        0x46 ((pc + (offset.setWidth 8).signExtend 16).setWidth 8) ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code284 : memory 0x284#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code285 : memory 0x285#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code286 : memory 0x286#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code287 : memory 0x287#16 = 0xe9#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have preserves (value : Word) : CodeImage
      (Function.update (Function.update memory 0x45 ((value >>> 8).setWidth 8)) 0x46 (value.setWidth 8)) :=
    (code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  let scratch : Uxn.Stack := { working with data := Function.update working.data (working.ptr + 1) (offset.setWidth 8) }
  obtain ⟨relative, relativeSteps, relativePC, relativeMem, relativeWP, relativeValue,
      relativeRP, relativeWF, relativeRF⟩ :=
    pc_relative memory pc 0x288 (offset.setWidth 8) scratch
      (Stack.pushWord returning returnAddress) code high low workingSpace
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have header : Reaches
      (machine memory 0x284 (Stack.pushWord working offset) (Stack.pushWord returning returnAddress))
      (machine memory 0x285 (Stack.push scratch (offset.setWidth 8))
        (Stack.pushWord returning returnAddress)) := by
    iterate 1
      apply Reaches.next
      · simp [uxn_state, uxn_step, code284]
        rfl
    convert Reaches.refl (machine memory 0x285 (Stack.push scratch (offset.setWidth 8))
      (Stack.pushWord returning returnAddress)) using 1
    simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, scratch]
    congr 3
    funext address
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | exfalso; bv_omega
  have before : Reaches
      (machine memory 0x284 (Stack.pushWord working offset) (Stack.pushWord returning returnAddress)) relative := by
    refine header.trans (.next ?_ relativeSteps)
    simp [uxn_state, uxn_step, code285, code286, code287]
  have relativeCode : CodeImage relative.mem.ram := by rw [relativeMem]; exact code
  have relativeWorking : relative.mem.wstk.ptr = working.ptr + 2#8 := by
    simpa [scratch] using relativeWP
  have workingWord : relative.mem.wstk.data working.ptr ++ relative.mem.wstk.data (working.ptr + 1#8) =
      pc + (offset.setWidth 8).signExtend 16 := by
    simpa [scratch] using relativeValue
  have workingEta : Stack.pushWord { relative.mem.wstk with ptr := working.ptr }
      (pc + (offset.setWidth 8).signExtend 16) = relative.mem.wstk := by
    simpa [relativeWorking, BitVec.sub_eq_add_neg, BitVec.add_assoc, workingWord]
      using Stack.asPushWord relative.mem.wstk
  have returningPointer : relative.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using relativeRP
  have returnHigh : relative.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [relativeRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : relative.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [relativeRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningEta : Stack.pushWord { relative.mem.rstk with ptr := returning.ptr } returnAddress = relative.mem.rstk := by
    simpa [returningPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, returnHigh, returnLow, append_split]
      using Stack.asPushWord relative.mem.rstk
  obtain ⟨final, finalSteps, finalPC, finalMem, finalWP, finalRP, finalWF, finalRF⟩ :=
    pc_set_absolute relative.mem.ram (pc + (offset.setWidth 8).signExtend 16) returnAddress
      { relative.mem.wstk with ptr := working.ptr } { relative.mem.rstk with ptr := returning.ptr }
      relativeCode (by dsimp; omega) (by dsimp; omega)
  have shape : relative = machine relative.mem.ram 0x288 relative.mem.wstk relative.mem.rstk := by
    cases relative
    simpa [machine] using relativePC
  have after : Reaches relative final := by
    rw [shape]
    simpa only [workingEta, returningEta] using finalSteps
  have finalCode : CodeImage final.mem.ram := by
    rw [finalMem, relativeMem]
    exact preserves _
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, relativeMem]
  · intro address bound
    rw [finalWF _ bound, relativeWF _ bound]
    simp (disch := bv_omega) only [scratch, Function.update_of_ne]
  · intro address bound
    rw [finalRF _ bound, relativeRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
