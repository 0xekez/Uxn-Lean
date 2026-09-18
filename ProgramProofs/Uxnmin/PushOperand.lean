import ProgramProofs.Uxnmin.PopHandler
import ProgramProofs.Uxnmin.StackView

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem push_byte (memory : Word → Byte) (softwareStack : Word) (pointer value : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 248)
    (returnSpace : returning.ptr.toNat ≤ 251) :
    ∃ final, Reaches
      (machine memory 0x293 (Stack.push working value)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 1#8))
        (softwareStack + pointer.setWidth 16) value ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code293 : memory 0x293#16 = 0x80#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code294 : memory 0x294#16 = 0x40#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code295 : memory 0x295#16 = 0x30#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code296 : memory 0x296#16 = 0x26#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code297 : memory 0x297#16 = 0xa0#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code298 : memory 0x298#16 = 0x01#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code299 : memory 0x299#16 = 0x00#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code29a : memory 0x29a#16 = 0x38#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code29b : memory 0x29b#16 = 0x2f#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code29c : memory 0x29c#16 = 0x80#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code29d : memory 0x29d#16 = 0x00#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code29e : memory 0x29e#16 = 0xd4#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code29f : memory 0x29f#16 = 0x4f#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a0 : memory 0x2a0#16 = 0x81#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a1 : memory 0x2a1#16 = 0x6f#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a2 : memory 0x2a2#16 = 0x15#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a3 : memory 0x2a3#16 = 0x38#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a4 : memory 0x2a4#16 = 0x15#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a5 : memory 0x2a5#16 = 0x6c#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have joined : (0#8 ++ pointer) + softwareStack = softwareStack + pointer.setWidth 16 := by
    rw [BitVec.append_def, BitVec.shiftLeftZeroExtend_eq, BitVec.setWidth'_eq]
    simp [BitVec.add_comm]
  have incremented : (pointer.setWidth 16 + 1#16).setWidth 8 = pointer + 1#8 := by bv_omega
  have scratch_order : 0x100#16 + softwareStack = softwareStack + 0x100#16 := BitVec.add_comm _ _
  have code2a3_separate : 0x2a3#16 ≠ softwareStack + 0x100#16 := by bv_omega
  have code2a4_separate : 0x2a4#16 ≠ softwareStack + 0x100#16 := by bv_omega
  have code2a5_separate : 0x2a5#16 ≠ softwareStack + 0x100#16 := by bv_omega
  have data_separate : 0x2a5#16 ≠ softwareStack + pointer.setWidth 16 := by bv_omega
  iterate 15
    apply Reaches.prepend
    · simp (config := { maxSteps := 1000000 }) [uxn_state, uxn_step,
        code293, code294, code295, code296, code297, code298, code299, code29a, code29b, code29c,
        code29d, code29e, code29f, code2a0, code2a1, code2a2, code2a3, code2a4, code2a5, high, low,
        ptr, joined, incremented, scratch_order, code2a3_separate, code2a4_separate,
        code2a5_separate, data_separate]
      rfl
  refine ⟨_, .refl _, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]
  · intro address lower
    simp (disch := bv_omega) only [Function.update_of_ne]

theorem push_word (memory : Word → Byte) (softwareStack : Word) (pointer : Byte) (value : Word)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247)
    (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x2a6 (Stack.pushWord working value)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update
        (Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 2#8))
          (softwareStack + pointer.setWidth 16) ((value >>> 8).setWidth 8))
        (softwareStack + (pointer + 1#8).setWidth 16) (value.setWidth 8) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have stackAfter : 0x555 ≤ (softwareStack + 0x100#16).toNat := by bv_omega
  have dataAfter : 0x555 ≤ (softwareStack + pointer.setWidth 16).toNat := by bv_omega
  have pointerSeparate : softwareStack + 0x100#16 ≠ softwareStack + pointer.setWidth 16 := by
    bv_omega
  have separate (address : Word) (bound : address.toNat < 0x555) :
      address ≠ softwareStack + 0x100#16 ∧ address ≠ softwareStack + pointer.setWidth 16 := by
    constructor <;> bv_omega
  have outerWorking : (Stack.push working (value.setWidth 8)).ptr.toNat ≤ 248 := by
    simp only [Stack.push]
    bv_omega
  have outerReturning : (Stack.pushWord returning returnAddress).ptr.toNat ≤ 251 := by
    simp only [Stack.pushWord, Stack.push]
    bv_omega
  obtain ⟨first, firstSteps, firstPC, firstWP, firstRP, firstMem, firstWFrame, firstRFrame⟩ :=
    push_byte memory softwareStack pointer ((value >>> 8).setWidth 8)
      (Stack.push working (value.setWidth 8)) (Stack.pushWord returning returnAddress)
      0x2aa selected code high low ptr outerWorking outerReturning
  have firstCode : CodeImage first.mem.ram := by
    rw [firstMem]
    exact (code.write _ _ (.inr (.inl stackAfter))).write _ _ (.inr (.inl dataAfter))
  have firstHigh : first.mem.ram 0x40#16 = (softwareStack >>> 8).setWidth 8 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)).2,
      Function.update_of_ne (separate _ (by decide)).1, high]
  have firstLow : first.mem.ram 0x41#16 = softwareStack.setWidth 8 := by
    rw [firstMem, Function.update_of_ne (separate _ (by decide)).2,
      Function.update_of_ne (separate _ (by decide)).1, low]
  have firstPtr : first.mem.ram (softwareStack + 0x100#16) = pointer + 1#8 := by
    rw [firstMem, Function.update_of_ne pointerSeparate]
    simp
  have firstValue : first.mem.wstk.data working.ptr = value.setWidth 8 := by
    rw [firstWFrame _ (by simp only [Stack.push]; bv_omega)]
    simp [Stack.push]
  have returnHigh : first.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [firstRFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : first.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [firstRFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have workingEta :
      Stack.push { first.mem.wstk with ptr := working.ptr } (value.setWidth 8) = first.mem.wstk := by
    dsimp [Stack.push]
    rw [← firstValue, Function.update_eq_self]
    simpa [Stack.push] using congrArg (fun pointer => { first.mem.wstk with ptr := pointer }) firstWP.symm
  have returningEta : Stack.pushWord { first.mem.rstk with ptr := returning.ptr } returnAddress =
      first.mem.rstk := by
    dsimp [Stack.pushWord, Stack.push]
    rw [← returnHigh, Function.update_eq_self, ← returnLow, Function.update_eq_self]
    simpa [Stack.pushWord, Stack.push] using
      congrArg (fun pointer => { first.mem.rstk with ptr := pointer }) firstRP.symm
  obtain ⟨second, secondSteps, secondPC, secondWP, secondRP, secondMem,
      secondWFrame, secondRFrame⟩ :=
    push_byte first.mem.ram softwareStack (pointer + 1#8) (value.setWidth 8)
      { first.mem.wstk with ptr := working.ptr } { first.mem.rstk with ptr := returning.ptr }
      returnAddress selected firstCode firstHigh firstLow firstPtr (by dsimp; omega) (by dsimp; omega)
  have secondMemory : second.mem.ram = Function.update
      (Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 2#8))
        (softwareStack + pointer.setWidth 16) ((value >>> 8).setWidth 8))
      (softwareStack + (pointer + 1#8).setWidth 16) (value.setWidth 8) := by
    rw [secondMem, firstMem, Function.update_comm pointerSeparate.symm, Function.update_idem]
    simp [BitVec.add_assoc]
  have firstShape : first = machine first.mem.ram 0x2aa first.mem.wstk first.mem.rstk := by
    cases first
    simpa [machine] using firstPC
  have code2a6 : memory 0x2a6#16 = 0x04#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a7 : memory 0x2a7#16 = 0x60#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a8 : memory 0x2a8#16 = 0xff#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2a9 : memory 0x2a9#16 = 0xe9#8 :=
    code _ (by decide) (by decide) (by simp [MutableCode])
  have code2aa : first.mem.ram 0x2aa#16 = 0x40#8 :=
    firstCode _ (by decide) (by decide) (by simp [MutableCode])
  have code2ab : first.mem.ram 0x2ab#16 = 0xff#8 :=
    firstCode _ (by decide) (by decide) (by simp [MutableCode])
  have code2ac : first.mem.ram 0x2ac#16 = 0xe6#8 :=
    firstCode _ (by decide) (by decide) (by simp [MutableCode])
  have before : Reaches (machine memory 0x2a6 (Stack.pushWord working value)
      (Stack.pushWord returning returnAddress)) first := by
    refine .next (t := machine memory 0x2a7
      (Stack.push (Stack.push working (value.setWidth 8)) ((value >>> 8).setWidth 8))
      (Stack.pushWord returning returnAddress)) ?_ (.next ?_ firstSteps)
    · simp [uxn_state, uxn_step, code2a6, Function.update_comm]
    · simp [uxn_state, uxn_step, code2a7, code2a8, code2a9]
  have after : Reaches first second := by
    rw [firstShape]
    refine .next (t := machine first.mem.ram 0x293 first.mem.wstk first.mem.rstk) ?_ ?_
    · simp [uxn_state, uxn_step, code2aa, code2ab, code2ac]
    · simpa [workingEta, returningEta] using secondSteps
  refine ⟨second, before.trans after, secondPC, secondWP, secondRP, secondMemory, ?_, ?_⟩
  · intro address bound
    rw [secondWFrame _ bound, firstWFrame _ (by simp only [Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.push, Function.update_of_ne]
  · intro address bound
    rw [secondRFrame _ bound, firstRFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

theorem push_operand (memory : Word → Byte) (softwareStack : Word) (pointer : Byte)
    (value : Word) (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247)
    (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x28c (Stack.pushWord working value)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = (if short then
        Function.update
          (Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 2#8))
            (softwareStack + pointer.setWidth 16) ((value >>> 8).setWidth 8))
          (softwareStack + (pointer + 1#8).setWidth 16) (value.setWidth 8)
        else Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 1#8))
          (softwareStack + pointer.setWidth 16) (value.setWidth 8)) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code28c : memory 0x28c#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code28d : memory 0x28d#16 = 0x44#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code28e : memory 0x28e#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code28f : memory 0x28f#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code290 : memory 0x290#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code291 : memory 0x291#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code292 : memory 0x292#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  cases short with
  | false =>
    let scratch : Uxn.Stack := { working with data := Function.update (Function.update working.data (working.ptr + 1) (value.setWidth 8)) (working.ptr + 2) 0 }
    obtain ⟨final, steps, pc, wp, rp, mem, wf, rf⟩ :=
      push_byte memory softwareStack pointer (value.setWidth 8) scratch returning returnAddress
        selected code high low ptr (by change working.ptr.toNat ≤ 248; omega) (by omega)
    have header : Reaches
        (machine memory 0x28c (Stack.pushWord working value) (Stack.pushWord returning returnAddress))
        (machine memory 0x293 (Stack.push scratch (value.setWidth 8))
          (Stack.pushWord returning returnAddress)) := by
      iterate 4
        apply Reaches.next
        · simp [uxn_state, uxn_step, code28c, code28d, code28e, code28f, code290,
            code291, code292, mode]
          rfl
      convert Reaches.refl (machine memory 0x293 (Stack.push scratch (value.setWidth 8))
        (Stack.pushWord returning returnAddress)) using 1
      simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, scratch]
      congr 3
      funext address
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | exfalso; bv_omega
    refine ⟨final, header.trans steps, pc, wp, rp, mem, ?_, rf⟩
    intro address bound
    rw [wf _ bound]
    simp (disch := bv_omega) only [scratch, Function.update_of_ne]
  | true =>
    let scratch : Uxn.Stack := { working with data := Function.update working.data (working.ptr + 2) 1 }
    obtain ⟨final, steps, pc, wp, rp, mem, wf, rf⟩ :=
      push_word memory softwareStack pointer value scratch returning returnAddress
        selected code high low ptr workingSpace returnSpace
    have header : Reaches
        (machine memory 0x28c (Stack.pushWord working value) (Stack.pushWord returning returnAddress))
        (machine memory 0x2a6 (Stack.pushWord scratch value) (Stack.pushWord returning returnAddress)) := by
      iterate 3
        apply Reaches.next
        · simp [uxn_state, uxn_step, code28c, code28d, code28e, code28f, code290, code291, mode]
          rfl
      convert Reaches.refl (machine memory 0x2a6 (Stack.pushWord scratch value)
        (Stack.pushWord returning returnAddress)) using 1
      simp only [machine, Stack.pushWord, Stack.push, BitVec.add_assoc, scratch]
      congr 3
      funext address
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | exfalso; bv_omega
    refine ⟨final, header.trans steps, pc, wp, rp, mem, ?_, rf⟩
    intro address bound
    rw [wf _ bound]
    simp (disch := bv_omega) only [scratch, Function.update_of_ne]


def stackOperand (memory : Word → Byte) (softwareStack : Word) (pointer : Byte) (short : Bool) : Word :=
  (if short then memory (softwareStack + (pointer - 2#8).setWidth 16) else 0#8) ++
    memory (softwareStack + (pointer - 1#8).setWidth 16)

def storeStackOperand (memory : Word → Byte) (softwareStack : Word) (pointer : Byte)
    (value : Word) (short : Bool) : Word → Byte :=
  if short then
    Function.update
      (Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 2#8))
        (softwareStack + pointer.setWidth 16) ((value >>> 8).setWidth 8))
      (softwareStack + (pointer + 1#8).setWidth 16) (value.setWidth 8)
  else Function.update (Function.update memory (softwareStack + 0x100#16) (pointer + 1#8))
    (softwareStack + pointer.setWidth 16) (value.setWidth 8)


end ProgramProofs.Uxnmin
