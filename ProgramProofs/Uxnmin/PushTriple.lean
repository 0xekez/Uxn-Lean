import ProgramProofs.Uxnmin.StackHandlers

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

inductive TriplePushSite where
  | rot | ovr
  deriving DecidableEq

def TriplePushSite.pc : TriplePushSite → Word
  | .rot => 0x3e2 | .ovr => 0x3fd

theorem push_triple (site : TriplePushSite) (memory : Word → Byte) (softwareStack : Word)
    (pointer : Byte) (first second third : Word) (short : Bool) (working returning : Uxn.Stack)
    (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 243) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory site.pc (Stack.pushWord (Stack.pushWord (Stack.pushWord working first) second) third)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand
        (storeStackOperand (storeStackOperand memory softwareStack pointer third short) softwareStack
          (pointer + (if short then 2#8 else 1#8)) second short) softwareStack
        (pointer + (if short then 2#8 else 1#8) + (if short then 2#8 else 1#8)) first short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨middle, firstSteps, firstPC, firstWP, firstRP, firstMem, firstWF, firstRF⟩ :=
    push_operand memory softwareStack pointer third short (Stack.pushWord (Stack.pushWord working first) second)
      (Stack.pushWord returning returnAddress) (site.pc + 3) selected code high low mode ptr
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have firstCall : memory site.pc = 0x60#8 := by
    cases site <;> exact code _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
  have firstOffset : memory (site.pc + 1) ++ memory (site.pc + 2) = 0x28c - (site.pc + 3) := by
    have hi : memory (site.pc + 1) = ((0x28c - (site.pc + 3)) >>> 8).setWidth 8 := by
      cases site <;> exact code _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
    have lo : memory (site.pc + 2) = (0x28c - (site.pc + 3)).setWidth 8 := by
      cases site <;> exact code _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
    rw [hi, lo, append_split]
  have before : Reaches
      (machine memory site.pc (Stack.pushWord (Stack.pushWord (Stack.pushWord working first) second) third)
        (Stack.pushWord returning returnAddress)) middle :=
    .next (jsi_call _ _ _ _ _ firstCall firstOffset) firstSteps
  have middleMem : middle.mem.ram = storeStackOperand memory softwareStack pointer third short := firstMem
  have middleCode : CodeImage middle.mem.ram := by
    rw [middleMem]
    exact store_operand_code _ _ _ _ _ selected code
  have reads (address : Word) (bound : address.toNat < 0x555) :
      middle.mem.ram address = memory address := by
    rw [middleMem]
    exact store_operand_frame _ _ _ _ _ selected address bound
  have middlePointer : middle.mem.ram (softwareStack + 0x100#16) =
      pointer + (if short then 2#8 else 1#8) := by
    rw [middleMem]
    exact store_operand_pointer _ _ _ _ _
  have nativeWP : middle.mem.wstk.ptr = working.ptr + 4#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using firstWP
  have nativeRP : middle.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using firstRP
  have workFirstHigh : middle.mem.wstk.data working.ptr = (first >>> 8).setWidth 8 := by
    rw [firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have workFirstLow : middle.mem.wstk.data (working.ptr + 1#8) = first.setWidth 8 := by
    rw [firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have workSecondHigh : middle.mem.wstk.data (working.ptr + 2#8) = (second >>> 8).setWidth 8 := by
    rw [firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have workSecondLow : middle.mem.wstk.data (working.ptr + 3#8) = second.setWidth 8 := by
    rw [firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push, BitVec.add_assoc]
  have returnHigh : middle.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : middle.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have workingEta : Stack.pushWord (Stack.pushWord { middle.mem.wstk with ptr := working.ptr } first) second = middle.mem.wstk := by
    simpa [nativeWP, workFirstHigh, workFirstLow, workSecondHigh, workSecondLow,
      BitVec.sub_eq_add_neg, BitVec.add_assoc, append_split] using Stack.asPushPair middle.mem.wstk
  have returningEta : Stack.pushWord { middle.mem.rstk with ptr := returning.ptr } returnAddress = middle.mem.rstk := by
    simpa [nativeRP, returnHigh, returnLow, BitVec.sub_eq_add_neg, BitVec.add_assoc, append_split]
      using Stack.asPushWord middle.mem.rstk
  have nextCall : middle.mem.ram (site.pc + 3) = 0x60#8 := by
    cases site <;> exact middleCode _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
  have nextOffset : middle.mem.ram ((site.pc + 3) + 1) ++ middle.mem.ram ((site.pc + 3) + 2) =
      0x28c - ((site.pc + 3) + 3) := by
    have hi : middle.mem.ram ((site.pc + 3) + 1) = ((0x28c - ((site.pc + 3) + 3)) >>> 8).setWidth 8 := by
      cases site <;> exact middleCode _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
    have lo : middle.mem.ram ((site.pc + 3) + 2) = (0x28c - ((site.pc + 3) + 3)).setWidth 8 := by
      cases site <;> exact middleCode _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
    rw [hi, lo, append_split]
  have nextJump : middle.mem.ram ((site.pc + 3) + 3) = 0x40#8 := by
    cases site <;> exact middleCode _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
  have jumpOffset : middle.mem.ram ((site.pc + 3) + 4) ++ middle.mem.ram ((site.pc + 3) + 5) =
      0x28c - ((site.pc + 3) + 6) := by
    have hi : middle.mem.ram ((site.pc + 3) + 4) = ((0x28c - ((site.pc + 3) + 6)) >>> 8).setWidth 8 := by
      cases site <;> exact middleCode _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
    have lo : middle.mem.ram ((site.pc + 3) + 5) = (0x28c - ((site.pc + 3) + 6)).setWidth 8 := by
      cases site <;> exact middleCode _ (by decide) (by decide) (by simp [TriplePushSite.pc, MutableCode])
    rw [hi, lo, append_split]
  obtain ⟨final, lastSteps, finalPC, finalWP, finalRP, finalMem, finalCode, finalWF, finalRF⟩ :=
    push_pair middle.mem.ram softwareStack (pointer + (if short then 2#8 else 1#8))
      first second short { middle.mem.wstk with ptr := working.ptr } { middle.mem.rstk with ptr := returning.ptr }
      returnAddress (site.pc + 3) selected middleCode
      (by rw [reads _ (by decide), high]) (by rw [reads _ (by decide), low])
      (by rw [reads _ (by decide), mode]) middlePointer nextCall nextOffset nextJump jumpOffset
      (by cases site <;> decide) (by cases site <;> decide) (by dsimp; omega) (by dsimp; omega)
  have shape : middle = machine middle.mem.ram (site.pc + 3) middle.mem.wstk middle.mem.rstk := by
    cases middle
    simpa [machine] using firstPC
  have after : Reaches middle final := by
    rw [shape]
    simpa only [workingEta, returningEta] using lastSteps
  refine ⟨final, before.trans after, finalPC, finalWP, finalRP, ?_, finalCode, ?_, ?_⟩
  · rw [finalMem, middleMem]
  · intro address bound
    rw [finalWF _ bound, firstWF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  · intro address bound
    rw [finalRF _ bound, firstRF _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
