import ProgramProofs.Uxnmin.PopHandler

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The forced-byte pop entry does not consult the instruction's short flag. -/
theorem pop_byte_operand (memory : Word → Byte) (softwareStack : Word) (pointer keep : Byte)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (ptr : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 251) :
    ∃ final, Reaches
      (machine memory 0x2b3 working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.wstk.data working.ptr = 0 ∧
      final.mem.wstk.data (working.ptr + 1#8) = memory (softwareStack + (pointer - 1#8).setWidth 16) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update memory
        (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - 1#8) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  have code2b3 : memory 0x2b3#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have code2b4 : memory 0x2b4#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  obtain ⟨final, steps, pc, wp, value, rp, mem, wf, rf⟩ :=
    pop_byte memory softwareStack pointer keep (Stack.push working 0) returning returnAddress
      selected code high low kept keepBound ptr
      (by simp only [Stack.push]; bv_omega) returnSpace
  have header : Reaches (machine memory 0x2b3 working (Stack.pushWord returning returnAddress))
      (machine memory 0x2b5 (Stack.push working 0) (Stack.pushWord returning returnAddress)) := by
    refine .next ?_ (.refl _)
    simp [uxn_state, uxn_step, code2b3, code2b4]
  refine ⟨final, header.trans steps, pc, ?_, ?_, ?_, rp, mem, ?_, rf⟩
  · simpa [Stack.push, BitVec.add_assoc] using wp
  · rw [wf _ (by simp only [Stack.push]; bv_omega)]
    simp [Stack.push]
  · simpa [Stack.push] using value
  · intro address bound
    rw [wf _ (by simp only [Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.push, Function.update_of_ne]


inductive OperandKind where
  | mode | byte | word
  deriving DecidableEq

def OperandKind.entry : OperandKind → Word
  | .mode => 0x2ad | .byte => 0x2b3 | .word => 0x2d0

def OperandKind.short : OperandKind → Bool → Bool
  | .mode, short => short
  | .byte, _ => false
  | .word, _ => true

theorem pop_operand_kind (kind : OperandKind) (memory : Word → Byte) (softwareStack : Word)
    (pointer keep : Byte) (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (ptr : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory kind.entry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.wstk.data working.ptr =
        (if kind.short short then memory (softwareStack + (pointer - 2#8).setWidth 16) else 0) ∧
      final.mem.wstk.data (working.ptr + 1#8) = memory (softwareStack + (pointer - 1#8).setWidth 16) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = Function.update memory
        (softwareStack + (0x100#16 + keep.setWidth 16)) (pointer - (if kind.short short then 2#8 else 1#8)) ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  cases kind with
  | mode =>
    exact pop_operand memory softwareStack pointer keep short working returning returnAddress
      selected code high low mode kept keepBound ptr workingSpace returnSpace
  | byte =>
    exact pop_byte_operand memory softwareStack pointer keep working returning returnAddress
      selected code high low kept keepBound ptr workingSpace (by omega)
  | word =>
    exact pop_word memory softwareStack pointer keep working returning returnAddress
      selected code high low kept keepBound ptr workingSpace returnSpace

end ProgramProofs.Uxnmin
