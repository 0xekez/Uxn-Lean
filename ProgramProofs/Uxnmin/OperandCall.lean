import ProgramProofs.Uxnmin.OperandPair

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def OperandCallCode (entry : Word) (kind : OperandKind) : Prop :=
  ∀ (memory : Word → Byte) (working returning : Uxn.Stack),
    CodeImage memory →
    Uxn.step (machine memory entry working returning) = .done (.next
      (machine memory kind.entry working (Stack.pushWord returning (entry + 3))))

theorem pop_call_operand (kind : OperandKind)
    (entry : Word) (calls : OperandCallCode entry kind) (memory : Word → Byte)
    (softwareStack : Word) (pointer keep : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 249)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory entry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = entry + 3 ∧
      final.mem.ram = Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
        (pointer - (if kind.short short then 2#8 else 1#8)) ∧
      CodeImage final.mem.ram ∧
      final.mem.wstk.ptr = working.ptr + 2#8 ∧
      final.mem.rstk.ptr = returning.ptr + 2#8 ∧
      Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (stackOperand memory softwareStack pointer (kind.short short)) = final.mem.wstk ∧
      Stack.pushWord { final.mem.rstk with ptr := returning.ptr } returnAddress = final.mem.rstk ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  obtain ⟨final, steps, pc, wp, vh, vl, rp, ram, wf, rf⟩ :=
    pop_operand_kind kind memory softwareStack pointer keep short working
      (Stack.pushWord returning returnAddress) (entry + 3) selected code high low mode kept keepBound cursor
      workingSpace (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have finalCode : CodeImage final.mem.ram := by
    rw [ram]
    apply code.write
    right; left
    rcases selected with rfl | rfl <;> bv_omega
  have workingEta : Stack.pushWord { final.mem.wstk with ptr := working.ptr }
      (stackOperand memory softwareStack pointer (kind.short short)) = final.mem.wstk := by
    simpa [wp, BitVec.sub_eq_add_neg, BitVec.add_assoc, vh, vl, stackOperand]
      using Stack.asPushWord final.mem.wstk
  have returningPointer : final.mem.rstk.ptr = returning.ptr + 2#8 := by
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using rp
  have returnHigh : final.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : final.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returningEta : Stack.pushWord { final.mem.rstk with ptr := returning.ptr } returnAddress = final.mem.rstk := by
    simpa [returningPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, returnHigh, returnLow, append_split]
      using Stack.asPushWord final.mem.rstk
  refine ⟨final, .next (calls memory working (Stack.pushWord returning returnAddress) code) steps,
    pc, ram, finalCode, wp, returningPointer, workingEta, returningEta, wf, ?_⟩
  intro address bound
  rw [rf _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
  simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
