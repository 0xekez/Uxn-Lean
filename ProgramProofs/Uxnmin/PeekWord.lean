import ProgramProofs.Uxnmin.MemoryBlocks
import ProgramProofs.Uxnmin.Embedding
import ProgramProofs.Uxnmin.Code
import ProgramProofs.Uxnmin.StackView

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The forced word reader at0x308 is independent of the guest mode byte. -/
theorem peek_word (memory : Word → Byte) (address mask returnAddress : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (workingSpace : working.ptr.toNat ≤ 250) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory 0x308 (Stack.pushWord (Stack.pushWord working address) mask)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2 ∧
      Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (memory (relocate address) ++ memory (relocate ((address + 1) &&& mask))) = final.mem.wstk ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  obtain ⟨final, steps, pc, ram, pointer, high, low, returningPointer, frame, returnFrame⟩ :=
    ProgramProofs.Uxnmin.peek_short memory address mask returnAddress working returning code
  simp only [BitVec.ofNat_eq_ofNat] at high low pointer
  have offset_eq (first second : Byte) : first + (second - first) = second := by bv_omega
  change final.mem.wstk.data working.ptr = memory (relocate address) at high
  change final.mem.wstk.data (working.ptr + 1#8) = memory (relocate ((address + 1#16) &&& mask)) at low
  refine ⟨final, steps, pc, ram, pointer, ?_, returningPointer, ?_, ?_⟩
  · simpa [pointer, BitVec.sub_eq_add_neg, BitVec.add_assoc, high, low]
      using Stack.asPushWord final.mem.wstk
  · intro index below
    have offset : 5 ≤ (index - working.ptr).toNat := by bv_omega
    simpa only [offset_eq] using frame (index - working.ptr) offset
  · intro index below
    have offset : 6 ≤ (index - returning.ptr).toNat := by bv_omega
    simpa only [offset_eq] using returnFrame (index - returning.ptr) offset

end ProgramProofs.Uxnmin
