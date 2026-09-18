import ProgramProofs.Uxnmin.OperandPair

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def PopPairCode (entry : Word) : Prop :=
  ∀ (memory : Word → Byte) (working returning : Uxn.Stack) (offset : Word),
    CodeImage memory → (offset = 0 ∨ offset = 3) →
    Uxn.step (machine memory (entry + offset) working returning) = .done (.next
      (machine memory 0x2ad working (Stack.pushWord returning (entry + offset + 3))))

theorem pop_pair (entry : Word) (calls : PopPairCode entry) (memory : Word → Byte)
    (softwareStack : Word) (pointer keep : Byte) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247)
    (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory entry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = entry + 6 ∧
      final.mem.ram = Function.update memory (softwareStack + (0x100#16 + keep.setWidth 16))
        (pointer - (if short then 2#8 else 1#8) - (if short then 2#8 else 1#8)) ∧
      CodeImage final.mem.ram ∧
      final.mem.wstk.ptr = working.ptr + 4#8 ∧
      final.mem.rstk.ptr = returning.ptr + 2#8 ∧
      Stack.pushWord (Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (stackOperand memory softwareStack pointer short))
        (stackOperand memory softwareStack (pointer - (if short then 2#8 else 1#8)) short) = final.mem.wstk ∧
      Stack.pushWord { final.mem.rstk with ptr := returning.ptr } returnAddress = final.mem.rstk ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  simpa [OperandKind.short] using
    pop_operand_pair .mode .mode entry
      (fun ram w r offset image position => by
        simpa [OperandKind.entry] using calls ram w r offset image position)
      memory softwareStack pointer keep short working returning returnAddress selected code high low mode
      kept keepBound cursor workingSpace returnSpace

end ProgramProofs.Uxnmin
