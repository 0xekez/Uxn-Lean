import ProgramProofs.Uxnmin.GuestPermutation
import ProgramProofs.Uxnmin.NipHandler
import ProgramProofs.Uxnmin.RotHandler
import ProgramProofs.Uxnmin.OvrHandler

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def StackOp.entry : StackOp → Word
  | .nip => 0x3c0 | .swp => 0x3ca | .rot => 0x3d7 | .dup => 0x3eb | .ovr => 0x3f5

def StackOp.poppedPointer (operator : StackOp) (pointer : Byte) (short : Bool) : Byte :=
  match operator with
  | .dup => pointer - operandSize short
  | .rot => pointer - operandSize short - operandSize short - operandSize short
  | _ => pointer - operandSize short - operandSize short

def StackOp.memory (operator : StackOp) (memory : Word → Byte) (base : Word)
    (pointer keep : Byte) (short : Bool) : Word → Byte :=
  let size := operandSize short
  let popped := Function.update memory (base + (0x100#16 + keep.setWidth 16))
    (operator.poppedPointer pointer short)
  let position := if keep = 0 then operator.poppedPointer pointer short else pointer
  let first := stackOperand memory base pointer short
  let second := stackOperand memory base (pointer - size) short
  match operator with
  | .nip => storeStackOperand popped base position first short
  | .swp => storeStackOperand (storeStackOperand popped base position first short)
      base (position + size) second short
  | .rot => storeStackOperand
      (storeStackOperand (storeStackOperand popped base position second short)
        base (position + size) first short)
      base (position + size + size)
      (stackOperand memory base (pointer - size - size) short) short
  | .dup => storeStackOperand (storeStackOperand popped base position first short)
      base (position + size) first short
  | .ovr => storeStackOperand
      (storeStackOperand (storeStackOperand popped base position second short)
        base (position + size) first short)
      base (position + size + size) second short

/-- The five stack-permutation handlers share this exact native contract. -/
theorem handler_stack (operator : StackOp) (memory : Word → Byte) (softwareStack : Word)
    (pointer keep : Byte) (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (kept : memory 0x2bf#16 = keep) (keepBound : keep.toNat ≤ 1)
    (cursor : memory (softwareStack + (0x100#16 + keep.setWidth 16)) = pointer)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 243) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches (machine memory operator.entry working (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = operator.memory memory softwareStack pointer keep short ∧
      CodeImage final.mem.ram ∧
      (∀ address : Byte, address.toNat < working.ptr.toNat →
        final.mem.wstk.data address = working.data address) ∧
      (∀ address : Byte, address.toNat < returning.ptr.toNat →
        final.mem.rstk.data address = returning.data address) := by
  cases operator with
  | nip =>
    simpa only [StackOp.entry, StackOp.memory, StackOp.poppedPointer, operandSize, BitVec.ofNat_eq_ofNat] using
      handler_nip memory softwareStack pointer keep short working returning returnAddress
        selected code high low mode kept keepBound cursor ptr (by omega) returnSpace
  | swp =>
    simpa only [StackOp.entry, StackOp.memory, StackOp.poppedPointer, operandSize, BitVec.ofNat_eq_ofNat] using
      handler_swp memory softwareStack pointer keep short working returning returnAddress
        selected code high low mode kept keepBound cursor ptr (by omega) returnSpace
  | rot =>
    simpa only [StackOp.entry, StackOp.memory, StackOp.poppedPointer, operandSize, BitVec.ofNat_eq_ofNat] using
      handler_rot memory softwareStack pointer keep short working returning returnAddress
        selected code high low mode kept keepBound cursor ptr workingSpace returnSpace
  | dup =>
    simpa only [StackOp.entry, StackOp.memory, StackOp.poppedPointer, operandSize, BitVec.ofNat_eq_ofNat] using
      handler_dup memory softwareStack pointer keep short working returning returnAddress
        selected code high low mode kept keepBound cursor ptr (by omega) returnSpace
  | ovr =>
    simpa only [StackOp.entry, StackOp.memory, StackOp.poppedPointer, operandSize, BitVec.ofNat_eq_ofNat] using
      handler_ovr memory softwareStack pointer keep short working returning returnAddress
        selected code high low mode kept keepBound cursor ptr workingSpace returnSpace

end ProgramProofs.Uxnmin
