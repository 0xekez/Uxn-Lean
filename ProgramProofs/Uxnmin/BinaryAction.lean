import ProgramProofs.Uxnmin.GuestStack

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def binaryAction (mode : Mode) (combine : Word → Word → Word) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    let first ← ops.dec
    let second ← ops.dec
    ops.inc (combine first second)
    return .done (.next (← get))

def binaryResult (guest : Uxn.State) (ret short keep : Bool) (combine : Word → Word → Word) : Uxn.State :=
  pushStack (popStack guest ret keep (operandSize short + operandSize short)) ret short
    (combine (operand (guestStack guest ret) (guestStack guest ret).ptr short)
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short))

/-- The common pop-pop-push action, independently of its arithmetic operation. -/
theorem binary_action (guest : Uxn.State) (ret short keep : Bool) (combine : Word → Word → Word) :
    (binaryAction ⟨short, keep, ret⟩ combine guest).fst =
      .done (.next (binaryResult guest ret short keep combine)) := by
  let decrement (pointer : Byte) (short : Bool) := if short then pointer - 1 - 1 else pointer - 1
  let rawOperand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :=
    if short then (stack.data (pointer - 1)).setWidth 16 |||
      (stack.data (pointer - 1 - 1)).setWidth 16 <<< 8
    else (stack.data (pointer - 1)).setWidth 16
  let rawResult (guest : Uxn.State) (ret short keep : Bool) (combine : Word → Word → Word) :=
    let source := guestStack guest ret
    pushStack (if keep then guest else setStack guest ret
      { source with ptr := decrement (decrement source.ptr short) short }) ret short
      (combine (rawOperand source source.ptr short)
        (rawOperand source (decrement source.ptr short) short))
  have execute (guest : Uxn.State) (ret short keep : Bool) (combine : Word → Word → Word) :
      (binaryAction ⟨short, keep, ret⟩ combine guest).fst =
        .done (.next (rawResult guest ret short keep combine)) := by
    as_aux_lemma =>
      cases ret <;> cases short <;> cases keep <;> rfl
  have decrement_eq (pointer : Byte) (short : Bool) :
      decrement pointer short = pointer - operandSize short := by
    cases short <;> simp [decrement, operandSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have operand_eq (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :
      rawOperand stack pointer short = operand stack pointer short := by
    cases short <;>
      simp [rawOperand, operand, ← join_bytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [execute]
  congr 2
  simp only [rawResult, operand_eq, decrement_eq]
  cases ret <;> cases short <;> cases keep <;>
    simp [binaryResult, guestStack, setStack, popStack, operandSize,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

end ProgramProofs.Uxnmin
