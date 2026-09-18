import ProgramProofs.Uxnmin.GuestStack
import ProgramProofs.Uxnmin.Comparison
import ProgramProofs.Uxnmin.OpcodeModes

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def comparisonAction (mode : Mode) (combine : Word → Word → Byte) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    let first ← ops.dec
    let second ← ops.dec
    ops.inc8 (combine first second)
    return .done (.next (← get))

def comparisonResult (guest : Uxn.State) (ret short keep : Bool)
    (combine : Word → Word → Byte) : Uxn.State :=
  pushStack (popStack guest ret keep (operandSize short + operandSize short)) ret false
    ((combine (operand (guestStack guest ret) (guestStack guest ret).ptr short)
      (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short)).setWidth 16)

/-- Comparison pops two operands but always pushes one byte. -/
theorem comparison_stack_action (guest : Uxn.State) (ret short keep : Bool)
    (combine : Word → Word → Byte) :
    (comparisonAction ⟨short, keep, ret⟩ combine guest).fst =
      .done (.next (comparisonResult guest ret short keep combine)) := by
  let decrement (pointer : Byte) (short : Bool) := if short then pointer - 1 - 1 else pointer - 1
  let rawOperand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :=
    if short then (stack.data (pointer - 1)).setWidth 16 |||
      (stack.data (pointer - 1 - 1)).setWidth 16 <<< 8
    else (stack.data (pointer - 1)).setWidth 16
  let rawResult (guest : Uxn.State) (ret short keep : Bool) (combine : Word → Word → Byte) :=
    let source := guestStack guest ret
    setStack guest ret (Stack.push
      (if keep then source else { source with ptr := decrement (decrement source.ptr short) short })
      (combine (rawOperand source source.ptr short)
        (rawOperand source (decrement source.ptr short) short)))
  have execute (guest : Uxn.State) (ret short keep : Bool) (combine : Word → Word → Byte) :
      (comparisonAction ⟨short, keep, ret⟩ combine guest).fst =
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
    simp [comparisonResult, guestStack, setStack, popStack, pushStack, operandSize,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

def ComparisonOp.operation : ComparisonOp → Uxn.Op
  | .equ => .equ | .neq => .neq | .gth => .gth | .lth => .lth

def ComparisonOp.combine : ComparisonOp → Word → Word → Byte
  | .equ, first, second => if first == second then 1 else 0
  | .neq, first, second => if first != second then 1 else 0
  | .gth, first, second => if first < second then 1 else 0
  | .lth, first, second => if first > second then 1 else 0

/-- The four comparison opcodes select the common byte-producing action. -/
theorem comparison_action (operator : ComparisonOp) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode) :
    Uxn.step guest = (comparisonAction
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ operator.combine
      { guest with pc := guest.pc + 1 }).fst := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = operator.guestOpcode) :
      Instruction.ofByte byte = .normal operator.operation
        ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte _ (by cases operator <;> decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;>
      subst byte <;> cases operator <;> rfl
  dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
  rw [decoded _ opcode]
  cases operator <;> rfl

end ProgramProofs.Uxnmin
