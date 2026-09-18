import ProgramProofs.Uxnmin.GuestPermutation
import ProgramProofs.Uxnmin.OpcodeModes

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def StackOp.operation : StackOp → Uxn.Op
  | .nip => .nip | .swp => .swp | .rot => .rot | .dup => .dup | .ovr => .ovr

def stackAction (operator : StackOp) (mode : Mode) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    match operator with
    | .nip =>
      let first ← ops.dec
      discard ops.dec
      ops.inc first
    | .swp =>
      let first ← ops.dec
      let second ← ops.dec
      ops.inc first
      ops.inc second
    | .rot =>
      let first ← ops.dec
      let second ← ops.dec
      let third ← ops.dec
      ops.inc second
      ops.inc first
      ops.inc third
    | .dup =>
      let first ← ops.dec
      ops.inc first
      ops.inc first
    | .ovr =>
      let first ← ops.dec
      let second ← ops.dec
      ops.inc second
      ops.inc first
      ops.inc second
    return .done (.next (← get))

def decrement (pointer : Byte) (short : Bool) := if short then pointer - 1 - 1 else pointer - 1
def rawOperand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) :=
  if short then (stack.data (pointer - 1)).setWidth 16 |||
    (stack.data (pointer - 1 - 1)).setWidth 16 <<< 8
  else (stack.data (pointer - 1)).setWidth 16
def rawNext (guest : Uxn.State) (operator : StackOp) (ret short keep : Bool) :=
  let source := guestStack guest ret
  let one := decrement source.ptr short
  let two := decrement one short
  let three := decrement two short
  let first := rawOperand source source.ptr short
  let second := rawOperand source one short
  let third := rawOperand source two short
  let popped : Uxn.Stack := { source with
    ptr := if keep then source.ptr else match operator with | .dup => one | .rot => three | _ => two }
  let push (stack : Uxn.Stack) (value : Word) :=
    if short then Stack.pushWord stack value else Stack.push stack (value.setWidth 8)
  setStack guest ret (match operator with
  | .nip => push popped first
  | .swp => push (push popped first) second
  | .rot => push (push (push popped second) first) third
  | .dup => push (push popped first) first
  | .ovr => push (push (push popped second) first) second)


end ProgramProofs.Uxnmin
