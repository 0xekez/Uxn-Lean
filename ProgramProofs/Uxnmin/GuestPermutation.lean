import ProgramProofs.Uxnmin.GuestStack

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

inductive StackOp where
  | nip | swp | rot | dup | ovr
  deriving DecidableEq

def StackOp.opcode : StackOp → Byte
  | .nip => 3 | .swp => 4 | .rot => 5 | .dup => 6 | .ovr => 7

def stackNext (guest : Uxn.State) (operator : StackOp) (ret short keep : Bool) : Uxn.State :=
  let size := operandSize short
  let source := guestStack guest ret
  let first := operand source source.ptr short
  let second := operand source (source.ptr - size) short
  match operator with
  | .nip => pushStack (popStack { guest with pc := guest.pc + 1 } ret keep (size + size)) ret short first
  | .swp => pushStack (pushStack (popStack { guest with pc := guest.pc + 1 } ret keep
      (size + size)) ret short first) ret short second
  | .rot => pushStack (pushStack (pushStack (popStack { guest with pc := guest.pc + 1 } ret keep
      (size + size + size)) ret short second) ret short first) ret short
      (operand source (source.ptr - size - size) short)
  | .dup => pushStack (pushStack (popStack { guest with pc := guest.pc + 1 } ret keep size)
      ret short first) ret short first
  | .ovr => pushStack (pushStack (pushStack (popStack { guest with pc := guest.pc + 1 } ret keep
      (size + size)) ret short second) ret short first) ret short second

end ProgramProofs.Uxnmin
