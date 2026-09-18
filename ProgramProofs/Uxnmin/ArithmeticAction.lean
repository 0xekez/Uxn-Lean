import ProgramProofs.Uxnmin.BinaryAction
import ProgramProofs.Uxnmin.Arithmetic
import ProgramProofs.Uxnmin.OpcodeModes

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def ArithmeticOp.operation : ArithmeticOp → Uxn.Op
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div
  | .and => .and | .ora => .ora | .eor => .eor

def ArithmeticOp.combine : ArithmeticOp → Word → Word → Word
  | .add, first, second => first + second
  | .sub, first, second => second - first
  | .mul, first, second => first * second
  | .div, first, second => second / first
  | .and, first, second => first &&& second
  | .ora, first, second => first ||| second
  | .eor, first, second => first ^^^ second

/-- Opcode dispatch selects a common arithmetic stack action. -/
theorem arithmetic_action (operator : ArithmeticOp) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode) :
    Uxn.step guest = (binaryAction
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
