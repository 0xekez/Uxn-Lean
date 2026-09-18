import Uxn.Uxn

namespace ProgramProofs.Uxnmin
open Uxn

inductive ArithmeticOp where
  | add | sub | mul | div | and | ora | eor
  deriving DecidableEq

def ArithmeticOp.guestOpcode : ArithmeticOp → Byte
  | .add => 0x18 | .sub => 0x19 | .mul => 0x1a | .div => 0x1b
  | .and => 0x1c | .ora => 0x1d | .eor => 0x1e

/-- Arguments follow pop order: the first operand is initially on top. -/
def ArithmeticOp.result : ArithmeticOp → Word → Word → Word
  | .add, first, second => second + first
  | .sub, first, second => second - first
  | .mul, first, second => second * first
  | .div, first, second => second / first
  | .and, first, second => second &&& first
  | .ora, first, second => second ||| first
  | .eor, first, second => second ^^^ first

end ProgramProofs.Uxnmin
