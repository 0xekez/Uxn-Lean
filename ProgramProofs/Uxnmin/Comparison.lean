import Uxn.Uxn

namespace ProgramProofs.Uxnmin
open Uxn

inductive ComparisonOp where
  | equ | neq | gth | lth
  deriving DecidableEq

def ComparisonOp.guestOpcode : ComparisonOp → Byte
  | .equ => 0x08 | .neq => 0x09 | .gth => 0x0a | .lth => 0x0b

/-- Arguments follow the interpreter's pop order: first is the guest's top operand. -/
def ComparisonOp.result : ComparisonOp → Word → Word → Byte
  | .equ, first, second => if second = first then 1 else 0
  | .neq, first, second => if second ≠ first then 1 else 0
  | .gth, first, second => if first < second then 1 else 0
  | .lth, first, second => if second < first then 1 else 0


end ProgramProofs.Uxnmin
