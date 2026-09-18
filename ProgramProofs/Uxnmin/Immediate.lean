import Uxn.Uxn

namespace ProgramProofs.Uxnmin
open Uxn

inductive ImmediateKind where
  | jci | jmi | jsi | lit (short ret : Bool)
  deriving DecidableEq

def ImmediateKind.opcode : ImmediateKind → Byte
  | .jci => 0x20 | .jmi => 0x40 | .jsi => 0x60
  | .lit short ret => 0x80 + (if short then 0x20 else 0) + (if ret then 0x40 else 0)

end ProgramProofs.Uxnmin
