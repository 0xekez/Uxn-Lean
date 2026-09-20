import ProgramProofs.Uxnmin.Rom
import ProgramProofs.Host.Memory

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

private def writeName : List UInt8 → Nat → (Word → Byte) → Word → Byte
  | [], _, ram => ram
  | byte :: bytes, offset, ram =>
      writeName bytes (offset + 1) (Function.update ram (BitVec.ofNat 16 offset) byte.toBitVec)

end ProgramProofs.Uxnmin
