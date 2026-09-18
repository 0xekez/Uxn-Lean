import ProgramProofs.Uxnmin.MemoryAccess
import ProgramProofs.Uxnmin.MixedOperands

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def AddressMode.mask : AddressMode → Word
  | .zero => 0x00ff | _ => 0xffff

def AddressMode.operandKind : AddressMode → OperandKind
  | .absolute => .word | _ => .byte

def AddressMode.nativeAddress (kind : AddressMode) (pc value : Word) : Word :=
  if kind = .relative then pc + (value.setWidth 8).signExtend 16 else value

/-- The native addressing mask implements the guest's second-byte address. -/
theorem AddressMode.following_mask (kind : AddressMode) (address : Word) :
    (address + 1#16) &&& kind.mask = kind.following address := by
  cases kind with
  | relative | absolute => exact BitVec.and_allOnes
  | zero =>
    change (address + 1) &&& (BitVec.allOnes 8).setWidth 16 = _
    rw [BitVec.and_setWidth_allOnes 8 8]
    have widen (byte : Byte) : 0#8 ++ byte = byte.setWidth 16 := by
      simpa using (join_bytes 0#8 byte).symm
    rw [widen, BitVec.setWidth_add _ _ (by decide)]
    rfl

end ProgramProofs.Uxnmin
