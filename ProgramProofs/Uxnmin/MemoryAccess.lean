import ProgramProofs.Uxnmin.GuestStack

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

inductive AddressMode where
  | zero | relative | absolute
  deriving DecidableEq

def AddressMode.loadOpcode : AddressMode → Byte
  | .zero => 0x10 | .relative => 0x12 | .absolute => 0x14

def AddressMode.loadOperation : AddressMode → Uxn.Op
  | .zero => .ldz | .relative => .ldr | .absolute => .lda

def AddressMode.address (kind : AddressMode) (guest : Uxn.State) (ret : Bool) : Word :=
  match kind with
  | .zero => ((guestStack guest ret).data ((guestStack guest ret).ptr - 1)).setWidth 16
  | .relative => guest.pc + ((guestStack guest ret).data ((guestStack guest ret).ptr - 1)).signExtend 16
  | .absolute => operand (guestStack guest ret) (guestStack guest ret).ptr true

def AddressMode.following : AddressMode → Word → Word
  | .zero, address => (address.setWidth 8 + 1#8).setWidth 16
  | _, address => address + 1

def AddressMode.consumed : AddressMode → Byte
  | .absolute => 2
  | _ => 1

end ProgramProofs.Uxnmin
