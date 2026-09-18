import ProgramProofs.Uxnmin.Code
import ProgramProofs.Uxnmin.Embedding
import ProgramProofs.Host.Execution

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def stackBase (ret : Bool) : Word := if ret then 0x657 else 0x555

def guestStack (guest : Uxn.State) (ret : Bool) : Uxn.Stack :=
  if ret then guest.mem.rstk else guest.mem.wstk

structure Represents (guest outer : Uxn.State) : Prop where
  code : CodeImage outer.mem.ram
  ram : ∀ address : Word, address.toNat < ramSize →
    outer.mem.ram (relocate address) = guest.mem.ram address
  stackData : ∀ (ret : Bool) (index : Byte),
    outer.mem.ram (stackBase ret + index.setWidth 16) = (guestStack guest ret).data index
  stackPointer : ∀ ret : Bool,
    outer.mem.ram (stackBase ret + 0x100) = (guestStack guest ret).ptr
  pcHigh : outer.mem.ram 0x45 = (guest.pc >>> 8).setWidth 8
  pcLow : outer.mem.ram 0x46 = guest.pc.setWidth 8

structure EvaluationBoundary (guest outer : Uxn.State) : Prop extends Represents guest outer where
  pc : outer.pc = 0x16d
  workingEmpty : outer.mem.wstk.ptr = 0
  returnSpace : outer.mem.rstk.ptr.toNat ≤ 245

-- POP leaves all native device bookkeeping intact.
def PopScratch (address : Word) : Prop :=
  address ∈ [0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x2bf, 0x655, 0x656, 0x757, 0x758]

end ProgramProofs.Uxnmin
