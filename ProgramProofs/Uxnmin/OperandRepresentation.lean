import ProgramProofs.Uxnmin.RepresentationStack
import ProgramProofs.Uxnmin.PushOperand

namespace ProgramProofs.Uxnmin
open Uxn

theorem Represents.operand {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret short : Bool) (pointer : Byte) :
    stackOperand outer.mem.ram (stackBase ret) pointer short =
      operand (guestStack guest ret) pointer short := by
  simp only [stackOperand, ProgramProofs.Uxnmin.operand, rep.stackData]
  rfl

theorem Represents.storeOperand {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret short : Bool) (value : Word) :
    Represents (ProgramProofs.Uxnmin.pushStack guest ret short value)
      { outer with mem.ram := storeStackOperand outer.mem.ram (stackBase ret) (guestStack guest ret).ptr value short } :=
  rep.pushStack ret short value

end ProgramProofs.Uxnmin
