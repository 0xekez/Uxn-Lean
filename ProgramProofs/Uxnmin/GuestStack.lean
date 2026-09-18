import ProgramProofs.Uxnmin.RepresentationPop

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def operandSize (short : Bool) : Byte := if short then 2 else 1

def operand (stack : Uxn.Stack) (pointer : Byte) (short : Bool) : Word :=
  (if short then stack.data (pointer - 2) else 0) ++ stack.data (pointer - 1)

def pushStack (guest : Uxn.State) (ret short : Bool) (value : Word) : Uxn.State :=
  if ret then { guest with mem.rstk := (
    if short then Stack.pushWord guest.mem.rstk value
    else Stack.push guest.mem.rstk (value.setWidth 8)) }
  else { guest with mem.wstk := (
    if short then Stack.pushWord guest.mem.wstk value
    else Stack.push guest.mem.wstk (value.setWidth 8)) }


def setStack (guest : Uxn.State) (ret : Bool) (stack : Uxn.Stack) : Uxn.State :=
  if ret then { guest with mem.rstk := stack } else { guest with mem.wstk := stack }

@[simp] theorem guestStack_setStack (guest : Uxn.State) (ret : Bool) (stack : Uxn.Stack) :
    guestStack (setStack guest ret stack) ret = stack := by cases ret <;> rfl

@[simp] theorem setStack_guestStack (guest : Uxn.State) (ret : Bool) :
    setStack guest ret (guestStack guest ret) = guest := by cases ret <;> rfl

@[simp] theorem setStack_setStack (guest : Uxn.State) (ret : Bool) (first second : Uxn.Stack) :
    setStack (setStack guest ret first) ret second = setStack guest ret second := by cases ret <;> rfl

@[simp] theorem guestStack_pc (guest : Uxn.State) (pc : Word) (ret : Bool) :
    guestStack { guest with pc } ret = guestStack guest ret := by cases ret <;> rfl

@[simp] theorem popStack_pointer (guest : Uxn.State) (ret keep : Bool) (amount : Byte) :
    (guestStack (popStack guest ret keep amount) ret).ptr =
      if keep then (guestStack guest ret).ptr else (guestStack guest ret).ptr - amount := by
  cases ret <;> cases keep <;> rfl

end ProgramProofs.Uxnmin
