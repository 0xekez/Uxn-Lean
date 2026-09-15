import ProgramProofs.Host.Word

namespace ProgramProofs.Host.Stack
open Uxn

def empty : Uxn.Stack := { data := fun _ => 0, ptr := 0 }

def push (s : Uxn.Stack) (b : Byte) : Uxn.Stack :=
  { data := Function.update s.data s.ptr b, ptr := s.ptr + 1 }

def pushWord (s : Uxn.Stack) (x : Word) : Uxn.Stack :=
  push (push s ((x >>> 8).setWidth 8)) (x.setWidth 8)

end ProgramProofs.Host.Stack
