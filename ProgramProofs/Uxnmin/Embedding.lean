import ProgramProofs.Uxnmin.Rom
namespace ProgramProofs.Uxnmin
open Uxn
def ramBase : Nat := 0x0859
def relocate (address : Word) : Word := 0x0859 + address
end ProgramProofs.Uxnmin
