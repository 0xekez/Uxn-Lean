import ProgramProofs.Host.Memory
import ProgramProofs.Host.Stack

/-- Explicit rules for unfolding state computations without changing global `[simp]`. -/
register_simp_attr uxn_state
/-- Explicit VM and stack rules for symbolic instruction execution. -/
register_simp_attr uxn_step

namespace ProgramProofs.Host
open Uxn Uxn.Host

def machine (ram : Word → Byte) (pc : Word) (w r : Uxn.Stack) : Uxn.State :=
  { pc, mem := { ram, wstk := w, rstk := r } }

theorem initial_shape (source : ByteArray) :
    ({ vm := machine (initialState source).vm.mem.ram 0 Stack.empty Stack.empty } :
      Uxn.Host.State) = initialState source := by
  simp only [machine, Stack.empty, initialState]

end ProgramProofs.Host
