import ProgramProofs.Host.Reduction
import ProgramProofs.Host.Stack
import Mathlib.Tactic.SplitIfs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Host
open Uxn

theorem native_swp (memory : Word → Byte) (pc first second : Word)
    (working returning : Uxn.Stack) (instruction : memory pc = 0x24) :
    Uxn.step (machine memory pc (Stack.pushWord (Stack.pushWord working first) second) returning) =
      .done (.next (machine memory (pc + 1) (Stack.pushWord (Stack.pushWord working second) first) returning)) := by
  simp [uxn_state, uxn_step, instruction, append_split]
  funext address
  simp only [Function.update_apply]
  split_ifs <;> rfl

theorem native_rot (memory : Word → Byte) (pc first second third : Word)
    (working returning : Uxn.Stack) (instruction : memory pc = 0x25) :
    Uxn.step (machine memory pc (Stack.pushWord (Stack.pushWord (Stack.pushWord working first) second) third) returning) =
      .done (.next (machine memory (pc + 1) (Stack.pushWord (Stack.pushWord (Stack.pushWord working second) third) first) returning)) := by
  simp [uxn_state, uxn_step, instruction, append_split]
  funext address
  simp only [Function.update_apply]
  split_ifs <;> rfl

theorem native_ovr (memory : Word → Byte) (pc first second : Word)
    (working returning : Uxn.Stack) (instruction : memory pc = 0x27) :
    Uxn.step (machine memory pc (Stack.pushWord (Stack.pushWord working first) second) returning) =
      .done (.next (machine memory (pc + 1) (Stack.pushWord (Stack.pushWord (Stack.pushWord working first) second) first) returning)) := by
  simp [uxn_state, uxn_step, instruction, append_split]
  funext address
  simp only [Function.update_apply]
  split_ifs <;> rfl

end ProgramProofs.Host
