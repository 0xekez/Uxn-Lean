import ProgramProofs.Host.Host

namespace ProgramProofs.Fibonacci
open Uxn Uxn.Host ProgramProofs.Host

private theorem deo_consoleVectorLow (mem : Memory) (value : Byte) :
    deo mem 0x11#8 value = (do
      modify (·.write 0x11 value)
      modify fun s => { s with consoleVector := s.read 0x10 ++ value }
      return {}) := rfl

/-- Reduce state operations while leaving IO actions opaque. -/
scoped macro "state_reduce" : tactic => `(tactic| (
  all_goals try simp [uxn_state]))

/-- Unfold one host iteration and symbolically execute its VM instruction. -/
scoped macro "host_step" "[" facts:term,* "]" : tactic => `(tactic| (
  rw [Uxn.Host.evalLoop.eq_def]
  all_goals try simp [uxn_state, Uxn.Host.step]
  all_goals try conv =>
    pattern Uxn.step _
    simp (disch := decide) only [machine, Uxn.step, stepM, fetchInstruction, fetchByte,
      StateT.run, Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, Pure.pure, StateT.pure, $[$facts:term],*]
    simp (disch := decide) [$[$facts:term],*, getElem!_pos, ByteArray.getElem_eq_getElem_data]
    dsimp [Uxn.Instruction.ofByte]
    simp [uxn_state, uxn_step]
    simp (disch := decide) [$[$facts:term],*, getElem!_pos, ByteArray.getElem_eq_getElem_data]
  all_goals try dsimp [Request.Result]
  all_goals try simp [respond, uxn_state]
  all_goals try rw [deo_consoleVectorLow]
  all_goals try simp [deo, Host.State.read, Host.State.write,
    Patch.apply, uxn_state, Function.update_apply,
    BitVec.sub_eq_add_neg, BitVec.add_assoc, Vector.get, Fin.cast, Array.getElem_set]))

end ProgramProofs.Fibonacci
