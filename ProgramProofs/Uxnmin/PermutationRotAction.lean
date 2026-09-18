import ProgramProofs.Uxnmin.PureMode
import ProgramProofs.Uxnmin.PermutationRaw
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def finishRot (mode : Mode) (values : Word × Word × Word) : StateM Uxn.State Step := do
  (stackOps mode.ret mode.short).inc values.2.1
  (stackOps mode.ret mode.short).inc values.1
  (stackOps mode.ret mode.short).inc values.2.2
  return .done (.next (← get))

theorem rotation_split (mode : Mode) :
    stackAction .rot mode = (do let values ← takeThree mode; finishRot mode values) := by
  unfold takeThree
  rw [← pureMode_bind]
  rfl

theorem takeThree_run (guest : Uxn.State) (ret short keep : Bool) :
    takeThree ⟨short, keep, ret⟩ guest =
      ((rawOperand (guestStack guest ret) (guestStack guest ret).ptr short,
        rawOperand (guestStack guest ret) (decrement (guestStack guest ret).ptr short) short,
        rawOperand (guestStack guest ret) (decrement (decrement (guestStack guest ret).ptr short) short) short),
        if keep then guest else setStack guest ret { guestStack guest ret with
          ptr := decrement (decrement (decrement (guestStack guest ret).ptr short) short) short }) := by
  as_aux_lemma =>
    cases ret <;> cases short <;> cases keep <;> rfl

theorem stack_action_rot_modular (guest : Uxn.State) (ret short keep : Bool) :
    (stackAction .rot ⟨short, keep, ret⟩ guest).fst =
      .done (.next (rawNext guest .rot ret short keep)) := by
  rw [rotation_split]
  simp only [state_bind_apply, takeThree_run, id_bind, finishRot, stack_inc, uxn_state]
  cases ret <;> cases short <;> cases keep <;> rfl

end ProgramProofs.Uxnmin
