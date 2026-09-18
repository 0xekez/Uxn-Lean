import ProgramProofs.Uxnmin.PureMode
import ProgramProofs.Uxnmin.PermutationRaw
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def takeTwo (mode : Mode) : StateM Uxn.State (Word × Word) :=
  pureMode mode fun ops => do
    let first ← ops.dec
    let second ← ops.dec
    return (first, second)

def finishOvr (mode : Mode) (values : Word × Word) : StateM Uxn.State Step := do
  (stackOps mode.ret mode.short).inc values.2
  (stackOps mode.ret mode.short).inc values.1
  (stackOps mode.ret mode.short).inc values.2
  return .done (.next (← get))

theorem over_split (mode : Mode) :
    stackAction .ovr mode = (do let values ← takeTwo mode; finishOvr mode values) := by
  unfold takeTwo
  rw [← pureMode_bind]
  rfl

theorem takeTwo_run (guest : Uxn.State) (ret short keep : Bool) :
    takeTwo ⟨short, keep, ret⟩ guest =
      ((rawOperand (guestStack guest ret) (guestStack guest ret).ptr short,
        rawOperand (guestStack guest ret) (decrement (guestStack guest ret).ptr short) short),
        if keep then guest else setStack guest ret { guestStack guest ret with
          ptr := decrement (decrement (guestStack guest ret).ptr short) short }) := by
  as_aux_lemma =>
    cases ret <;> cases short <;> cases keep <;> rfl

theorem stack_action_ovr_modular (guest : Uxn.State) (ret short keep : Bool) :
    (stackAction .ovr ⟨short, keep, ret⟩ guest).fst =
      .done (.next (rawNext guest .ovr ret short keep)) := by
  rw [over_split]
  simp only [state_bind_apply, takeTwo_run, id_bind, finishOvr, stack_inc, uxn_state]
  cases ret <;> cases short <;> cases keep <;> rfl

end ProgramProofs.Uxnmin
