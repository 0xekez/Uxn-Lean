import ProgramProofs.Uxnmin.PermutationRaw
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host
theorem stack_action_swp (guest : Uxn.State) (ret short keep : Bool) :
    (stackAction .swp ⟨short, keep, ret⟩ guest).fst =
      .done (.next (rawNext guest .swp ret short keep)) := by
  as_aux_lemma =>
    dsimp only [rawNext, decrement, rawOperand]
    cases ret <;> cases short <;> cases keep <;> rfl
end ProgramProofs.Uxnmin
