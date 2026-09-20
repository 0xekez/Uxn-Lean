import ProgramProofs.Uxnmin.PureEvaluation
import ProgramProofs.RankedSimulation

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host

def Silent (direct : Configuration) : Configuration → Configuration → Prop :=
  Relation.ReflTransGen (fun a b => a.next = some b ∧ label direct = label a)

def Block (boundary : Configuration → Configuration → Prop) (direct nested : Configuration) : Prop :=
  ∃ last, Silent direct nested last ∧ label direct = label last ∧
    Option.Rel (fun d c => ∃ finish, Silent d c finish ∧ boundary d finish) direct.next last.next

theorem PureReaches.silent {state final : Uxn.Host.State}
    (steps : PureReaches state final) (world : Void IO.RealWorld) (direct : Configuration)
    (live : label direct = .ok none world) :
    Silent direct (.running state world) (.running final world) :=
  Relation.ReflTransGen.mono (fun _ _ step => ⟨step.1, live.trans step.2.symm⟩) _ _ (steps.path world)

theorem label_evaluating (state : Uxn.Host.State) (after : ReturnTo)
    (control : state.control = .evaluating after) (world : Void IO.RealWorld) :
    label (.running state world) = .ok none world := by
  simp only [label, Uxn.Host.State.next, control, Option.isNone_some, Bool.false_eq_true, if_false]

theorem evaluating_reaches {first final : Uxn.State}
    (steps : ProgramProofs.Host.Reaches first final) (state : Uxn.Host.State)
    (after : ReturnTo) (control : state.control = .evaluating after) :
    PureReaches {state with vm := first} {state with vm := final} := by
  simpa only [← control] using Host.Reaches.evaluating steps state after

theorem configuration_next_step {state updated : Uxn.Host.State} {vm : Uxn.State}
    (after : ReturnTo) (world : Void IO.RealWorld)
    (control : state.control = .evaluating after)
    (step : Uxn.Host.step state.vm state = pure (.next vm, updated)) :
    Configuration.next (.running state world) = some (.running {updated with vm} world) := by
  rw [Configuration.next, next_of_step control step]
  rfl

theorem pure_block {filename : String} {initialWorld : Void IO.RealWorld}
    (confined : Confined (.starting (Uxn.Host.file filename) initialWorld))
    (compatible : CompatibleDevices (.starting (Uxn.Host.file filename) initialWorld))
    {invocation : Invocation} {guest outer : Uxn.Host.State} (world : Void IO.RealWorld)
    (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
    (image : Evaluation invocation guest outer)
    (brk : guest.vm.mem.ram guest.vm.pc ≠ 0)
    (write : guest.vm.mem.ram guest.vm.pc &&& 0x1f ≠ 0x17) :
    Block (Boundary filename initialWorld) (.running guest world) (.running outer world) := by
  obtain ⟨vm, first, final, direct, native, suffix, represented⟩ :=
    pure_evaluation confined compatible world reachable image brk write
  have direct := configuration_next_step invocation.directReturn world image.guestControl direct
  refine ⟨.running outer world, .refl, ?_, ?_⟩
  · rw [label_evaluating guest _ image.guestControl, label_evaluating outer _ image.outerControl]
  · rw [direct, configuration_next_pure invocation.outerReturn world image.outerControl native]
    refine .some ⟨.running {outer with vm := final} world, ?_,
      .evaluating invocation (reachable.tail direct) represented⟩
    exact (evaluating_reaches suffix outer _ image.outerControl).silent world _
      (label_evaluating {guest with vm := vm} _ image.guestControl world)

end ProgramProofs.Uxnmin.Model
