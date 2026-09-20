import ProgramProofs.Uxnmin.Semantics
import ProgramProofs.Host.Reaches

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host

/-- A finite sequence of host transitions that perform no IO. -/
inductive PureReaches : Uxn.Host.State → Uxn.Host.State → Prop where
  | refl (state) : PureReaches state state
  | head {state middle final} : state.next = some (pure middle) →
      PureReaches middle final → PureReaches state final

theorem PureReaches.trans {state middle final : Uxn.Host.State}
    (first : PureReaches state middle) (last : PureReaches middle final) :
    PureReaches state final := by
  induction first with
  | refl => exact last
  | head step _ rest => exact .head step (rest last)

theorem PureReaches.prepend {state middle : Uxn.Host.State} {property : Uxn.Host.State → Prop}
    (step : state.next = some (pure middle))
    (tail : ∃ final, PureReaches middle final ∧ property final) :
    ∃ final, PureReaches state final ∧ property final := by
  obtain ⟨final, steps, property⟩ := tail
  exact ⟨final, .head step steps, property⟩

theorem PureReaches.path {state final : Uxn.Host.State}
    (steps : PureReaches state final) (world : Void IO.RealWorld) :
    Relation.ReflTransGen
      (fun a b => Configuration.next a = some b ∧ label a = .ok none world)
      (.running state world) (.running final world) := by
  induction steps with
  | refl => exact .refl
  | head step _ rest =>
    refine .head ⟨?_, ?_⟩ rest
    · simp only [Configuration.next, step, Option.map_some]
      rfl
    · simp only [label, step, Option.isNone_some, Bool.false_eq_true, if_false]

/-- Pure VM execution retains the host's evaluation continuation. -/
theorem Host.Reaches.evaluating {vm final : Uxn.State}
    (steps : ProgramProofs.Host.Reaches vm final) (host : Uxn.Host.State) (after : ReturnTo) :
    PureReaches { host with vm, control := .evaluating after }
      { host with vm := final, control := .evaluating after } := by
  induction steps with
  | refl => exact .refl _
  | next step _ rest =>
    apply PureReaches.head _ rest
    simp only [Uxn.Host.State.next, Uxn.Host.step, step]
    rfl

/-- The result of a successful instruction is installed in the live host state. -/
theorem next_of_step {state updated : Uxn.Host.State} {vm : Uxn.State} {after : ReturnTo}
    (control : state.control = .evaluating after)
    (step : Uxn.Host.step state.vm state = pure (.next vm, updated)) :
    state.next = some (pure { updated with vm }) := by
  simp only [Uxn.Host.State.next, control, step]
  rfl

/-- A pure VM instruction is one actual host/configuration transition. -/
theorem configuration_next_pure {state : Uxn.Host.State} {vm : Uxn.State}
    (after : ReturnTo) (world : Void IO.RealWorld)
    (control : state.control = .evaluating after)
    (step : Uxn.step state.vm = .done (.next vm)) :
    Configuration.next (.running state world) = some (.running {state with vm} world) := by
  rw [Configuration.next, next_of_step (updated := state) (vm := vm) control (by simp only [Uxn.Host.step, step, uxn_state])]
  rfl

/-- A BRK finishes the current evaluation and selects its saved continuation. -/
theorem next_of_brk {state updated : Uxn.Host.State} {vm : Uxn.State} {after : ReturnTo}
    (control : state.control = .evaluating after)
    (step : Uxn.Host.step state.vm state = pure (.brk vm, updated)) :
    state.next = some (pure { updated with vm, control := .console (match after with
      | .arguments args => if updated.consoleVector == 0 then .done else .arguments args
      | .console work => work) }) := by
  cases after <;> simp only [Uxn.Host.State.next, control, step] <;> rfl

end ProgramProofs.Uxnmin.Model
