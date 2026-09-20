import ProgramProofs.Uxnmin.Chunks

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host

theorem configuration_pure {state final : Uxn.Host.State} (world : Void IO.RealWorld)
    (step : state.next = some (pure final)) :
    Configuration.next (.running state world) = some (.running final world) := by
  rw [Configuration.next, step]
  rfl

theorem PureReaches.last {state final : Uxn.Host.State} (steps : PureReaches state final) :
    state = final ∨ ∃ penultimate, PureReaches state penultimate ∧ penultimate.next = some (pure final) := by
  induction steps with
  | refl => exact .inl rfl
  | @head state middle final step rest ih =>
    rcases ih with same | ⟨penultimate, before, last⟩
    · subst middle; exact .inr ⟨state, .refl _, step⟩
    · exact .inr ⟨penultimate, .head step before, last⟩

/-- Align a pure block at its last transition, so completion labels remain exact. -/
theorem pure_last_block {boundary : Configuration → Configuration → Prop}
    {direct direct' : Configuration} {outer final : Uxn.Host.State} (world : Void IO.RealWorld)
    (live : label direct = .ok none world) (directStep : direct.next = some direct')
    (steps : PureReaches outer final) (different : outer ≠ final)
    (related : boundary direct' (.running final world)) : Block boundary direct (.running outer world) := by
  obtain same | ⟨penultimate, before, last⟩ := steps.last
  · exact (different same).elim
  · refine ⟨.running penultimate world, before.silent world direct live, ?_, ?_⟩
    · simp only [label, last, Option.isNone_some, Bool.false_eq_true, if_false]
      exact live
    · rw [directStep, configuration_pure world last]
      exact .some ⟨_, .refl, related⟩

theorem next_delivery_zero {state : Uxn.Host.State} (value kind : Byte) (after : Console)
    (control : state.control = .delivering value kind after) (zero : state.consoleVector = 0) :
    state.next = some (pure { (state.write Port.Console.read value).write Port.Console.type kind with
      control := .console after }) := by
  simp only [Uxn.Host.State.next, control, Uxn.Host.State.write, zero]
  rfl

theorem next_delivery_vector {state : Uxn.Host.State} (value kind : Byte) (after : Console)
    (control : state.control = .delivering value kind after) (nonzero : state.consoleVector ≠ 0) :
    state.next = some (pure { (state.write Port.Console.read value).write Port.Console.type kind with
      vm.pc := state.consoleVector, control := .evaluating (.console after) }) := by
  simp only [Uxn.Host.State.next, control, Uxn.Host.State.write]
  simp only [BitVec.ofNat_eq_ofNat] at nonzero
  simp [nonzero]

theorem next_brk {state : Uxn.Host.State} (after : ReturnTo)
    (control : state.control = .evaluating after) (brk : state.vm.mem.ram state.vm.pc = 0) :
    state.next = some (pure {state with
      vm.pc := state.vm.pc + 1,
      control := .console (match after with
        | .arguments args => if state.consoleVector == 0 then .done else .arguments args
        | .console work => work)}) := by
  apply next_of_brk control
  simp [Uxn.Host.step, uxn_state, uxn_step, brk]

theorem machine_self (vm : Uxn.State) :
    ProgramProofs.Host.machine vm.mem.ram vm.pc vm.mem.wstk vm.mem.rstk = vm := by
  cases vm
  rfl

end ProgramProofs.Uxnmin.Model
