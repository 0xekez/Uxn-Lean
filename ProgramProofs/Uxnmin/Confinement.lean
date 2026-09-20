import ProgramProofs.Uxnmin.Steps

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Confinement is inherited at any reachable configuration. -/
theorem Confined.reachable {start state : Configuration} (confined : Confined start)
    (reachable : Reachable start state) : Confined state :=
  fun _ _ later => confined _ _ (reachable.trans later)

theorem CompatibleDevices.reachable {start state : Configuration}
    (compatible : CompatibleDevices start) (reachable : Reachable start state) :
    CompatibleDevices state :=
  fun _ _ _ later => compatible _ _ _ (reachable.trans later)

/-- The replacement operation leaves all observations other than outside RAM alone. -/
theorem replaceOutside_label (ram : Word → Byte) (state : Configuration)
    (confined : Confined state) : label (replaceOutside ram state) = label state := by
  cases state with
  | starting => rfl
  | failed => rfl
  | running state world =>
    have h := confined state world .refl ram
    simp only [label]
    have terminal : (match replaceOutside ram (.running state world) with
        | .running updated _ => updated.next.isNone
        | _ => true) = state.next.isNone := by
      have h := congrArg Option.isNone h
      simpa [Configuration.next, replaceOutside] using h
    simp only [replaceOutside] at terminal ⊢
    rw [terminal]
    rfl

/-- Replace the unrepresented part of a VM's RAM. -/
def replaceRAM (ram : Word → Byte) (vm : Uxn.State) : Uxn.State :=
  { vm with mem.ram := fun address =>
      if address.toNat < ramSize then vm.mem.ram address else ram address }

/-- Observations that ignore outside RAM commute with a confined transition. -/
theorem Confined.observe {start : Configuration} {state : Uxn.Host.State}
    {world : Void IO.RealWorld} {α : Type}
    (confined : Confined start) (reachable : Reachable start (.running state world))
    (observe : Configuration → α)
    (unchanged : ∀ ram config, observe (replaceOutside ram config) = observe config)
    (ram : Word → Byte) :
    ((replaceOutside ram (.running state world)).next).map observe =
      (Configuration.next (.running state world)).map observe := by
  rw [confined state world reachable ram, Option.map_map]
  simp only [Function.comp_def, unchanged]

/-- Extensional confinement forces the fetched instruction to be in guest RAM. -/
theorem Confined.pc_lt {start : Configuration} (confined : Confined start)
    (state : Uxn.Host.State) (world : Void IO.RealWorld) (after : ReturnTo)
    (reachable : Reachable start (.running state world))
    (control : state.control = .evaluating after) : state.vm.pc.toNat < ramSize := by
  let evaluating : Configuration → Bool
    | .running state _ => match state.control with | .evaluating _ => true | _ => false
    | _ => false
  have replacement (ram : Word → Byte) (config : Configuration) :
      evaluating (replaceOutside ram config) = evaluating config := by
    cases config <;> rfl
  have tag (ram : Word → Byte) (opcode :
      (if state.vm.pc.toNat < ramSize then state.vm.mem.ram state.vm.pc else ram state.vm.pc) = 0) :
      ((replaceOutside ram (.running state world)).next).map evaluating = some false := by
    simp only [replaceOutside, Configuration.next, Uxn.Host.State.next, control]
    simp [Uxn.Host.step, opcode, uxn_state, uxn_step, evaluating, Configuration.ofResult]
    rfl
  have lit (ram : Word → Byte) (opcode :
      (if state.vm.pc.toNat < ramSize then state.vm.mem.ram state.vm.pc else ram state.vm.pc) = 0x80) :
      ((replaceOutside ram (.running state world)).next).map evaluating = some true := by
    simp only [replaceOutside, Configuration.next, Uxn.Host.State.next, control]
    simp [Uxn.Host.step, opcode, uxn_state, uxn_step, evaluating, Configuration.ofResult]
    rfl
  by_contra outside
  have zero := congrArg (Option.map evaluating) (confined state world reachable (fun _ => 0))
  have nonzero := congrArg (Option.map evaluating) (confined state world reachable (fun _ => 0x80))
  simp only [Option.map_map, Function.comp_def, replacement] at zero nonzero
  rw [tag _ (by simp [outside])] at zero
  rw [lit _ (by simp [outside])] at nonzero
  exact Bool.noConfusion (Option.some.inj (zero.trans nonzero.symm))

end ProgramProofs.Uxnmin.Model
