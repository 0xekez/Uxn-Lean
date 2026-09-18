import ProgramProofs.Uxnmin.Semantics
import ProgramProofs.Host.Reduction

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host

/-- Extensional confinement forces instruction fetches to stay in guest RAM. -/
theorem Semantics.Confined.pc_lt {start : Configuration}
    (confined : Confined start) (vm : Uxn.State) (host : Uxn.Host.State)
    (world : Void IO.RealWorld) (reachable : Reachable start (.ok (.next vm, host) world)) :
    vm.pc.toNat < ramSize := by
  let stopped : Configuration → Bool
    | .ok (.brk _, _) _ => true
    | _ => false
  have replacement (n : Nat) (ram : Word → Byte) (c : Configuration) :
      stopped (replaceOutside n ram c) = stopped c := by
    cases c with
    | error => rfl
    | ok pair world => cases pair with | mk outcome host => cases outcome <;> rfl
  have brk (vm : Uxn.State) (host : Uxn.Host.State) (world : Void IO.RealWorld)
      (opcode : vm.mem.ram vm.pc = 0) :
      (next (.ok (.next vm, host) world)).map stopped = some true := by
    simp [next, Uxn.Host.step, stopped, opcode, uxn_state, uxn_step]
    rfl
  have lit (vm : Uxn.State) (host : Uxn.Host.State) (world : Void IO.RealWorld)
      (opcode : vm.mem.ram vm.pc = 0x80) :
      (next (.ok (.next vm, host) world)).map stopped = some false := by
    simp [next, Uxn.Host.step, stopped, opcode, uxn_state, uxn_step]
    rfl
  by_contra outside
  have zero := congrArg (Option.map stopped) (confined _ reachable (fun _ => 0))
  have nonzero := congrArg (Option.map stopped) (confined _ reachable (fun _ => 0x80))
  simp only [Option.map_map, Function.comp_def, replacement] at zero nonzero
  have zeroTag : (next (replaceOutside ramSize (fun _ => 0)
      (.ok (.next vm, host) world))).map stopped = some true := by
    apply brk
    simp [replaceOutside.replace, outside]
  have litTag : (next (replaceOutside ramSize (fun _ => 0x80)
      (.ok (.next vm, host) world))).map stopped = some false := by
    apply lit
    simp [replaceOutside.replace, outside]
  rw [zeroTag] at zero
  rw [litTag] at nonzero
  exact Bool.noConfusion (Option.some.inj (zero.trans nonzero.symm))

/-- Confinement and device compatibility hold when execution resumes at a reachable state. -/
theorem restrictions_reachable {start state : Configuration}
    (reachable : Reachable start state) (confined : Confined start)
    (compatible : CompatibleDevices start) :
    Confined state ∧ CompatibleDevices state := by
  exact ⟨fun _ tail => confined _ (reachable.trans tail),
    fun vm host world tail => compatible vm host world (reachable.trans tail)⟩

/-- Replacing outside memory twice keeps only the final replacement. -/
theorem replaceOutside_replaceOutside (cutoff : Nat) (first last : Word → Byte)
    (state : Configuration) :
    replaceOutside cutoff last (replaceOutside cutoff first state) =
      replaceOutside cutoff last state := by
  have ram (vm : Uxn.State) :
      replaceOutside.replace cutoff last (replaceOutside.replace cutoff first vm) =
        replaceOutside.replace cutoff last vm := by
    simp only [replaceOutside.replace]
    congr 2
    funext address
    split <;> rfl
  cases state with
  | error => rfl
  | ok pair world =>
    rcases pair with ⟨outcome, host⟩
    cases outcome <;> simp only [replaceOutside, ram]

/-- A confined step preserves every RAM byte outside the guest's address space. -/
theorem Semantics.Confined.outside_unchanged {start : Configuration}
    (confined : Confined start) (vm : Uxn.State) (host : Uxn.Host.State)
    (world : Void IO.RealWorld) (reachable : Reachable start (.ok (.next vm, host) world))
    (outcome : Outcome) (host' : Uxn.Host.State) (world' : Void IO.RealWorld)
    (step : next (.ok (.next vm, host) world) = some (.ok (outcome, host') world'))
    (address : Word) (outside : ramSize ≤ address.toNat) :
    (match outcome with | .next vm' | .brk vm' => vm'.mem.ram address) = vm.mem.ram address := by
  have unchanged : replaceOutside ramSize vm.mem.ram (.ok (.next vm, host) world) =
      .ok (.next vm, host) world := by
    simp only [replaceOutside, replaceOutside.replace, ite_self]
  have preserved := confined _ reachable vm.mem.ram
  rw [unchanged, step, Option.map_some] at preserved
  have memory := congrArg
    (fun c : Configuration => match c with
      | .ok (.next vm', _) _ | .ok (.brk vm', _) _ => vm'.mem.ram address
      | .error _ _ => 0) (Option.some.inj preserved)
  cases outcome <;> simpa [replaceOutside, replaceOutside.replace, Nat.not_lt.mpr outside] using memory

/-- Any observation independent of outside RAM is unchanged by replacing it
before a confined instruction. -/
theorem Semantics.Confined.observe {start state : Configuration} {α : Type}
    (confined : Confined start) (reachable : Reachable start state)
    (observe : Configuration → α)
    (unchanged : ∀ ram state, observe (replaceOutside ramSize ram state) = observe state)
    (ram : Word → Byte) :
    (next (replaceOutside ramSize ram state)).map observe = (next state).map observe := by
  rw [confined _ reachable ram, Option.map_map]
  simp only [Function.comp_def, unchanged]

end ProgramProofs.Uxnmin
