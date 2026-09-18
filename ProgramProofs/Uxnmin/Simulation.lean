import ProgramProofs.Uxnmin.Semantics
import ProgramProofs.Host.Execution
import ProgramProofs.RankedSimulation
import Mathlib.Data.Nat.Find

namespace ProgramProofs

/-- Extend a relation at instruction boundaries to a ranked simulation.
Each boundary pair must admit finitely many label-preserving concrete steps,
followed by a concrete step matching the direct step through the boundary
relation. If the direct state has halted, the endpoint must also have halted.
The matching step is separate from the finite path, so a direct transition
always takes at least one concrete transition. -/
theorem RankedSimulation.of_blocks {D C Obs : Type*}
    {nextD : D → Option D} {nextC : C → Option C}
    {labelD : D → Obs} {labelC : C → Obs}
    (boundary : D → C → Prop)
    (blocks : ∀ d c, boundary d c → ∃ last,
      Relation.ReflTransGen
        (fun x y => nextC x = some y ∧ labelD d = labelC x) c last ∧
      labelD d = labelC last ∧
      Option.Rel boundary (nextD d) (nextC last)) :
    ∃ R : D → C → Prop,
      (∀ d c, boundary d c → R d c) ∧
      RankedSimulation nextD nextC labelD labelC R := by
  classical
  let pending : Nat → D → C → Prop :=
    Nat.rec (fun d c => labelD d = labelC c ∧
        Option.Rel boundary (nextD d) (nextC c))
      (fun _ tail d c => labelD d = labelC c ∧
        ∃ c', nextC c = some c' ∧ tail d c')
  let dec : ∀ d c, DecidablePred (fun n => pending n d c) :=
    fun _ _ _ => Classical.propDecidable _
  let R : D → C → Prop := fun d c => ∃ n, pending n d c
  have includes : ∀ d c, boundary d c → R d c := by
    intro d c related
    obtain ⟨last, path, agree, matched⟩ := blocks d c related
    clear related
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, agree, matched⟩
    | @head c c' step _ ih =>
      obtain ⟨n, tail⟩ := ih
      exact ⟨n + 1, step.2, c', step.1, tail⟩
  refine ⟨R, includes, ?_, ?_⟩
  · intro d c ⟨n, tail⟩
    cases n <;> exact tail.1
  · refine ⟨fun (d : D) (c : C) => if related : R d c then @Nat.find (fun n => pending n d c) (dec d c) related else 0, ?_⟩
    intro d c related
    change ∃ n, pending n d c at related
    have tail := @Nat.find_spec _ (dec d c) related
    generalize chosen : @Nat.find _ (dec d c) related = n at tail
    cases n with
    | zero =>
      left
      obtain ⟨_, matched⟩ := tail
      exact Option.Rel.rec (fun h => .some (includes _ _ h)) .none matched
    | succ n =>
      obtain ⟨_, c', step, tail⟩ := tail
      have related' : R d c' := ⟨n, tail⟩
      refine Or.inr ⟨c', step, related', ?_⟩
      dsimp only
      rw [dif_pos related', dif_pos (show R d c from related), chosen]
      exact Nat.lt_succ_of_le (@Nat.find_min' _ (dec d c') related' n tail)

/-- Instruction-boundary blocks may perform their observable action before
returning to the next boundary. Both the prefix before that action and the
suffix after it are silent, at the old and new direct labels respectively. -/
theorem RankedSimulation.of_silent_chunks {D C Obs : Type*}
    {nextD : D → Option D} {nextC : C → Option C}
    {labelD : D → Obs} {labelC : C → Obs}
    (boundary : D → C → Prop)
    (blocks : ∀ d c, boundary d c → ∃ last,
      Relation.ReflTransGen
        (fun x y => nextC x = some y ∧ labelD d = labelC x) c last ∧
      labelD d = labelC last ∧
      Option.Rel (fun d' c' => ∃ finish,
        Relation.ReflTransGen
          (fun x y => nextC x = some y ∧ labelD d' = labelC x) c' finish ∧
        boundary d' finish) (nextD d) (nextC last)) :
    ∃ R : D → C → Prop,
      (∀ d c, boundary d c → R d c) ∧
      RankedSimulation nextD nextC labelD labelC R := by
  let settling : D → C → Prop := fun d c => ∃ finish,
    Relation.ReflTransGen
      (fun x y => nextC x = some y ∧ labelD d = labelC x) c finish ∧
    boundary d finish
  obtain ⟨R, includes, simulation⟩ := RankedSimulation.of_blocks settling (by
    intro d c ⟨finish, prelude, related⟩
    obtain ⟨last, suffix, agree, matched⟩ := blocks d finish related
    exact ⟨last, prelude.trans suffix, agree, matched⟩)
  exact ⟨R, fun d c related => includes d c ⟨c, .refl, related⟩, simulation⟩

end ProgramProofs

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host

/-- The assembly of the exact correctness conclusion from a loading contract
and instruction-handler contracts. The boundary relation must include terminal
and error configurations; this theorem imposes no representation choices.

The hypotheses of `correct` (filename bounds, file contents, confinement and
device compatibility) are used to prove the two premises below. They are not
needed again when the checked contracts are assembled into a simulation. -/
theorem correct_of_boundary (filename : String) (program : ByteArray)
    (before after : Void IO.RealWorld)
    (boundary : Configuration → Configuration → Prop) :
    let initial := Uxn.Host.initialState program
    let start : Configuration := .ok (.next initial.vm, initial) after
    (∃ steps host,
      Uxn.Host.run rom [filename] (some steps) before = .ok (0, host) after ∧
      host.fuel = some 0 ∧ boundary start (.ok (.next host.vm, host) after)) →
    (∀ d c, boundary d c → ∃ last,
      Relation.ReflTransGen (fun x y => next x = some y ∧ label d = label x) c last ∧
      label d = label last ∧
      Option.Rel (fun d' c' => ∃ finish,
        Relation.ReflTransGen
          (fun x y => next x = some y ∧ label d' = label x) c' finish ∧
        boundary d' finish) (next d) (next last)) →
    ∃ steps host, ∃ R : Configuration → Configuration → Prop,
      Uxn.Host.run rom [filename] (some steps) before = .ok (0, host) after ∧
      host.fuel = some 0 ∧
      R start (.ok (.next host.vm, host) after) ∧
      RankedSimulation next next label label R := by
  dsimp only
  intro loaded_boundary instruction_chunks
  obtain ⟨steps, host, loaded, exhausted, related⟩ := loaded_boundary
  obtain ⟨R, includes, simulation⟩ :=
    RankedSimulation.of_silent_chunks boundary instruction_chunks
  exact ⟨steps, host, R, loaded, exhausted, includes _ _ related, simulation⟩

/-- A finite device-free VM block is silent in the simulation's transition
system. The host record and IO world remain fixed throughout the block. -/
theorem reaches_chunk {s t : Uxn.State} (steps : ProgramProofs.Host.Reaches s t)
    (host : Uxn.Host.State) (world : Void IO.RealWorld) :
    Relation.ReflTransGen
      (fun x y => next x = some y ∧ label (.ok (.next s, host) world) = label x)
      (.ok (.next s, host) world) (.ok (.next t, host) world) := by
  induction steps with
  | refl => exact .refl
  | @next s t u step _ rest =>
    refine Relation.ReflTransGen.head ?_ rest
    constructor
    · simp only [next, Uxn.Host.step, step]
      rfl
    · rfl

/-- One concrete pure step followed by a silent block matches one guest
instruction, including instructions that return to the same machine state. -/
theorem nondevice_chunk_of_step {guest guest' outer first outer' : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (direct : Uxn.step guest = .done (.next guest'))
    (step : Uxn.step outer = .done (.next first))
    (steps : ProgramProofs.Host.Reaches first outer') :
    next (.ok (.next guest, guestHost) world) = some (.ok (.next guest', guestHost) world) ∧
    next (.ok (.next outer, outerHost) world) = some (.ok (.next first, outerHost) world) ∧
    Relation.ReflTransGen
      (fun x y => next x = some y ∧ label (.ok (.next guest', guestHost) world) = label x)
      (.ok (.next first, outerHost) world) (.ok (.next outer', outerHost) world) := by
  refine ⟨?_, ?_, reaches_chunk steps outerHost world⟩
  · simp only [next, Uxn.Host.step, direct]
    rfl
  · simp only [next, Uxn.Host.step, step]
    rfl

/-- Distinct endpoints guarantee that a device-free block has a first step. -/
theorem nondevice_chunk {guest guest' outer outer' : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (direct : Uxn.step guest = .done (.next guest'))
    (steps : ProgramProofs.Host.Reaches outer outer') (nonempty : outer ≠ outer') :
    ∃ first,
      next (.ok (.next guest, guestHost) world) = some (.ok (.next guest', guestHost) world) ∧
      next (.ok (.next outer, outerHost) world) = some (.ok (.next first, outerHost) world) ∧
      Relation.ReflTransGen
        (fun x y => next x = some y ∧ label (.ok (.next guest', guestHost) world) = label x)
        (.ok (.next first, outerHost) world) (.ok (.next outer', outerHost) world) := by
  cases steps with
  | refl => exact (nonempty rfl).elim
  | @next _ middle _ step rest =>
    exact ⟨middle, nondevice_chunk_of_step guestHost outerHost world direct step rest⟩

end ProgramProofs.Uxnmin
