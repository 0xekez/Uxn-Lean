import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Find

namespace ProgramProofs

-- A one-sided variant of well-founded simulation where every step of
-- the specification corresponds corresponds to ≥ 1 step of the
-- simulation, adapted from Manolios, *Mechanical Verification of
-- Reactive Systems* (2001), §4.2, Definition 4 (p. 37).
def RankedSimulation {D C Obs : Type*}
    (nextD : D → Option D) (nextC : C → Option C)
    (labelD : D → Obs) (labelC : C → Obs) (R : D → C → Prop) : Prop :=
  (∀ d c, R d c → labelD d = labelC c) ∧
  ∃ rank : D → C → Nat, ∀ d c, R d c →
    Option.Rel R (nextD d) (nextC c) ∨
      ∃ c', nextC c = some c' ∧ R d c' ∧ rank d c' < rank d c

/-- Finitely many stuttering steps suffice to match the next direct step,
including the case where the direct execution has ended. -/
theorem RankedSimulation.matches {D C Obs : Type*}
    {nextD : D → Option D} {nextC : C → Option C}
    {labelD : D → Obs} {labelC : C → Obs} {R : D → C → Prop}
    (simulation : RankedSimulation nextD nextC labelD labelC R)
    {d : D} {c : C} (related : R d c) :
    ∃ c', Relation.ReflTransGen (fun x y => nextC x = some y ∧ R d y) c c' ∧
      Option.Rel R (nextD d) (nextC c') := by
  obtain ⟨_, rank, progress⟩ := simulation
  induction h : rank d c using Nat.strongRecOn generalizing c with
  | ind n ih =>
    rcases progress d c related with matched | ⟨c', step, related', smaller⟩
    · exact ⟨c, .refl, matched⟩
    · obtain ⟨last, path, matched⟩ := ih (rank d c') (by simpa [h] using smaller) related' rfl
      exact ⟨last, (Relation.ReflTransGen.single ⟨step, related'⟩).trans path, matched⟩

/-- Extend a relation at instruction boundaries to a ranked simulation.
Each boundary pair must admit finitely many label-preserving concrete steps,
followed by a concrete step matching the direct step through the boundary
relation. If the direct state has halted, the endpoint must also have halted.
The matching step is separate from the finite path, so a direct transition
always takes at least one concrete transition. -/
theorem RankedSimulation.of_finite_blocks {D C Obs : Type*}
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
theorem RankedSimulation.of_silent_blocks {D C Obs : Type*}
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
  obtain ⟨R, includes, simulation⟩ := RankedSimulation.of_finite_blocks settling (by
    intro d c ⟨finish, prelude, related⟩
    obtain ⟨last, suffix, agree, matched⟩ := blocks d finish related
    exact ⟨last, prelude.trans suffix, agree, matched⟩)
  exact ⟨R, fun d c related => includes d c ⟨c, .refl, related⟩, simulation⟩


end ProgramProofs
