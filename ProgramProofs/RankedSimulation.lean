import Mathlib.Logic.Relation

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

end ProgramProofs
