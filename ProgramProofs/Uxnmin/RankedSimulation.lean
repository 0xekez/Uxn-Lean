import LeanLTL.Logics.LTL.Core
import ProgramProofs.RankedSimulation
import Mathlib.Logic.Function.Iterate

namespace LeanLTL.LTL.Formula

/-- An LTL formula contains no occurrence of the `next` operator. -/
@[simp] def NextFree {Obs : Type*} : Formula Obs → Prop
  | .var _ => True
  | .not φ => φ.NextFree
  | .or φ ψ | .until φ ψ => φ.NextFree ∧ ψ.NextFree
  | .next _ => False

end LeanLTL.LTL.Formula

namespace ProgramProofs

open LeanLTL

/-- A terminal state repeats forever for infinite-trace LTL semantics. -/
private def advance {S : Type*} (next : S → Option S) (s : S) : S :=
  (next s).getD s

/-- The observable execution, starting with the initial state's label. -/
def observedRun {S Obs : Type*} (next : S → Option S) (label : S → Obs)
    (s : S) : LTL.Trace Obs where
  trace := {
    toFun? := fun n => some (label ((advance next)^[n] s))
    length := ⊤
    nempty := by simp
    defined := by simp
  }
  infinite := rfl

/-- LeanLTL satisfaction on a machine's observable execution. -/
def Satisfies {S Obs : Type*} (next : S → Option S) (label : S → Obs)
    (s : S) (φ : LTL.Formula Obs) : Prop :=
  LTL.sat (observedRun next label s) φ

/-- Related executions satisfy exactly the same next-free LTL formulas.
The rank excludes infinite stuttering. Atoms inspect the shared labels. -/
theorem RankedSimulation.preserves
    {D C Obs : Type*}
    {nextD : D → Option D} {nextC : C → Option C}
    {labelD : D → Obs} {labelC : C → Obs} {R : D → C → Prop}
    (simulation : RankedSimulation nextD nextC labelD labelC R)
    {d : D} {c : C} (related : R d c)
    (φ : LTL.Formula Obs) (nextFree : φ.NextFree) :
    Satisfies nextD labelD d φ ↔ Satisfies nextC labelC c φ := by
  induction φ generalizing d c with
  | var p =>
    simpa only [Satisfies, LTL.sat, observedRun, LeanLTL.Trace.toFun,
      Function.iterate_zero, id_eq, Option.get_some] using
      (congrArg p (simulation.1 d c related)).to_iff
  | not φ ih => exact not_congr (ih related nextFree)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ related nextFree.1) (ihψ related nextFree.2)
  | next φ _ => exact nextFree.elim
  | «until» φ ψ ihφ ihψ =>
    suffices witnesses :
        (∃ n, (∀ i < n, Satisfies nextD labelD ((advance nextD)^[i] d) φ) ∧
          Satisfies nextD labelD ((advance nextD)^[n] d) ψ) ↔
        (∃ n, (∀ i < n, Satisfies nextC labelC ((advance nextC)^[i] c) φ) ∧
          Satisfies nextC labelC ((advance nextC)^[n] c) ψ) by
      simpa only [Satisfies, LTL.sat, observedRun, LeanLTL.Trace.shift,
        Function.iterate_add_apply, ENat.top_sub_natCast, Nat.zero_le, true_and] using witnesses
    obtain ⟨_, rank, progress⟩ := simulation
    have step : ∀ d c, R d c →
        R (advance nextD d) (advance nextC c) ∨
          (R d (advance nextC c) ∧ rank d (advance nextC c) < rank d c) := by
      intro d c related
      rcases progress d c related with matched | ⟨c', hc', related', smaller⟩
      · left
        cases hd : nextD d <;> cases hc : nextC c <;> simp_all [advance]
      · right
        simpa [advance, hc'] using And.intro related' smaller
    constructor
    · rintro ⟨n, hφ, hψ⟩
      induction n generalizing d c with
      | zero => exact ⟨0, by simp, (ihψ related nextFree.2).mp hψ⟩
      | succ n ih =>
        -- Match the direct witness, decreasing the rank on extra concrete steps.
        induction h : rank d c using Nat.strongRecOn generalizing c with
        | ind rank ihRank =>
          obtain ⟨k, hφ', hψ'⟩ :
              ∃ k, (∀ i < k, Satisfies nextC labelC ((advance nextC)^[i] (advance nextC c)) φ) ∧
                Satisfies nextC labelC ((advance nextC)^[k] (advance nextC c)) ψ := by
            rcases step d c related with matched | ⟨stutter, smaller⟩
            · apply ih matched
              · intro i hi
                simpa only [Function.iterate_succ_apply] using hφ (i + 1) (by omega)
              · simpa only [Function.iterate_succ_apply] using hψ
            · exact ihRank _ (by simpa [h] using smaller) stutter rfl
          refine ⟨k + 1, ?_, ?_⟩
          · intro i hi
            cases i with
            | zero => exact (ihφ related nextFree.1).mp (hφ 0 (by omega))
            | succ i =>
              simpa only [Function.iterate_succ_apply] using hφ' i (by omega)
          · simpa only [Function.iterate_succ_apply] using hψ'
    · rintro ⟨n, hφ, hψ⟩
      induction n generalizing d c with
      | zero => exact ⟨0, by simp, (ihψ related nextFree.2).mpr hψ⟩
      | succ n ih =>
        have tailψ : Satisfies nextC labelC ((advance nextC)^[n] (advance nextC c)) ψ := by
          simpa only [Function.iterate_succ_apply] using hψ
        have tailφ : ∀ i < n,
            Satisfies nextC labelC ((advance nextC)^[i] (advance nextC c)) φ := by
          intro i hi
          simpa only [Function.iterate_succ_apply] using hφ (i + 1) (by omega)
        rcases step d c related with matched | ⟨stutter, _⟩
        · obtain ⟨k, hφ', hψ'⟩ := ih matched tailφ tailψ
          refine ⟨k + 1, ?_, ?_⟩
          · intro i hi
            cases i with
            | zero => exact (ihφ related nextFree.1).mpr (hφ 0 (by omega))
            | succ i =>
              simpa only [Function.iterate_succ_apply] using hφ' i (by omega)
          · simpa only [Function.iterate_succ_apply] using hψ'
        · exact ih stutter tailφ tailψ

end ProgramProofs
