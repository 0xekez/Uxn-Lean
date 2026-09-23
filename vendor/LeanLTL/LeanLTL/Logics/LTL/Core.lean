import LeanLTL.Trace.Defs

/-!
Core split of UCSCFormalMethods/LeanLTL at
d5473f06ab9d0ea652a51b2e78b11089731c4b6c.

The LTL definitions and derived connectives below are unchanged upstream text.
Only the TraceSet translation and its proof dependencies are omitted.
-/

namespace LeanLTL.Trace

@[simp] theorem length_eq_of_infinite {σ : Type*} {t : Trace σ}
    (h : t.Infinite) : t.length = ⊤ := h

@[simp] theorem infinite_lt_length {σ : Type*} (t : Trace σ) (h : t.Infinite) (n : Nat) :
    n < t.length := by
  simp [Trace.Infinite] at h
  simp [h]

@[simp] theorem infinite_shift_iff {σ : Type*} (t : Trace σ) {i} {h} :
    (t.shift i h).Infinite ↔ t.Infinite := by
  simp [Trace.Infinite, Trace.shift]

end LeanLTL.Trace

namespace LeanLTL.LTL

-- Definitions taken from "Handbook of model checking", Section 2.3.1 (without past-time operators)
-- Note: Past-time operators add no expressive power to the logic (see source)
def Var (σ : Type*) := σ -> Prop
structure Trace (σ : Type*) where
  trace : LeanLTL.Trace σ
  infinite : trace.Infinite

attribute [simp] Trace.infinite

inductive Formula (σ : Type*) where
  | var (v : (Var σ))
  | not (f : Formula σ)
  | or (f₁ f₂ : Formula σ)
  | next (f : Formula σ)
  | until (f₁ f₂ : Formula σ)

def sat {σ : Type*} (t : Trace σ) (f : Formula σ) : Prop :=
  match f with
  | Formula.var v        => v (t.trace.toFun 0 (by simp))
  | Formula.not f        => ¬ sat t f
  | Formula.or f₁ f₂     => sat t f₁ ∨ sat t f₂
  | Formula.next f       =>
    let next_t := {
      trace := t.trace.shift 1 (by simp)
      infinite := by simp
    }
    sat next_t f
  | Formula.until f₁ f₂  =>
    ∃ i ≥ 0,
    let t_i := {
      trace := t.trace.shift i (by simp)
      infinite := by simp
    }
    (∀ j < i,
      let t_j := {
        trace := t.trace.shift j (by simp)
        infinite := by simp
      }
      sat t_j f₁)
    ∧ sat t_i f₂

variable {σ : Type*}

def Formula.true : Formula σ := Formula.var (fun _ => True)
def Formula.false : Formula σ := Formula.var (fun _ => False)
def Formula.and (f₁ f₂ : Formula σ) : Formula σ := (f₁.not.or f₂.not).not
def Formula.imp (f₁ f₂ : Formula σ) : Formula σ := f₁.not.or f₂
def Formula.eventually (f₁ : Formula σ) : Formula σ := Formula.true.until f₁
def Formula.globally (f₁ : Formula σ) : Formula σ := f₁.not.eventually.not
def Formula.weak_until (f₁ f₂ : Formula σ) : Formula σ := Formula.or (f₁.until f₂) f₁.globally
end LeanLTL.LTL
