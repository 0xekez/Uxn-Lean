import ProgramProofs.Host.Host

namespace ProgramProofs.Host
open Uxn Uxn.Host

-- A proof-only finite execution relation over the existing VM step function.
inductive Reaches : Uxn.State → Uxn.State → Prop where
  | refl (s) : Reaches s s
  | next {s t u} : Uxn.step s = .done (.next t) → Reaches t u → Reaches s u

theorem Reaches.trans {s t u} (h : Reaches s t) (k : Reaches t u) :
    Reaches s u := by
  induction h with
  | refl => exact k
  | next hs _ ih => exact .next hs (ih k)

/-- Device-free finite execution preserves the unbounded host loop. -/
theorem Reaches.evalLoop {s t : Uxn.State} (h : Reaches s t)
    (host : Uxn.Host.State) (hf : host.fuel = none) :
    evalLoop (.next s) host = evalLoop (.next t) host := by
  induction h with
  | refl => rfl
  | next hs _ ih =>
    rw [evalLoop_next _ host hf, hs]
    exact ih

theorem Reaches.prepend {start next : Uxn.State} {property : Uxn.State → Prop}
    (step : Uxn.step start = .done (.next next))
    (rest : ∃ final, Reaches next final ∧ property final) :
    ∃ final, Reaches start final ∧ property final := by
  obtain ⟨final, steps, property⟩ := rest
  exact ⟨final, .next step steps, property⟩

end ProgramProofs.Host
