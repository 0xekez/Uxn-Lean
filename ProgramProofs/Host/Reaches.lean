import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO

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

theorem Reaches.prepend {start next : Uxn.State} {property : Uxn.State → Prop}
    (step : Uxn.step start = .done (.next next))
    (rest : ∃ final, Reaches next final ∧ property final) :
    ∃ final, Reaches start final ∧ property final := by
  obtain ⟨final, steps, property⟩ := rest
  exact ⟨final, .next step steps, property⟩

end ProgramProofs.Host
