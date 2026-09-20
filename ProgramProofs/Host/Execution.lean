import ProgramProofs.Host.Host
import ProgramProofs.Host.Reaches

namespace ProgramProofs.Host
open Uxn Uxn.Host

/-- Device-free finite execution preserves the host run and its continuation. -/
theorem Reaches.evaluate {s t : Uxn.State} (h : Reaches s t)
    (after : ReturnTo) (host : Uxn.Host.State) :
    evaluate after s host = evaluate after t host := by
  induction h with
  | refl => rfl
  | next hs _ ih =>
    simp only [ProgramProofs.Host.evaluate]
    rw [run_next]
    simpa only [ProgramProofs.Host.evaluate, Uxn.Host.State.next, Uxn.Host.step, hs, uxn_state, pure_bind] using ih

end ProgramProofs.Host
