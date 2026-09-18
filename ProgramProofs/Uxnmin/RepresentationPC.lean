import ProgramProofs.Uxnmin.RepresentationPop
import ProgramProofs.Uxnmin.Return

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Updating both stored PC bytes implements an arbitrary guest jump. -/
theorem Represents.setPC {guest outer : Uxn.State} (rep : Represents guest outer) (pc : Word) :
    Represents { guest with pc }
      { outer with mem.ram := (Function.update
          (Function.update outer.mem.ram 0x45 ((pc >>> 8).setWidth 8))
          0x46 (pc.setWidth 8)) } := by
  constructor
  · exact (rep.code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  · intro address bound
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by
      dsimp [relocate, ramSize] at *
      bv_omega), Function.update_of_ne (by
      dsimp [relocate, ramSize] at *
      bv_omega)]
    exact rep.ram address bound
  · intro ret index
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by cases ret <;> dsimp [stackBase] <;> bv_omega),
      Function.update_of_ne (by cases ret <;> dsimp [stackBase] <;> bv_omega)]
    exact rep.stackData ret index
  · intro ret
    cases ret with
    | false => simpa [stackBase, guestStack] using rep.stackPointer false
    | true => simpa [stackBase, guestStack] using rep.stackPointer true
  · simp
  · simp

/-- The fetch/decode prefix has a first actual VM step, even when the whole
instruction eventually returns to its original boundary state. -/
theorem header_progress {guest outer dispatched : Uxn.State}
    (before : Represents guest outer)
    (after : Represents { guest with pc := guest.pc + 1 } dispatched)
    (steps : Reaches outer dispatched) :
    ∃ first, Uxn.step outer = .done (.next first) ∧ Reaches first dispatched := by
  cases steps with
  | refl => exact False.elim (before.ne_of_pc_next after rfl rfl)
  | next step rest => exact ⟨_, step, rest⟩

end ProgramProofs.Uxnmin
