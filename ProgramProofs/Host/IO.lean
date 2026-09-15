import Uxn.Host

namespace ProgramProofs.Host
open Uxn

private theorem io_bind_apply {α β} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w = match x w with
      | .ok a w' => f a w'
      | .error e w' => .error e w' := by
  change EST.bind x f w = _
  exact (EST.bind.eq_def x f w).trans (by cases x w <;> rfl)

/-- IO sequencing obeys the monad laws on both successful and failed actions. -/
instance : LawfulMonad IO := LawfulMonad.mk' IO
  (id_map := by
    intro α x
    funext w
    change EST.bind x (fun a => EST.pure (id a)) w = x w
    exact (EST.bind.eq_def _ _ _).trans (by cases x w <;> rfl))
  (pure_bind := by intros; rfl)
  (bind_assoc := by
    intro α β γ x f g
    funext w
    simp only [io_bind_apply]
    cases x w <;> rfl)

/-- The host's single-byte stdout action, named for composing output proofs. -/
def writeStdout (byte : Byte) : IO Unit := do
  (← IO.getStdout).write ⟨#[UInt8.ofBitVec byte]⟩

end ProgramProofs.Host
