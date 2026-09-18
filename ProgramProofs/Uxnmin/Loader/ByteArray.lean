import Uxn.Host
import Init.Data.Array.Lemmas

namespace ByteArray

theorem forIn_data_toList {β : Type v} {m : Type v → Type w} [Monad m]
    (bytes : ByteArray) (initial : β) (action : UInt8 → β → m (ForInStep β)) :
    forIn bytes initial action = forIn bytes.data.toList initial action := by
  rw [Array.forIn_toList]
  have loop : ∀ (n : Nat) (bound : n ≤ bytes.size) (state : β),
      ByteArray.forIn.loop bytes action n bound state =
        Array.forIn'.loop bytes.data (fun byte _ => action byte) n bound state := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro bound state
      simp only [ByteArray.forIn.loop, Array.forIn'.loop]
      congr 1
      funext result
      cases result with
      | done => rfl
      | yield state => exact ih _ state
  exact loop bytes.size (Nat.le_refl _) initial

end ByteArray
