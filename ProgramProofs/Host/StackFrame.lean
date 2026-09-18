import ProgramProofs.Host.Stack

namespace ProgramProofs.Host.Stack
open Uxn

/-- A stack-prefix-preserving block preserves its top-word decomposition. -/
theorem asPushWord_of_frame (before after : Uxn.Stack) (pointer : Byte) (value : Word)
    (shape : Stack.pushWord { before with ptr := pointer } value = before)
    (space : pointer.toNat ≤ 253) (samePointer : after.ptr = before.ptr)
    (frame : ∀ index : Byte, index.toNat < before.ptr.toNat → after.data index = before.data index) :
    Stack.pushWord { after with ptr := pointer } value = after := by
  have beforePointer := congrArg Uxn.Stack.ptr shape
  simp only [Stack.pushWord, Stack.push] at beforePointer
  have beforeHigh := congrArg (fun stack : Uxn.Stack => stack.data pointer) shape
  have beforeLow := congrArg (fun stack : Uxn.Stack => stack.data (pointer + 1#8)) shape
  simp [Stack.pushWord, Stack.push] at beforeHigh beforeLow
  have high : after.data pointer = (value >>> 8).setWidth 8 := by
    rw [frame _ (by rw [← beforePointer]; bv_omega)]
    exact beforeHigh.symm
  have low : after.data (pointer + 1#8) = value.setWidth 8 := by
    rw [frame _ (by rw [← beforePointer]; bv_omega)]
    exact beforeLow.symm
  apply congrArg₂ Uxn.Stack.mk
  · funext index
    by_cases first : index = pointer
    · subst index
      simp [Stack.push, high]
    · by_cases second : index = pointer + 1#8
      · subst index
        simp [Stack.push, low]
      · simp [Stack.push, Function.update_of_ne, first, second]
  · simp [Stack.push, samePointer, ← beforePointer, BitVec.add_assoc]


end ProgramProofs.Host.Stack
