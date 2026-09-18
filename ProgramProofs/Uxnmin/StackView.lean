import ProgramProofs.Host.Stack

set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Host.Stack
open Uxn

theorem asPushWord (stack : Uxn.Stack) :
    pushWord { stack with ptr := stack.ptr - 2 }
      (stack.data (stack.ptr - 2) ++ stack.data (stack.ptr - 1)) = stack := by
  cases stack with
  | mk data ptr =>
    have next : ptr - 2 + 1 = ptr - 1 := by bv_omega
    have finish : ptr - 1 + 1 = ptr := by bv_omega
    dsimp only [pushWord, push]
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb,
      BitVec.extractLsb'_append_eq_left, BitVec.setWidth_append_eq_right, next, finish]
    simp only [Function.update_eq_self]

end ProgramProofs.Host.Stack
