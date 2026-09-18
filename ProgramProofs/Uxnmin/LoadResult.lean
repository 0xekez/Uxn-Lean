import ProgramProofs.Uxnmin.LoadAction

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def loadResult (kind : AddressMode) (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack guest ret keep kind.consumed) ret short
    (if short then guest.mem.ram (kind.address guest ret) ++
      guest.mem.ram (kind.following (kind.address guest ret))
     else (guest.mem.ram (kind.address guest ret)).setWidth 16)

/-- The zero-page load action, including the byte wraparound of its second address. -/
theorem load_zero_action (guest : Uxn.State) (ret short keep : Bool) :
    (loadAction .zero ⟨short, keep, ret⟩ guest).fst = .done (.next (loadResult .zero guest ret short keep)) := by
  let raw (guest : Uxn.State) (ret short keep : Bool) :=
    let address := (guestStack guest ret).data ((guestStack guest ret).ptr - 1)
    pushStack (popStack guest ret keep 1) ret short
      (if short then guest.mem.ram (address.setWidth 16) ++ guest.mem.ram ((address + 1#8).setWidth 16)
       else (guest.mem.ram (address.setWidth 16)).setWidth 16)
  have execute (guest : Uxn.State) (ret short keep : Bool) :
      (loadAction .zero ⟨short, keep, ret⟩ guest).fst = .done (.next (raw guest ret short keep)) := by
    as_aux_lemma => cases ret <;> cases short <;> cases keep <;> rfl
  rw [execute]
  congr 2
  simp [raw, loadResult, AddressMode.address, AddressMode.following, AddressMode.consumed]

/-- Relative loads use the already-advanced instruction pointer. -/
theorem load_relative_action (guest : Uxn.State) (ret short keep : Bool) :
    (loadAction .relative ⟨short, keep, ret⟩ guest).fst =
      .done (.next (loadResult .relative guest ret short keep)) := by
  as_aux_lemma => cases ret <;> cases short <;> cases keep <;> rfl

/-- Absolute loads consume a two-byte address in either result mode. -/
theorem load_absolute_action (guest : Uxn.State) (ret short keep : Bool) :
    (loadAction .absolute ⟨short, keep, ret⟩ guest).fst =
      .done (.next (loadResult .absolute guest ret short keep)) := by
  let rawAddress (stack : Uxn.Stack) := (stack.data (stack.ptr - 1)).setWidth 16 |||
    (stack.data (stack.ptr - 1 - 1)).setWidth 16 <<< 8
  let raw (guest : Uxn.State) (ret short keep : Bool) :=
    let source := guestStack guest ret
    pushStack (if keep then guest else setStack guest ret { source with ptr := source.ptr - 1 - 1 }) ret short
      (if short then guest.mem.ram (rawAddress source) ++ guest.mem.ram (rawAddress source + 1)
       else (guest.mem.ram (rawAddress source)).setWidth 16)
  have execute (guest : Uxn.State) (ret short keep : Bool) :
      (loadAction .absolute ⟨short, keep, ret⟩ guest).fst = .done (.next (raw guest ret short keep)) := by
    as_aux_lemma => cases ret <;> cases short <;> cases keep <;> rfl
  have address (stack : Uxn.Stack) : rawAddress stack = operand stack stack.ptr true := by
    simp [rawAddress, operand, join_bytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [execute]
  congr 2
  simp only [raw, address]
  cases ret <;> cases short <;> cases keep <;>
    simp [loadResult, AddressMode.address, AddressMode.following, AddressMode.consumed,
      setStack, popStack, guestStack, BitVec.sub_eq_add_neg, BitVec.add_assoc]

end ProgramProofs.Uxnmin
