import ProgramProofs.Uxnmin.GuestStack

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Scratch registers and both software stacks; device bookkeeping begins at `0x759`. -/
def StackScratch (address : Word) : Prop :=
  PopScratch address ∨ (0x555 ≤ address.toNat ∧ address.toNat < 0x759)

/-- Update an encoded pointer without changing any stack byte. -/
theorem Represents.setStackPointer {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret : Bool) (pointer : Byte) :
    Represents (setStack guest ret { guestStack guest ret with ptr := pointer })
      { outer with mem.ram := Function.update outer.mem.ram (stackBase ret + 0x100) pointer } := by
  have restored : ∀ p : Byte, p - (p - pointer) = pointer := by intro p; bv_omega
  have update := rep.popStack ret false ((guestStack guest ret).ptr - pointer)
  cases ret <;> simpa [ProgramProofs.Uxnmin.popStack, guestStack, setStack, restored] using update

/-- Update an encoded byte, including bytes exposed by pointer wraparound. -/
theorem Represents.setStackByte {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret : Bool) (index value : Byte) :
    Represents (setStack guest ret { guestStack guest ret with data := Function.update (guestStack guest ret).data index value })
      { outer with mem.ram := Function.update outer.mem.ram (stackBase ret + index.setWidth 16) value } := by
  constructor
  · apply rep.code.write
    right; left
    cases ret <;> dsimp [stackBase] <;> bv_omega
  · intro address confined
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by
      cases ret <;>
        dsimp [stackBase, relocate, ramSize] at *
      all_goals bv_omega)]
    cases ret <;> exact rep.ram address confined
  · intro selected address
    have represented := rep.stackData selected address
    by_cases sameStack : selected = ret
    · subst selected
      by_cases same : address = index
      · subst address
        cases ret <;> simp [setStack, guestStack]
      · have separate : stackBase ret + address.setWidth 16 ≠ stackBase ret + index.setWidth 16 := by bv_omega
        cases ret <;> simpa [setStack, guestStack, separate, same] using represented
    · have separate : stackBase selected + address.setWidth 16 ≠ stackBase ret + index.setWidth 16 := by
        cases ret <;> cases selected <;> dsimp [stackBase] at * <;> first | contradiction | bv_omega
      cases ret <;> cases selected <;> first
        | contradiction
        | simpa [setStack, guestStack, separate] using represented
  · intro selected
    have represented := rep.stackPointer selected
    have separate : stackBase selected + 0x100 ≠ stackBase ret + index.setWidth 16 := by
      cases ret <;> cases selected <;> dsimp [stackBase] <;> bv_omega
    change Function.update outer.mem.ram (stackBase ret + index.setWidth 16) value
      (stackBase selected + 0x100) = _
    rw [Function.update_of_ne separate]
    cases ret <;> cases selected <;> exact represented
  · have separate : (0x45 : Word) ≠ stackBase ret + index.setWidth 16 := by
      cases ret <;> dsimp [stackBase] <;> bv_omega
    change Function.update outer.mem.ram (stackBase ret + index.setWidth 16) value 0x45 = _
    rw [Function.update_of_ne separate]
    cases ret <;> exact rep.pcHigh
  · have separate : (0x46 : Word) ≠ stackBase ret + index.setWidth 16 := by
      cases ret <;> dsimp [stackBase] <;> bv_omega
    change Function.update outer.mem.ram (stackBase ret + index.setWidth 16) value 0x46 = _
    rw [Function.update_of_ne separate]
    cases ret <;> exact rep.pcLow

/-- The keep cursor is disjoint from represented guest state. -/
theorem Represents.setCursor {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret : Bool) (pointer : Byte) :
    Represents guest { outer with mem.ram := Function.update outer.mem.ram (stackBase ret + 0x101) pointer } := by
  have restored : ∀ p : Byte, p - (p - pointer) = pointer := by intro p; bv_omega
  simpa [ProgramProofs.Uxnmin.popStack, restored] using rep.popStack ret true ((guestStack guest ret).ptr - pointer)

/-- Pushing an operand has exactly the RAM footprint used by the ROM helper. -/
theorem Represents.pushStack {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret short : Bool) (value : Word) :
    Represents (pushStack guest ret short value)
      { outer with
        mem.ram := if short then
          Function.update (Function.update (Function.update outer.mem.ram
            (stackBase ret + 0x100) ((guestStack guest ret).ptr + 2))
            (stackBase ret + (guestStack guest ret).ptr.setWidth 16) ((value >>> 8).setWidth 8))
            (stackBase ret + ((guestStack guest ret).ptr + 1).setWidth 16) (value.setWidth 8)
          else Function.update (Function.update outer.mem.ram
            (stackBase ret + 0x100) ((guestStack guest ret).ptr + 1))
            (stackBase ret + (guestStack guest ret).ptr.setWidth 16) (value.setWidth 8) } := by
  cases short
  · have pushed := (rep.setStackPointer ret ((guestStack guest ret).ptr + 1)).setStackByte ret
      (guestStack guest ret).ptr (value.setWidth 8)
    cases ret <;> simpa [ProgramProofs.Uxnmin.pushStack, setStack, guestStack, Stack.push] using pushed
  · have pushed := ((rep.setStackPointer ret ((guestStack guest ret).ptr + 2)).setStackByte ret
      (guestStack guest ret).ptr ((value >>> 8).setWidth 8)).setStackByte ret
      ((guestStack guest ret).ptr + 1) (value.setWidth 8)
    cases ret <;> simpa [ProgramProofs.Uxnmin.pushStack, setStack, guestStack,
      Stack.pushWord, Stack.push, BitVec.add_assoc] using pushed

end ProgramProofs.Uxnmin
