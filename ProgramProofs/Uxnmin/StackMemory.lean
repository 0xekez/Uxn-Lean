import ProgramProofs.Uxnmin.PushOperand

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

theorem store_operand_frame (memory : Word → Byte) (softwareStack : Word)
    (pointer : Byte) (value : Word) (short : Bool)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (address : Word) (bound : address.toNat < 0x555) :
    storeStackOperand memory softwareStack pointer value short address = memory address := by
  have above : 0x555 ≤ softwareStack.toNat := by
    rcases selected with rfl | rfl <;> decide
  have below : softwareStack.toNat ≤ 0x657 := by
    rcases selected with rfl | rfl <;> decide
  have ptrSeparate : address ≠ softwareStack + 0x100#16 := by bv_omega
  have dataSeparate (index : Byte) : address ≠ softwareStack + index.setWidth 16 := by bv_omega
  cases short <;> simp [storeStackOperand, Function.update_of_ne, ptrSeparate, dataSeparate]

theorem store_operand_code (memory : Word → Byte) (softwareStack : Word)
    (pointer : Byte) (value : Word) (short : Bool)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657) (code : CodeImage memory) :
    CodeImage (storeStackOperand memory softwareStack pointer value short) := by
  intro address lower upper immutable
  rw [store_operand_frame memory softwareStack pointer value short selected address upper]
  exact code address lower upper immutable

theorem store_operand_pointer (memory : Word → Byte) (softwareStack : Word)
    (pointer : Byte) (value : Word) (short : Bool) :
    storeStackOperand memory softwareStack pointer value short (softwareStack + 0x100#16) =
      pointer + (if short then 2#8 else 1#8) := by
  have separate (index : Byte) : softwareStack + 0x100#16 ≠ softwareStack + index.setWidth 16 := by
    bv_omega
  cases short <;> simp [storeStackOperand, Function.update_of_ne, separate]

end ProgramProofs.Uxnmin
