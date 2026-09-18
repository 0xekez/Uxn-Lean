import ProgramProofs.Uxnmin.Rom
import ProgramProofs.Host.Memory

namespace ProgramProofs.Uxnmin
open Uxn

-- ROM bytes deliberately used as writable immediate operands.
def MutableCode (address : Word) : Prop :=
  address = 0x13e ∨ address = 0x175 ∨ address = 0x176 ∨
  address = 0x199 ∨ address = 0x1a4 ∨ address = 0x2bf

def CodeImage (memory : Word → Byte) : Prop :=
  ∀ address : Word, 0x100 ≤ address.toNat → address.toNat < 0x555 →
    ¬ MutableCode address → memory address = rom.data[address.toNat - 0x100]!.toBitVec

theorem CodeImage.write {memory : Word → Byte} (code : CodeImage memory)
    (address : Word) (value : Byte)
    (available : address.toNat < 0x100 ∨ 0x555 ≤ address.toNat ∨ MutableCode address) :
    CodeImage (Function.update memory address value) := by
  intro location lower upper immutable
  have different : location ≠ address := by
    rintro rfl
    rcases available with before | after | mutable
    · omega
    · omega
    · exact immutable mutable
  rw [Function.update_of_ne different]
  exact code location lower upper immutable

end ProgramProofs.Uxnmin
