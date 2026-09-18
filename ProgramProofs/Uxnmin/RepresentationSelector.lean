import ProgramProofs.Uxnmin.RepresentationPop
import ProgramProofs.Uxnmin.Return

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Selecting another software stack changes no represented guest state. -/
theorem Represents.setSource {guest outer : Uxn.State} (rep : Represents guest outer) (source : Word) :
    Represents guest
      { outer with mem.ram := (Function.update
          (Function.update outer.mem.ram 0x40 ((source >>> 8).setWidth 8))
          0x41 (source.setWidth 8)) } := by
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
  · simpa using rep.pcHigh
  · simpa using rep.pcLow

end ProgramProofs.Uxnmin
