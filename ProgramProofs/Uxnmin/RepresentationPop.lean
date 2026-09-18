import ProgramProofs.Uxnmin.Representation

namespace ProgramProofs.Uxnmin
open Uxn

def popStack (guest : Uxn.State) (ret keep : Bool) (amount : Byte) : Uxn.State :=
  if keep then guest
  else if ret then { guest with mem.rstk.ptr := guest.mem.rstk.ptr - amount }
  else { guest with mem.wstk.ptr := guest.mem.wstk.ptr - amount }

theorem Represents.popStack {guest outer : Uxn.State} (rep : Represents guest outer)
    (ret keep : Bool) (amount : Byte) :
    Represents (popStack guest ret keep amount)
      { outer with
        mem.ram := Function.update outer.mem.ram
          (stackBase ret + (0x100 + (if keep then 1#8 else 0#8).setWidth 16))
          ((guestStack guest ret).ptr - amount) } := by
  constructor
  · exact rep.code.write _ _ (.inr (.inl (by
      cases ret <;> cases keep <;> decide)))
  · intro address confined
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by
      cases ret <;> cases keep <;>
        dsimp [stackBase, relocate, ramSize] at *
      all_goals bv_omega)]
    cases ret <;> cases keep <;> exact rep.ram address confined
  · intro selected index
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by
      cases ret <;> cases keep <;> cases selected <;> dsimp [stackBase]
      all_goals bv_omega)]
    cases ret <;> cases keep <;> cases selected <;> exact rep.stackData _ index
  · intro selected
    have working := rep.stackPointer false
    have returning := rep.stackPointer true
    change outer.mem.ram 0x655#16 = guest.mem.wstk.ptr at working
    change outer.mem.ram 0x757#16 = guest.mem.rstk.ptr at returning
    cases ret <;> cases keep <;> cases selected <;>
      simp [stackBase, guestStack, ProgramProofs.Uxnmin.popStack, working, returning]
  · cases ret <;> cases keep <;>
      simpa [stackBase, ProgramProofs.Uxnmin.popStack] using rep.pcHigh
  · cases ret <;> cases keep <;>
      simpa [stackBase, ProgramProofs.Uxnmin.popStack] using rep.pcLow

theorem Represents.transport {guest outer replacement : Uxn.State}
    (rep : Represents guest outer) (ram : replacement.mem.ram = outer.mem.ram) :
    Represents guest replacement := by
  cases rep
  constructor <;> (simp only [ram]; assumption)

end ProgramProofs.Uxnmin
