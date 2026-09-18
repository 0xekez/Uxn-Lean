import ProgramProofs.Uxnmin.ShiftAction

set_option maxHeartbeats 400000

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def shiftNext (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack { guest with pc := guest.pc + 1 } ret keep
    (1 + operandSize short)) ret short
      (shiftResult (operand (guestStack guest ret) (guestStack guest ret).ptr false)
        (operand (guestStack guest ret) ((guestStack guest ret).ptr - 1) short))

/-- Exact direct shift behavior in all short, keep and selected-stack
modes, including pointer wraparound. -/
theorem guest_shift (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x1f) :
    Uxn.step guest = .done (.next (shiftNext guest
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  rw [shift_action guest opcode, shift_stack_action]
  rfl

end ProgramProofs.Uxnmin
