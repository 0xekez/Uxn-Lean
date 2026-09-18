import ProgramProofs.Uxnmin.GuestStack

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def incNext (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack { guest with pc := guest.pc + 1 } ret keep (operandSize short)) ret short
    (operand (guestStack guest ret) (guestStack guest ret).ptr short + 1)

theorem guest_inc (guest : Uxn.State) (base : guest.mem.ram guest.pc &&& 0x1f = 1) :
    Uxn.step guest = .done (.next (incNext guest
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  have widen (byte : Byte) : (0#8 ++ byte : Word) = byte.setWidth 16 := by
    simpa using (join_bytes 0#8 byte).symm
  have possibilities : ∀ b : Byte, b &&& 0x1f = 1 →
      b = 0x01 ∨ b = 0x21 ∨ b = 0x41 ∨ b = 0x61 ∨
      b = 0x81 ∨ b = 0xa1 ∨ b = 0xc1 ∨ b = 0xe1 := by decide
  rcases possibilities _ base with
    opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode <;>
    simp [uxn_state, uxn_step, opcode, incNext, popStack, pushStack, guestStack, operandSize, operand, widen]

end ProgramProofs.Uxnmin
