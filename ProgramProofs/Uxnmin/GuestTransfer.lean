import ProgramProofs.Uxnmin.OpcodeModes
import ProgramProofs.Uxnmin.GuestStack

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def transferNext (guest : Uxn.State) (ret short keep : Bool) : Uxn.State :=
  pushStack (popStack { guest with pc := guest.pc + 1 } ret keep (operandSize short)) (!ret) short
    (operand (guestStack guest ret) (guestStack guest ret).ptr short)

theorem guest_transfer (guest : Uxn.State) (base : guest.mem.ram guest.pc &&& 0x1f = 15) :
    Uxn.step guest = .done (.next (transferNext guest
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  have widen (byte : Byte) : (0#8 ++ byte : Word) = byte.setWidth 16 := by
    simpa using (join_bytes 0#8 byte).symm
  rcases opcode_modes (guest.mem.ram guest.pc) 15 (by decide) base with
    opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode <;>
    simp [uxn_state, uxn_step, opcode, transferNext, pushStack, popStack, guestStack,
      operandSize, operand, widen]

end ProgramProofs.Uxnmin
