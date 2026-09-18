import ProgramProofs.Uxnmin.MemoryAccess
import ProgramProofs.Uxnmin.OpcodeModes

set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def loadAction (kind : AddressMode) (mode : Mode) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    match kind with
    | .zero => ops.inc (← ops.load (← ops.dec8))
    | .relative => ops.inc (← ops.load ((← get).pc + (← ops.dec8).signExtend 16))
    | .absolute => ops.inc (← ops.load (← ops.dec16))
    return .done (.next (← get))

/-- Opcode dispatch selects the corresponding memory-load action. -/
theorem load_frontend (kind : AddressMode) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = kind.loadOpcode) :
    Uxn.step guest = (loadAction kind
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ { guest with pc := guest.pc + 1 }).fst := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = kind.loadOpcode) :
      Instruction.ofByte byte = .normal kind.loadOperation
        ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte _ (by cases kind <;> decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;>
      subst byte <;> cases kind <;> rfl
  dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
  rw [decoded _ opcode]
  cases kind <;> rfl

end ProgramProofs.Uxnmin
