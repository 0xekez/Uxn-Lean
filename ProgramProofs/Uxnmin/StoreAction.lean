import ProgramProofs.Uxnmin.MemoryAccess
import ProgramProofs.Uxnmin.OpcodeModes

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def AddressMode.storeOpcode : AddressMode → Byte
  | .zero => 0x11 | .relative => 0x13 | .absolute => 0x15

def AddressMode.storeOperation : AddressMode → Uxn.Op
  | .zero => .stz | .relative => .str | .absolute => .sta

def storeAction (kind : AddressMode) (mode : Mode) : StateM Uxn.State Step :=
  withMode mode fun ops => do
    match kind with
    | .zero =>
      let address ← ops.dec8
      ops.store address (← ops.dec)
    | .relative =>
      let offset ← ops.dec8
      ops.store ((← get).pc + offset.signExtend 16) (← ops.dec)
    | .absolute =>
      let address ← ops.dec16
      ops.store address (← ops.dec)
    return .done (.next (← get))

/-- Opcode dispatch selects the corresponding memory-store action. -/
theorem store_frontend (kind : AddressMode) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = kind.storeOpcode) :
    Uxn.step guest = (storeAction kind
      ⟨(guest.mem.ram guest.pc).getLsbD 5, (guest.mem.ram guest.pc).getLsbD 7,
        (guest.mem.ram guest.pc).getLsbD 6⟩ { guest with pc := guest.pc + 1 }).fst := by
  have decoded (byte : Byte) (base : byte &&& 0x1f = kind.storeOpcode) :
      Instruction.ofByte byte = .normal kind.storeOperation
        ⟨byte.getLsbD 5, byte.getLsbD 7, byte.getLsbD 6⟩ := by
    rcases opcode_modes byte _ (by cases kind <;> decide) base with
      eq | eq | eq | eq | eq | eq | eq | eq <;>
      subst byte <;> cases kind <;> rfl
  dsimp only [Uxn.step, Uxn.stepM, Uxn.fetchInstruction, Uxn.fetchByte, uxn_state]
  rw [decoded _ opcode]
  cases kind <;> rfl

end ProgramProofs.Uxnmin
