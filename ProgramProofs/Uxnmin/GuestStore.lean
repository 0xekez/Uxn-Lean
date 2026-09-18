import ProgramProofs.Uxnmin.StoreResult

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Direct semantics for STZ, STR, and STA in all eight modes. -/
theorem guest_store (kind : AddressMode) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = kind.storeOpcode) :
    Uxn.step guest = .done (.next (storeResult kind { guest with pc := guest.pc + 1 }
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  rw [store_frontend kind guest opcode, store_action]

end ProgramProofs.Uxnmin
