import ProgramProofs.Uxnmin.LoadResult

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Direct semantics for LDZ, LDR, and LDA in all eight modes. -/
theorem guest_load (kind : AddressMode) (guest : Uxn.State)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = kind.loadOpcode) :
    Uxn.step guest = .done (.next (loadResult kind { guest with pc := guest.pc + 1 }
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      ((guest.mem.ram guest.pc).getLsbD 7))) := by
  rw [load_frontend kind guest opcode]
  cases kind
  · exact load_zero_action _ _ _ _
  · exact load_relative_action _ _ _ _
  · exact load_absolute_action _ _ _ _

end ProgramProofs.Uxnmin
