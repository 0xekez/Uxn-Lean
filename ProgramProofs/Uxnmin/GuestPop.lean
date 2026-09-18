import ProgramProofs.Host.Reduction

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

-- The complete direct instruction effect, for all eight POP modes.
theorem guest_pop (vm : Uxn.State) (base : vm.mem.ram vm.pc &&& 0x1f = 2) :
    Uxn.step vm = .done (.next (
      if (vm.mem.ram vm.pc).getLsbD 7 then { vm with pc := vm.pc + 1 }
      else if (vm.mem.ram vm.pc).getLsbD 6 then
        { vm with
          pc := vm.pc + 1
          mem.rstk.ptr := vm.mem.rstk.ptr - (if (vm.mem.ram vm.pc).getLsbD 5 then 2 else 1) }
      else
        { vm with
          pc := vm.pc + 1
          mem.wstk.ptr := vm.mem.wstk.ptr - (if (vm.mem.ram vm.pc).getLsbD 5 then 2 else 1) })) := by
  have possibilities : ∀ b : Byte, b &&& 0x1f = 2 →
      b = 0x02 ∨ b = 0x22 ∨ b = 0x42 ∨ b = 0x62 ∨
      b = 0x82 ∨ b = 0xa2 ∨ b = 0xc2 ∨ b = 0xe2 := by decide
  rcases possibilities (vm.mem.ram vm.pc) base with
    opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode <;>
    simp [uxn_state, uxn_step, opcode]

end ProgramProofs.Uxnmin
