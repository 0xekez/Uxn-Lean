import ProgramProofs.Uxnmin.Representation

set_option maxRecDepth 8192

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- A completed nonzero-opcode handler returns to the next guest instruction. -/
theorem return_to_loop (vm : Uxn.State) (code : CodeImage vm.mem.ram)
    (pc : vm.pc = 0x170) (working : vm.mem.wstk.ptr = 1)
    (ok : vm.mem.wstk.data 0#8 ≠ 0#8) :
    Uxn.step vm = .done (.next { vm with pc := 0x16d, mem.wstk.ptr := 0 }) := by
  have call : vm.mem.ram 0x170#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have high : vm.mem.ram 0x171#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have low : vm.mem.ram 0x172#16 = 0xfa#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  change Uxn.step (machine vm.mem.ram vm.pc vm.mem.wstk vm.mem.rstk) = _
  rw [pc]
  simp [uxn_state, uxn_step, call, high, low, working, ok]

/-- Advancing the represented PC forces a nonempty native execution. -/
theorem Represents.ne_of_pc_next {guest guest' outer final : Uxn.State}
    (before : Represents guest outer) (after : Represents guest' final)
    (pc : guest'.pc = guest.pc + 1) : outer ≠ final := by
  intro same
  have high := after.pcHigh
  have low := after.pcLow
  rw [← same, before.pcHigh, pc] at high
  rw [← same, before.pcLow, pc] at low
  have equal : guest.pc = guest.pc + 1 := by
    calc
      guest.pc = (guest.pc >>> 8).setWidth 8 ++ guest.pc.setWidth 8 := (append_split _).symm
      _ = ((guest.pc + 1) >>> 8).setWidth 8 ++ (guest.pc + 1).setWidth 8 :=
        congrArg₂ BitVec.append high low
      _ = guest.pc + 1 := append_split _
  bv_omega

end ProgramProofs.Uxnmin
