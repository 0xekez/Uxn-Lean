import ProgramProofs.Uxnmin.ImmediateHeader
import ProgramProofs.Uxnmin.ImmediateJump
import ProgramProofs.Uxnmin.GuestImmediate
import ProgramProofs.Uxnmin.RepresentationPC
import ProgramProofs.Uxnmin.RepresentationStack

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JMI implements the same displacement, including jumps back to its own boundary. -/
theorem immediate_jump_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = 0x40)
    (firstBound : (guest.pc + 1).toNat < ramSize) (secondBound : (guest.pc + 2).toNat < ramSize) :
    ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary (immediateNext .jmi guest) final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, entry, working, top, returnShape, returnFrame,
    _, _, _, _, headerMemory⟩ := immediate_header .jmi boundary confined opcode
  change dispatched.pc = 0x3a4 at entry
  obtain ⟨first, firstStep, suffix⟩ := header_progress boundary.toRepresents rep headerRun
  obtain ⟨pushed, handlerRun, handlerPC, handlerWP, handlerRP, handlerRAM, handlerCode, handlerWF, handlerRF⟩ :=
    handler_jmi dispatched.mem.ram (guest.pc + 1) 0x170 dispatched.mem.wstk
      {dispatched.mem.rstk with ptr := outer.mem.rstk.ptr} rep.code rep.pcHigh rep.pcLow
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches first pushed := by
    apply suffix.trans
    simpa only [returnShape, ← entry, machine] using handlerRun
  have pushedTop : pushed.mem.wstk.data 0#8 = 0x40#8 := by
    rw [handlerWF _ (by simp [working])]
    exact top
  let final : Uxn.State := {pushed with pc := 0x16d, mem.wstk.ptr := 0}
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed handlerCode handlerPC (handlerWP.trans working) (by rw [pushedTop]; decide)
  have operand : dispatched.mem.ram (relocate (guest.pc + 1)) ++
      dispatched.mem.ram (relocate (guest.pc + 1 + 1)) = immediateWord guest := by
    rw [rep.ram _ firstBound, rep.ram _ (by simpa [BitVec.add_assoc] using secondBound)]
    simp [immediateWord, BitVec.add_assoc]
  have represented : Represents (immediateNext .jmi guest) final := by
    apply (rep.setPC (guest.pc + 3 + immediateWord guest)).transport
    change pushed.mem.ram = _
    rw [handlerRAM, operand]
    congr 2 <;> bv_omega
  refine ⟨first, final, firstStep, run.trans (.next loop (.refl _)), ⟨represented, rfl, rfl, ?_⟩, ?_, handlerRP, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerRP]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    have notHigh : address ≠ 0x45 := by intro h; apply noPop; simp [PopScratch, h]
    have notLow : address ≠ 0x46 := by intro h; apply noPop; simp [PopScratch, h]
    change pushed.mem.ram address = outer.mem.ram address
    rw [handlerRAM, Function.update_of_ne notLow, Function.update_of_ne notHigh]
    exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerRF _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
