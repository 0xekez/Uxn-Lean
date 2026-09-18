import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.PopHandler
import ProgramProofs.Uxnmin.RepresentationPop
import ProgramProofs.Uxnmin.GuestPop

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- All eight current-ROM POP opcodes, from one evaluation boundary to the next.
The result preserves all device bookkeeping and every active native return-frame byte. -/
theorem pop_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x02) :
    ∃ guest' final, Uxn.step guest = .done (.next guest') ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, ¬ PopScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  have tableHigh : outer.mem.ram 0x519#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x51a#16 = 0xbb#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x3bb := by
    rw [opcode] at pc
    simpa [tableHigh, tableLow] using pc
  obtain ⟨popped, popRun, popPC, popWorking, popReturning, popMemory, popCode, popFrame, popReturnFrame⟩ :=
    handler_pop dispatched.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6))
      (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
      (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0)
      ((guest.mem.ram guest.pc).getLsbD 5) dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> simp [stackBase])
      rep.code sourceHigh sourceLow short keep
      (by cases (guest.mem.ram guest.pc).getLsbD 7 <;> decide) cursor
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches outer popped := by
    apply headerRun.trans
    simpa only [returnShape, ← dispatchPC, machine] using popRun
  have poppedTop : popped.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [popFrame _ (by simp [working])]
    exact top
  have poppedWorking : popped.mem.wstk.ptr = 1 := popWorking.trans working
  let final : Uxn.State := { popped with pc := 0x16d, mem.wstk.ptr := 0 }
  have loop : Uxn.step popped = .done (.next final) :=
    return_to_loop popped popCode popPC poppedWorking (by
      rw [poppedTop]
      intro zero
      simp [zero] at opcode)
  let guest' := popStack { guest with pc := guest.pc + 1 }
    ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 7)
    (if (guest.mem.ram guest.pc).getLsbD 5 then 2 else 1)
  have guestStep : Uxn.step guest = .done (.next guest') := by
    simpa only [guest', popStack] using guest_pop guest opcode
  have represented : Represents guest' final := by
    apply (rep.popStack ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 7)
      (if (guest.mem.ram guest.pc).getLsbD 5 then 2 else 1)).transport
    simpa [final, guestStack] using popMemory
  refine ⟨guest', final, guestStep, run.trans (.next loop (.refl _)),
    ⟨represented, rfl, rfl, ?_⟩, ?_, ?_, popReturning, ?_⟩
  · change popped.mem.rstk.ptr.toNat ≤ 245
    rw [popReturning]
    exact boundary.returnSpace
  · apply boundary.toRepresents.ne_of_pc_next represented
    dsimp [guest', popStack]
    split <;> first | rfl | split <;> rfl
  · intro address outside
    change popped.mem.ram address = outer.mem.ram address
    rw [popMemory, Function.update_of_ne]
    · exact headerMemory address outside
    · cases (guest.mem.ram guest.pc).getLsbD 6 <;>
        cases (guest.mem.ram guest.pc).getLsbD 7 <;>
        simp_all [PopScratch, stackBase]
  · intro index below
    change popped.mem.rstk.data index = outer.mem.rstk.data index
    rw [popReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
