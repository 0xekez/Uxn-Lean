import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.JumpHandlers
import ProgramProofs.Uxnmin.RepresentationPC
import ProgramProofs.Uxnmin.StackFrame
import ProgramProofs.Uxnmin.OperandRepresentation
import ProgramProofs.Uxnmin.GuestJump

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Every JMP mode returns to an evaluation boundary with positive native progress. -/
theorem jump_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 12) :
    ∃ guest' first final, Uxn.step guest = .done (.next guest') ∧
      Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary guest' final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  have tableHigh : outer.mem.ram 0x52d#16 = 0x04#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x52e#16 = 0x2e#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x42e := by
    rw [opcode] at pc
    simpa [tableHigh, tableLow] using pc
  obtain ⟨pushed, handlerRun, handlerPC, handlerWorking, handlerReturning, handlerMemory, handlerCode, handlerFrame, handlerReturnFrame⟩ :=
    handler_jmp dispatched.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6)) (guest.pc + 1)
      (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
      (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0)
      ((guest.mem.ram guest.pc).getLsbD 5) dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> simp [stackBase])
      rep.code sourceHigh sourceLow short rep.pcHigh rep.pcLow keep
      (by cases (guest.mem.ram guest.pc).getLsbD 7 <;> decide) cursor
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  obtain ⟨first, firstStep, suffix⟩ := header_progress boundary.toRepresents rep headerRun
  have run : Reaches first pushed := by
    apply suffix.trans
    simpa only [returnShape, ← dispatchPC, machine] using handlerRun
  have pushedTop : pushed.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [handlerFrame _ (by simp [working])]
    exact top
  let final : Uxn.State := { pushed with pc := 0x16d, mem.wstk.ptr := 0 }
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed handlerCode handlerPC (handlerWorking.trans working) (by
      rw [pushedTop]
      intro zero
      simp [zero] at opcode)
  let guest' := jumpNext guest ((guest.mem.ram guest.pc).getLsbD 6)
    ((guest.mem.ram guest.pc).getLsbD 5) ((guest.mem.ram guest.pc).getLsbD 7)
  have represented : Represents guest' final := by
    have value := rep.operand ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 5) (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
    simp only [guestStack_pc] at value
    have changed := (rep.popStack ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 7) (operandSize ((guest.mem.ram guest.pc).getLsbD 5))).setPC
        (jumpTarget (guest.pc + 1)
          (operand (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6))
            (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
            ((guest.mem.ram guest.pc).getLsbD 5))
          ((guest.mem.ram guest.pc).getLsbD 5))
    apply changed.transport
    change pushed.mem.ram = _
    simpa only [value, operandSize, guestStack_pc, BitVec.ofNat_eq_ofNat] using handlerMemory
  refine ⟨guest', first, final, guest_jump guest opcode, firstStep, run.trans (.next loop (.refl _)),
    ⟨represented, rfl, rfl, ?_⟩,
    ?_, handlerReturning, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerReturning]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    change pushed.mem.ram address = outer.mem.ram address
    have notHigh : address ≠ 0x45 := by intro h; apply noPop; simp [PopScratch, h]
    have notLow : address ≠ 0x46 := by intro h; apply noPop; simp [PopScratch, h]
    rw [handlerMemory, Function.update_of_ne notLow, Function.update_of_ne notHigh]
    simp only [BitVec.ofNat_eq_ofNat]
    simpa only [Function.update_of_ne (StackScratch.cursor_separate outside
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 7))]
      using headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
