import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.SubroutineHandler
import ProgramProofs.Uxnmin.RepresentationPC
import ProgramProofs.Uxnmin.RepresentationSelector
import ProgramProofs.Uxnmin.StackFrame
import ProgramProofs.Uxnmin.OperandRepresentation
import ProgramProofs.Uxnmin.GuestSubroutine

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Every JSR mode returns to a boundary after saving the return PC. -/
theorem subroutine_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 14) :
    ∃ guest' first final, Uxn.step guest = .done (.next guest') ∧
      Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary guest' final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory, destinationHigh, destinationLow⟩ :=
    instruction_header_full boundary confined
  have tableHigh : outer.mem.ram 0x531#16 = 0x04#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x532#16 = 0x40#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x440 := by
    rw [opcode] at pc
    simpa [tableHigh, tableLow] using pc
  obtain ⟨pushed, handlerRun, handlerPC, handlerWorking, handlerReturning, handlerMemory, handlerCode, handlerFrame, handlerReturnFrame⟩ :=
    handler_jsr dispatched.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6))
      (stackBase (!((guest.mem.ram guest.pc).getLsbD 6))) (guest.pc + 1)
      (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
      (guestStack guest (!((guest.mem.ram guest.pc).getLsbD 6))).ptr
      (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0)
      ((guest.mem.ram guest.pc).getLsbD 5) dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> simp [stackBase])
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> simp [stackBase])
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> decide)
      rep.code sourceHigh sourceLow destinationHigh destinationLow short rep.pcHigh rep.pcLow keep
      (by cases (guest.mem.ram guest.pc).getLsbD 7 <;> decide) cursor
      (by simpa using rep.stackPointer (!((guest.mem.ram guest.pc).getLsbD 6)))
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
  let guest' := subroutineNext guest ((guest.mem.ram guest.pc).getLsbD 6)
    ((guest.mem.ram guest.pc).getLsbD 5) ((guest.mem.ram guest.pc).getLsbD 7)
  have represented : Represents guest' final := by
    apply ((((rep.popStack ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 7) (operandSize ((guest.mem.ram guest.pc).getLsbD 5))).setSource
      (stackBase (!((guest.mem.ram guest.pc).getLsbD 6)))).storeOperand
      (!((guest.mem.ram guest.pc).getLsbD 6)) true (guest.pc + 1)).setPC
      (jumpTarget (guest.pc + 1) (operand (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6))
        (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
        ((guest.mem.ram guest.pc).getLsbD 5)) ((guest.mem.ram guest.pc).getLsbD 5))).transport
    have value := rep.operand ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 5) (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
    simp only [guestStack_pc] at value
    change pushed.mem.ram = _
    rw [handlerMemory, value]
    cases (guest.mem.ram guest.pc).getLsbD 6 <;>
      cases (guest.mem.ram guest.pc).getLsbD 7 <;>
      simp [ProgramProofs.Uxnmin.popStack, guestStack, operandSize]
  refine ⟨guest', first, final, guest_subroutine guest opcode, firstStep, run.trans (.next loop (.refl _)),
    ⟨represented, rfl, rfl, ?_⟩, ?_, handlerReturning, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerReturning]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    change pushed.mem.ram address = outer.mem.ram address
    have notHigh : address ≠ 0x40 := by intro h; apply noPop; simp [PopScratch, h]
    have notLow : address ≠ 0x41 := by intro h; apply noPop; simp [PopScratch, h]
    have notPCHigh : address ≠ 0x45 := by intro h; apply noPop; simp [PopScratch, h]
    have notPCLow : address ≠ 0x46 := by intro h; apply noPop; simp [PopScratch, h]
    rw [handlerMemory, Function.update_of_ne notPCLow, Function.update_of_ne notPCHigh, storeStackOperand_frame _ _ _ _ _ outside,
      Function.update_of_ne notLow, Function.update_of_ne notHigh]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [Function.update_of_ne (StackScratch.cursor_separate outside
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 7))]
    exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
