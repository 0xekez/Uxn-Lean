import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.IncHandler
import ProgramProofs.Uxnmin.OperandRepresentation
import ProgramProofs.Uxnmin.GuestInc

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Every INC mode implements one direct instruction and returns to the loop. -/
theorem inc_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 1) :
    ∃ guest' final, Uxn.step guest = .done (.next guest') ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  have tableHigh : outer.mem.ram 0x517#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x518#16 = 0xb4#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x3b4 := by
    rw [opcode] at pc
    simpa [tableHigh, tableLow] using pc
  obtain ⟨pushed, handlerRun, handlerPC, handlerWorking, handlerReturning, handlerMemory, handlerCode, handlerFrame, handlerReturnFrame⟩ :=
    handler_inc dispatched.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6))
      (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
      (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0)
      ((guest.mem.ram guest.pc).getLsbD 5) dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> simp [stackBase])
      rep.code sourceHigh sourceLow short keep
      (by cases (guest.mem.ram guest.pc).getLsbD 7 <;> decide) cursor
      (by simpa using rep.stackPointer ((guest.mem.ram guest.pc).getLsbD 6))
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches outer pushed := by
    apply headerRun.trans
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
  let guest' := incNext guest ((guest.mem.ram guest.pc).getLsbD 6)
    ((guest.mem.ram guest.pc).getLsbD 5) ((guest.mem.ram guest.pc).getLsbD 7)
  have represented : Represents guest' final := by
    apply ((rep.popStack ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 7) (operandSize ((guest.mem.ram guest.pc).getLsbD 5))).storeOperand
      ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 5)
      (operand (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6))
        (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
        ((guest.mem.ram guest.pc).getLsbD 5) + 1)).transport
    have value := rep.operand ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 5) (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
    simp only [guestStack_pc] at value
    change pushed.mem.ram = _
    rw [handlerMemory, value]
    cases hs : (guest.mem.ram guest.pc).getLsbD 5 <;>
      cases hr : (guest.mem.ram guest.pc).getLsbD 6 <;>
      cases hk : (guest.mem.ram guest.pc).getLsbD 7 <;>
      simp [ProgramProofs.Uxnmin.popStack, guestStack, storeStackOperand, operandSize]
  have nextPC : guest'.pc = guest.pc + 1 := by
    dsimp [guest', incNext]
    cases (guest.mem.ram guest.pc).getLsbD 6 <;>
      cases (guest.mem.ram guest.pc).getLsbD 5 <;>
      cases (guest.mem.ram guest.pc).getLsbD 7 <;> rfl
  refine ⟨guest', final, guest_inc guest opcode, run.trans (.next loop (.refl _)),
    ⟨represented, rfl, rfl, ?_⟩, boundary.toRepresents.ne_of_pc_next represented nextPC,
    ?_, handlerReturning, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerReturning]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    have outsideStack : address.toNat < 0x555 ∨ 0x759 ≤ address.toNat := by
      have excluded : ¬ (0x555 ≤ address.toNat ∧ address.toNat < 0x759) :=
        fun h => outside (.inr h)
      omega
    change pushed.mem.ram address = outer.mem.ram address
    rw [handlerMemory]
    cases hs : (guest.mem.ram guest.pc).getLsbD 5 <;>
      cases hr : (guest.mem.ram guest.pc).getLsbD 6 <;>
      cases hk : (guest.mem.ram guest.pc).getLsbD 7 <;>
      simp only [storeStackOperand, stackBase, Bool.false_eq_true, if_false, if_true]
    all_goals simp (disch := bv_omega) only [Function.update_of_ne]
    all_goals exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
