import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.ArithmeticHandlers
import ProgramProofs.Uxnmin.GuestArithmetic
import ProgramProofs.Uxnmin.StackFrame
import ProgramProofs.Uxnmin.Return

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The seven arithmetic operations in all eight modes, from one evaluation
boundary to the next, preserving device bookkeeping and the active native frame. -/
theorem arithmetic_simulation (operator : ArithmeticOp) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode) :
    ∃ guest' final, Uxn.step guest = .done (.next guest') ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  let ret := (guest.mem.ram guest.pc).getLsbD 6
  let short := (guest.mem.ram guest.pc).getLsbD 5
  let keep := (guest.mem.ram guest.pc).getLsbD 7
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    mode, kept, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  have dispatchPC : dispatched.pc = operator.entry := by
    rw [opcode] at pc
    apply pc.trans
    rw [boundary.code _ (by cases operator <;> decide) (by cases operator <;> decide)
      (by cases operator <;> simp [ArithmeticOp.guestOpcode, MutableCode]),
      boundary.code _ (by cases operator <;> decide) (by cases operator <;> decide)
      (by cases operator <;> simp [ArithmeticOp.guestOpcode, MutableCode])]
    cases operator <;> rfl
  obtain ⟨computed, arithmeticRun, arithmeticPC, arithmeticWorking, arithmeticReturning,
    arithmeticMemory, arithmeticCode, arithmeticFrame, arithmeticReturnFrame⟩ :=
    handler_arithmetic operator dispatched.mem.ram (stackBase ret)
      (guestStack guest ret).ptr (if keep then 1 else 0) short dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases ret <;> simp [stackBase]) rep.code sourceHigh sourceLow mode kept
      (by cases keep <;> decide) cursor
      (by simpa only [guestStack_pc, BitVec.ofNat_eq_ofNat] using rep.stackPointer ret)
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches outer computed := by
    apply headerRun.trans
    simpa only [returnShape, ← dispatchPC, machine] using arithmeticRun
  have nonzero : guest.mem.ram guest.pc ≠ 0#8 := by
    intro zero
    cases operator <;> simp [zero, ArithmeticOp.guestOpcode] at opcode
  have computedTop : computed.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [arithmeticFrame _ (by simp [working])]
    exact top
  let final : Uxn.State := { computed with pc := 0x16d, mem.wstk.ptr := 0 }
  have loop : Uxn.step computed = .done (.next final) :=
    return_to_loop computed arithmeticCode arithmeticPC (arithmeticWorking.trans working)
      (computedTop ▸ nonzero)
  let guest' := arithmeticNext guest operator ret short keep
  have represented : Represents guest' final := by
    apply ((rep.popStack ret keep (operandSize short + operandSize short)).storeOperand ret short
      (operator.result (operand (guestStack guest ret) (guestStack guest ret).ptr short)
        (operand (guestStack guest ret) ((guestStack guest ret).ptr - operandSize short) short))).transport
    change computed.mem.ram = _
    rw [arithmeticMemory, rep.operand, rep.operand]
    cases keep <;>
      simp [guestStack_pc, popStack_pointer, operandSize,
        BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
  refine ⟨guest', final, guest_arithmetic operator guest opcode,
    run.trans (.next loop (.refl _)), ⟨represented, rfl, rfl, ?_⟩, ?_, ?_, arithmeticReturning, ?_⟩
  · change computed.mem.rstk.ptr.toNat ≤ 245
    rw [arithmeticReturning]
    exact boundary.returnSpace
  · apply boundary.toRepresents.ne_of_pc_next represented
    have preserved (state : Uxn.State) (ret short keep : Bool) :
        (arithmeticNext state operator ret short keep).pc = state.pc + 1 := by
      cases ret <;> cases short <;> cases keep <;> rfl
    exact preserved guest ret short keep
  · intro address outside
    change computed.mem.ram address = outer.mem.ram address
    rw [arithmeticMemory, storeStackOperand_frame _ ret short _ _ outside]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [Function.update_of_ne (StackScratch.cursor_separate outside ret keep)]
    exact headerMemory address (fun scratch => outside (.inl scratch))
  · intro index below
    change computed.mem.rstk.data index = outer.mem.rstk.data index
    rw [arithmeticReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
