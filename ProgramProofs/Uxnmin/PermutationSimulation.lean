import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.GuestPermutationDirect
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.PermutationRepresentation
import ProgramProofs.Uxnmin.StackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- All five stack permutations in all eight modes, from boundary to boundary. -/
theorem stack_simulation (operator : StackOp) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = operator.opcode) :
    ∃ guest' final, Uxn.step guest = .done (.next guest') ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  have direct := guest_stack operator guest opcode
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  have dispatchPC : dispatched.pc = operator.entry := by
    rw [opcode] at pc
    rw [pc]
    cases operator with
    | nip =>
      have high : outer.mem.ram 0x51b#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      have low : outer.mem.ram 0x51c#16 = 0xc0#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      simp [StackOp.opcode, StackOp.entry, high, low]
    | swp =>
      have high : outer.mem.ram 0x51d#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      have low : outer.mem.ram 0x51e#16 = 0xca#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      simp [StackOp.opcode, StackOp.entry, high, low]
    | rot =>
      have high : outer.mem.ram 0x51f#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      have low : outer.mem.ram 0x520#16 = 0xd7#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      simp [StackOp.opcode, StackOp.entry, high, low]
    | dup =>
      have high : outer.mem.ram 0x521#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      have low : outer.mem.ram 0x522#16 = 0xeb#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      simp [StackOp.opcode, StackOp.entry, high, low]
    | ovr =>
      have high : outer.mem.ram 0x523#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      have low : outer.mem.ram 0x524#16 = 0xf5#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
      simp [StackOp.opcode, StackOp.entry, high, low]
  obtain ⟨pushed, handlerRun, handlerPC, handlerWorking, handlerReturning, handlerMemory, handlerCode, handlerFrame, handlerReturnFrame⟩ :=
    handler_stack operator dispatched.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6))
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
      cases operator <;> simp [zero, StackOp.opcode] at opcode)
  let guest' := stackNext guest operator ((guest.mem.ram guest.pc).getLsbD 6)
    ((guest.mem.ram guest.pc).getLsbD 5) ((guest.mem.ram guest.pc).getLsbD 7)
  have represented : Represents guest' final := by
    apply (represents_permutation rep operator ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 5) ((guest.mem.ram guest.pc).getLsbD 7)).transport
    exact handlerMemory
  have nextPC : guest'.pc = guest.pc + 1 := by
    dsimp [guest', stackNext]
    cases operator <;> cases (guest.mem.ram guest.pc).getLsbD 6 <;>
      cases (guest.mem.ram guest.pc).getLsbD 7 <;> rfl
  refine ⟨guest', final, direct, run.trans (.next loop (.refl _)),
    ⟨represented, rfl, rfl, ?_⟩, boundary.toRepresents.ne_of_pc_next represented nextPC,
    ?_, handlerReturning, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerReturning]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    change pushed.mem.ram address = outer.mem.ram address
    rw [handlerMemory]
    cases operator <;> simp only [StackOp.memory]
    all_goals repeat' rw [storeStackOperand_frame _ _ _ _ _ outside]
    all_goals
      simp only [BitVec.ofNat_eq_ofNat]
      rw [Function.update_of_ne (StackScratch.cursor_separate outside
        ((guest.mem.ram guest.pc).getLsbD 6) ((guest.mem.ram guest.pc).getLsbD 7))]
      exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
