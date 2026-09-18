import ProgramProofs.Uxnmin.ImmediateHeader
import ProgramProofs.Uxnmin.LiteralHandler
import ProgramProofs.Uxnmin.GuestImmediate
import ProgramProofs.Uxnmin.RepresentationPC
import ProgramProofs.Uxnmin.OperandRepresentation
import ProgramProofs.Uxnmin.StackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Every LIT variant pushes the confined immediate bytes onto the selected guest stack. -/
theorem literal_simulation (short ret : Bool) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = (ImmediateKind.lit short ret).opcode)
    (firstBound : (guest.pc + 1).toNat < ramSize)
    (secondBound : short = true → (guest.pc + 2).toNat < ramSize) :
    ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary (immediateNext (.lit short ret) guest) final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, entry, working, top, returnShape, returnFrame,
    mode, _, sourceHigh, sourceLow, headerMemory⟩ := immediate_header (.lit short ret) boundary confined opcode
  change dispatched.pc = 0x36d at entry
  obtain ⟨first, firstStep, suffix⟩ := header_progress boundary.toRepresents rep headerRun
  have high : dispatched.mem.ram 0x40#16 = (stackBase ret >>> 8).setWidth 8 := by
    cases short <;> cases ret <;> simpa [ImmediateKind.opcode] using sourceHigh
  have low : dispatched.mem.ram 0x41#16 = (stackBase ret).setWidth 8 := by
    cases short <;> cases ret <;> simpa [ImmediateKind.opcode] using sourceLow
  have shortMode : dispatched.mem.ram 0x44#16 = if short then 1 else 0 := by
    cases short <;> cases ret <;> simpa [ImmediateKind.opcode] using mode
  obtain ⟨pushed, handlerRun, handlerPC, handlerWP, handlerRP, handlerRAM, handlerCode, handlerWF, handlerRF⟩ :=
    handler_lit dispatched.mem.ram (stackBase ret) (guest.pc + 1) (guestStack guest ret).ptr short
      dispatched.mem.wstk {dispatched.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170
      (by cases ret <;> simp [stackBase]) rep.code high low shortMode rep.pcHigh rep.pcLow
      (by simpa using rep.stackPointer ret)
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches first pushed := by
    apply suffix.trans
    simpa only [returnShape, ← entry, machine] using handlerRun
  have pushedTop : pushed.mem.wstk.data 0#8 = (ImmediateKind.lit short ret).opcode := by
    rw [handlerWF _ (by simp [working])]
    exact top
  let final : Uxn.State := {pushed with pc := 0x16d, mem.wstk.ptr := 0}
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed handlerCode handlerPC (handlerWP.trans working) (by
      rw [pushedTop]
      cases short <;> cases ret <;> decide)
  have value : peekValue dispatched.mem.ram (guest.pc + 1) 0xffff short =
      if short then immediateWord guest else (guest.mem.ram (guest.pc + 1)).setWidth 16 := by
    have mask (x : Word) : x &&& 0xffff#16 = x := BitVec.and_allOnes
    cases modeEq : short
    · simp only [peekValue, Bool.false_eq_true, if_false, rep.ram _ firstBound]
      simpa using (join_bytes 0#8 (guest.mem.ram (guest.pc + 1))).symm
    · simp only [peekValue, if_true, BitVec.ofNat_eq_ofNat, mask]
      have firstValue := rep.ram _ firstBound
      have secondValue := rep.ram _ (secondBound modeEq)
      simp only [BitVec.ofNat_eq_ofNat] at firstValue secondValue
      simp only [immediateWord, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, firstValue, secondValue]
  have represented : Represents (immediateNext (.lit short ret) guest) final := by
    have changed := ((rep.storeOperand ret short
      (if short then immediateWord guest else (guest.mem.ram (guest.pc + 1)).setWidth 16)).setPC
      (guest.pc + (if short then 3 else 2))).transport (replacement := final) (by
        change pushed.mem.ram = _
        rw [handlerRAM, value]
        cases short <;> simp [guestStack, BitVec.add_assoc])
    cases short <;> cases ret <;> simpa [immediateNext, pushStack] using changed
  refine ⟨first, final, firstStep, run.trans (.next loop (.refl _)), ⟨represented, rfl, rfl, ?_⟩, ?_, handlerRP, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerRP]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    have notHigh : address ≠ 0x45 := by intro h; apply noPop; simp [PopScratch, h]
    have notLow : address ≠ 0x46 := by intro h; apply noPop; simp [PopScratch, h]
    change pushed.mem.ram address = outer.mem.ram address
    rw [handlerRAM, Function.update_of_ne notLow, Function.update_of_ne notHigh,
      storeStackOperand_frame _ _ _ _ _ outside]
    exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerRF _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
