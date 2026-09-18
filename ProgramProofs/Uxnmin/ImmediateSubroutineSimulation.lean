import ProgramProofs.Uxnmin.ImmediateHeader
import ProgramProofs.Uxnmin.ImmediateJump
import ProgramProofs.Uxnmin.ImmediateSave
import ProgramProofs.Uxnmin.RepresentationSelector
import ProgramProofs.Uxnmin.OperandRepresentation
import ProgramProofs.Uxnmin.StackFrame
import ProgramProofs.Host.StackFrame
import ProgramProofs.Uxnmin.GuestImmediate
import ProgramProofs.Uxnmin.RepresentationPC
import ProgramProofs.Uxnmin.RepresentationStack

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JSI saves the return address and then applies the immediate displacement. -/
theorem immediate_subroutine_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = 0x60)
    (firstBound : (guest.pc + 1).toNat < ramSize) (secondBound : (guest.pc + 2).toNat < ramSize) :
    ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary (immediateNext .jsi guest) final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, entry, working, top, returnShape, returnFrame,
    _, _, _, _, headerMemory⟩ := immediate_header .jsi boundary confined opcode
  change dispatched.pc = 0x396 at entry
  obtain ⟨first, firstStep, suffix⟩ := header_progress boundary.toRepresents rep headerRun
  have returnSpace : outer.mem.rstk.ptr.toNat ≤ 253 := by have := boundary.returnSpace; omega
  have dispatchedRP : dispatched.mem.rstk.ptr = outer.mem.rstk.ptr + 2#8 := by
    have ptr := congrArg Uxn.Stack.ptr returnShape
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using ptr.symm
  obtain ⟨saved, saveRun, savePC, saveWP, saveRP, saveRAM, saveCode, saveWF, saveRF⟩ :=
    immediate_save_return dispatched.mem.ram (guest.pc + 1) guest.mem.rstk.ptr dispatched.mem.wstk dispatched.mem.rstk
      rep.code rep.pcHigh rep.pcLow (by simpa [stackBase, guestStack] using rep.stackPointer true)
      (by simp [working]) (by rw [dispatchedRP]; have := boundary.returnSpace; bv_omega)
  have savedRep : Represents {guest with pc := guest.pc + 1, mem.rstk := Stack.pushWord guest.mem.rstk (guest.pc + 3)} saved := by
    have target := ((rep.setSource 0x657).storeOperand true true (guest.pc + 3)).transport (replacement := saved)
      (by simpa [guestStack, stackBase, BitVec.add_assoc] using saveRAM)
    simpa [pushStack, guestStack] using target
  have savedReturn : Stack.pushWord {saved.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170 = saved.mem.rstk :=
    Stack.asPushWord_of_frame dispatched.mem.rstk saved.mem.rstk outer.mem.rstk.ptr 0x170
      returnShape returnSpace saveRP saveRF
  obtain ⟨pushed, handlerRun, handlerPC, handlerWP, handlerRP, handlerRAM, handlerCode, handlerWF, handlerRF⟩ :=
    handler_jmi saved.mem.ram (guest.pc + 1) 0x170 saved.mem.wstk
      {saved.mem.rstk with ptr := outer.mem.rstk.ptr} saveCode savedRep.pcHigh savedRep.pcLow
      (by rw [saveWP, working]; decide) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches first pushed := by
    apply suffix.trans
    have saves : Reaches dispatched saved := by
      simpa only [← entry, machine] using saveRun
    apply saves.trans
    simpa only [savedReturn, ← savePC, machine] using handlerRun
  have pushedTop : pushed.mem.wstk.data 0#8 = 0x60#8 := by
    rw [handlerWF _ (by rw [saveWP, working]; decide), saveWF _ (by simp [working])]
    exact top
  let final : Uxn.State := {pushed with pc := 0x16d, mem.wstk.ptr := 0}
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed handlerCode handlerPC (handlerWP.trans (saveWP.trans working)) (by rw [pushedTop]; decide)
  have operand : saved.mem.ram (relocate (guest.pc + 1)) ++
      saved.mem.ram (relocate (guest.pc + 1 + 1)) = immediateWord guest := by
    rw [savedRep.ram _ firstBound, savedRep.ram _ (by simpa [BitVec.add_assoc] using secondBound)]
    simp [immediateWord, BitVec.add_assoc]
  have represented : Represents (immediateNext .jsi guest) final := by
    apply (savedRep.setPC (guest.pc + 3 + immediateWord guest)).transport
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
    rw [saveRAM]
    change storeStackOperand _ (stackBase true) _ _ true address = _
    rw [storeStackOperand_frame _ true true _ _ outside]
    have notSourceHigh : address ≠ 0x40 := by intro h; apply noPop; simp [PopScratch, h]
    have notSourceLow : address ≠ 0x41 := by intro h; apply noPop; simp [PopScratch, h]
    rw [Function.update_of_ne notSourceLow, Function.update_of_ne notSourceHigh]
    exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerRF _ below, saveRF _ (by rw [dispatchedRP]; have := boundary.returnSpace; bv_omega)]
    exact returnFrame index below

end ProgramProofs.Uxnmin
