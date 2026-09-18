import ProgramProofs.Uxnmin.ImmediateHeader
import ProgramProofs.Uxnmin.ImmediateJump
import ProgramProofs.Uxnmin.ImmediateCondition
import ProgramProofs.Uxnmin.ImmediateSkip
import ProgramProofs.Uxnmin.RepresentationSelector
import ProgramProofs.Uxnmin.RepresentationPC
import ProgramProofs.Uxnmin.RepresentationStack
import ProgramProofs.Host.StackFrame
import ProgramProofs.Uxnmin.GuestImmediate

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- JCI pops its condition and reads its displacement only when the branch is taken. -/
theorem immediate_conditional_simulation {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = 0x20)
    (firstBound : guest.mem.wstk.data (guest.mem.wstk.ptr - 1) ≠ 0 → (guest.pc + 1).toNat < ramSize)
    (secondBound : guest.mem.wstk.data (guest.mem.wstk.ptr - 1) ≠ 0 → (guest.pc + 2).toNat < ramSize) :
    ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      EvaluationBoundary (immediateNext .jci guest) final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, entry, working, top, returnShape, returnFrame,
    _, kept, _, _, headerMemory⟩ := immediate_header .jci boundary confined opcode
  change dispatched.pc = 0x381 at entry
  obtain ⟨first, firstStep, suffix⟩ := header_progress boundary.toRepresents rep headerRun
  have returnSpace : outer.mem.rstk.ptr.toNat ≤ 253 := by have := boundary.returnSpace; omega
  have dispatchedRP : dispatched.mem.rstk.ptr = outer.mem.rstk.ptr + 2#8 := by
    have ptr := congrArg Uxn.Stack.ptr returnShape
    simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using ptr.symm
  obtain ⟨popped, popRun, popPC, popWP, popRP, popRAM, popCode, popWF, popRF⟩ :=
    immediate_condition dispatched.mem.ram guest.mem.wstk.ptr dispatched.mem.wstk dispatched.mem.rstk
      rep.code (by simpa [ImmediateKind.opcode] using kept)
      (by simpa [stackBase, guestStack] using rep.stackPointer false)
      (by simp [working]) (by rw [dispatchedRP]; have := boundary.returnSpace; bv_omega)
  have poppedRep : Represents {guest with pc := guest.pc + 1, mem.wstk.ptr := guest.mem.wstk.ptr - 1} popped := by
    have target := ((rep.setSource 0x555).popStack false false 1).transport (replacement := popped)
      (by simpa [guestStack, stackBase] using popRAM)
    simpa [popStack] using target
  have poppedReturn : Stack.pushWord {popped.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170 = popped.mem.rstk :=
    Stack.asPushWord_of_frame dispatched.mem.rstk popped.mem.rstk outer.mem.rstk.ptr 0x170
      returnShape returnSpace popRP popRF
  have condition : dispatched.mem.ram (0x555 + (guest.mem.wstk.ptr - 1#8).setWidth 16) =
      guest.mem.wstk.data (guest.mem.wstk.ptr - 1#8) := by
    simpa [stackBase, guestStack] using rep.stackData false (guest.mem.wstk.ptr - 1#8)
  rw [condition] at popPC
  let target : Word := if guest.mem.wstk.data (guest.mem.wstk.ptr - 1) = 0 then guest.pc + 3
    else guest.pc + 3 + immediateWord guest
  obtain ⟨pushed, handlerRun, handlerPC, handlerWP, handlerRP, handlerRAM, handlerCode, handlerWF, handlerRF⟩ :
      ∃ pushed, Reaches popped pushed ∧ pushed.pc = 0x170 ∧
        pushed.mem.wstk.ptr = popped.mem.wstk.ptr ∧ pushed.mem.rstk.ptr = outer.mem.rstk.ptr ∧
        pushed.mem.ram = Function.update (Function.update popped.mem.ram 0x45 ((target >>> 8).setWidth 8)) 0x46 (target.setWidth 8) ∧
        CodeImage pushed.mem.ram ∧
        (∀ index : Byte, index.toNat < popped.mem.wstk.ptr.toNat → pushed.mem.wstk.data index = popped.mem.wstk.data index) ∧
        (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → pushed.mem.rstk.data index = popped.mem.rstk.data index) := by
    by_cases zero : guest.mem.wstk.data (guest.mem.wstk.ptr - 1) = 0
    · obtain ⟨pushed, run, pc, wp, rp, ram, code, wf, rf⟩ :=
        immediate_skip popped.mem.ram (guest.pc + 1) 0x170 popped.mem.wstk
          {popped.mem.rstk with ptr := outer.mem.rstk.ptr} popCode poppedRep.pcHigh poppedRep.pcLow
          (by rw [popWP, working]; decide) (by change outer.mem.rstk.ptr.toNat ≤ 254; omega)
      refine ⟨pushed, ?_, pc, wp, rp, ?_, code, wf, rf⟩
      · have nativeZero : guest.mem.wstk.data (guest.mem.wstk.ptr - 1#8) = 0#8 := zero
        have selectedPC : popped.pc = 0x38e := by simpa only [if_pos nativeZero] using popPC
        simpa only [poppedReturn, ← selectedPC, machine] using run
      · simp only [target, if_pos zero]
        simpa [BitVec.add_assoc] using ram
    · obtain ⟨pushed, run, pc, wp, rp, ram, code, wf, rf⟩ :=
        handler_jmi popped.mem.ram (guest.pc + 1) 0x170 popped.mem.wstk
          {popped.mem.rstk with ptr := outer.mem.rstk.ptr} popCode poppedRep.pcHigh poppedRep.pcLow
          (by rw [popWP, working]; decide) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
      have operand : popped.mem.ram (relocate (guest.pc + 1)) ++
          popped.mem.ram (relocate (guest.pc + 1 + 1)) = immediateWord guest := by
        rw [poppedRep.ram _ (firstBound zero), poppedRep.ram _ (by simpa [BitVec.add_assoc] using secondBound zero)]
        simp [immediateWord, BitVec.add_assoc]
      refine ⟨pushed, ?_, pc, wp, rp, ?_, code, wf, rf⟩
      · have nativeNonzero : guest.mem.wstk.data (guest.mem.wstk.ptr - 1#8) ≠ 0#8 := zero
        have selectedPC : popped.pc = 0x3a4 := by simpa only [if_neg nativeNonzero] using popPC
        simpa only [poppedReturn, ← selectedPC, machine] using run
      · rw [ram, operand]
        simp only [target, if_neg zero]
        congr 2 <;> bv_omega
  have run : Reaches first pushed := by
    apply suffix.trans
    have pops : Reaches dispatched popped := by simpa only [← entry, machine] using popRun
    exact pops.trans handlerRun
  have pushedTop : pushed.mem.wstk.data 0#8 = 0x20#8 := by
    rw [handlerWF _ (by rw [popWP, working]; decide), popWF _ (by simp [working])]
    exact top
  let final : Uxn.State := {pushed with pc := 0x16d, mem.wstk.ptr := 0}
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed handlerCode handlerPC (handlerWP.trans (popWP.trans working)) (by rw [pushedTop]; decide)
  have represented : Represents (immediateNext .jci guest) final := by
    have result := (poppedRep.setPC target).transport (replacement := final) handlerRAM
    simpa [immediateNext, target] using result
  refine ⟨first, final, firstStep, run.trans (.next loop (.refl _)), ⟨represented, rfl, rfl, ?_⟩, ?_, handlerRP, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerRP]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    have notHigh : address ≠ 0x45 := by intro h; apply noPop; simp [PopScratch, h]
    have notLow : address ≠ 0x46 := by intro h; apply noPop; simp [PopScratch, h]
    have notSourceHigh : address ≠ 0x40 := by intro h; apply noPop; simp [PopScratch, h]
    have notSourceLow : address ≠ 0x41 := by intro h; apply noPop; simp [PopScratch, h]
    have notPointer : address ≠ 0x655 := by intro h; apply outside; right; simp [h]
    change pushed.mem.ram address = outer.mem.ram address
    rw [handlerRAM, Function.update_of_ne notLow, Function.update_of_ne notHigh, popRAM,
      Function.update_of_ne notPointer, Function.update_of_ne notSourceLow, Function.update_of_ne notSourceHigh]
    exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerRF _ below, popRF _ (by rw [dispatchedRP]; have := boundary.returnSpace; bv_omega)]
    exact returnFrame index below

end ProgramProofs.Uxnmin
