import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.LoadHandler
import ProgramProofs.Uxnmin.GuestLoad
import ProgramProofs.Uxnmin.StackFrame
import ProgramProofs.Uxnmin.Return

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Each confined memory load returns to the interpreter boundary with its exact guest result. -/
theorem load_simulation (kind : AddressMode) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = kind.loadOpcode)
    (firstBound : (kind.address { guest with pc := guest.pc + 1 }
      ((guest.mem.ram guest.pc).getLsbD 6)).toNat < ramSize)
    (secondBound : (guest.mem.ram guest.pc).getLsbD 5 = true →
      (kind.following (kind.address { guest with pc := guest.pc + 1 }
        ((guest.mem.ram guest.pc).getLsbD 6))).toNat < ramSize) :
    ∃ guest' final, Uxn.step guest = .done (.next guest') ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  let ret := (guest.mem.ram guest.pc).getLsbD 6
  let short := (guest.mem.ram guest.pc).getLsbD 5
  let keep := (guest.mem.ram guest.pc).getLsbD 7
  let advanced := { guest with pc := guest.pc + 1 }
  let address := kind.address advanced ret
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    mode, kept, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  have dispatchPC : dispatched.pc = kind.loadEntry := by
    rw [opcode] at pc
    apply pc.trans
    cases kind <;>
      rw [boundary.code _ (by decide) (by decide) (by simp [MutableCode, AddressMode.loadOpcode]),
        boundary.code _ (by decide) (by decide) (by simp [MutableCode, AddressMode.loadOpcode])] <;> rfl
  obtain ⟨computed, loadRun, loadPC, loadWorking, loadReturning,
    loadMemory, loadCode, loadFrame, loadReturnFrame⟩ :=
    handler_load kind dispatched.mem.ram (stackBase ret) (guest.pc + 1)
      (guestStack guest ret).ptr (if keep then 1 else 0) short dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases ret <;> simp [stackBase]) rep.code sourceHigh sourceLow mode rep.pcHigh rep.pcLow kept
      (by cases keep <;> decide) cursor
      (by simpa only [guestStack_pc, BitVec.ofNat_eq_ofNat] using rep.stackPointer ret)
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches outer computed := by
    apply headerRun.trans
    simpa only [returnShape, ← dispatchPC, machine] using loadRun
  have nonzero : guest.mem.ram guest.pc ≠ 0#8 := by
    intro zero
    cases kind <;> simp [zero, AddressMode.loadOpcode] at opcode
  have computedTop : computed.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [loadFrame _ (by simp [working])]
    exact top
  let final : Uxn.State := { computed with pc := 0x16d, mem.wstk.ptr := 0 }
  have loop : Uxn.step computed = .done (.next final) :=
    return_to_loop computed loadCode loadPC (loadWorking.trans working)
      (computedTop ▸ nonzero)
  have nativeAddress : kind.nativeAddress (guest.pc + 1)
      (stackOperand dispatched.mem.ram (stackBase ret) (guestStack guest ret).ptr
        (kind.operandKind.short short)) = address := by
    rw [rep.operand]
    cases kind <;> simp [AddressMode.nativeAddress, AddressMode.operandKind, OperandKind.short,
      address, AddressMode.address, advanced, guestStack_pc, operand, ← join_bytes]

  let value : Word := if short then guest.mem.ram address ++ guest.mem.ram (kind.following address)
    else (guest.mem.ram address).setWidth 16
  have readValue : peekValue
      (Function.update dispatched.mem.ram
        (stackBase ret + (0x100#16 + (if keep then 1#8 else 0#8).setWidth 16))
        ((guestStack guest ret).ptr - kind.consumed)) address kind.mask short = value := by
    have exterior (location : Word) (bound : location.toNat < ramSize) :
        relocate location ≠ stackBase ret + (0x100#16 + (if keep then 1#8 else 0#8).setWidth 16) := by
      cases ret <;> cases keep <;> dsimp [relocate, stackBase, ramSize] at * <;> bv_omega
    have firstRead := rep.ram address firstBound
    have lastRead (mode : short = true) := rep.ram (kind.following address) (secondBound mode)
    cases mode : short with
    | false =>
      simp [peekValue, value, mode, Function.update_of_ne (exterior address firstBound), firstRead,
        ← join_bytes]
    | true =>
      simp only [peekValue, value, mode, if_true, BitVec.ofNat_eq_ofNat]
      rw [AddressMode.following_mask]
      rw [Function.update_of_ne (exterior address firstBound),
        Function.update_of_ne (exterior _ (secondBound mode)), firstRead, lastRead mode]
  let guest' := loadResult kind advanced ret short keep
  have represented : Represents guest' final := by
    apply ((rep.popStack ret keep kind.consumed).storeOperand ret short value).transport
    change computed.mem.ram = _
    rw [loadMemory, nativeAddress]
    dsimp only
    simp only [BitVec.ofNat_eq_ofNat]
    rw [readValue]
    cases keep <;> simp [guestStack_pc, popStack_pointer]
  refine ⟨guest', final, guest_load kind guest opcode,
    run.trans (.next loop (.refl _)), ⟨represented, rfl, rfl, ?_⟩, ?_, ?_, loadReturning, ?_⟩
  · change computed.mem.rstk.ptr.toNat ≤ 245
    rw [loadReturning]
    exact boundary.returnSpace
  · apply boundary.toRepresents.ne_of_pc_next represented
    have preserved (state : Uxn.State) (ret short keep : Bool) :
        (loadResult kind state ret short keep).pc = state.pc := by
      cases ret <;> cases short <;> cases keep <;> rfl
    exact preserved advanced ret short keep
  · intro location outside
    change computed.mem.ram location = outer.mem.ram location
    rw [loadMemory, storeStackOperand_frame _ ret short _ _ outside]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [Function.update_of_ne (StackScratch.cursor_separate outside ret keep)]
    exact headerMemory location (fun scratch => outside (.inl scratch))
  · intro index below
    change computed.mem.rstk.data index = outer.mem.rstk.data index
    rw [loadReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
