import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.StoreHandler
import ProgramProofs.Uxnmin.GuestStore
import ProgramProofs.Uxnmin.StackFrame
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.RepresentationMemory

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Each confined memory store returns to the interpreter boundary with its exact guest result. -/
theorem store_simulation (kind : AddressMode) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = kind.storeOpcode)
    (firstBound : (kind.address { guest with pc := guest.pc + 1 }
      ((guest.mem.ram guest.pc).getLsbD 6)).toNat < ramSize)
    (secondBound : (guest.mem.ram guest.pc).getLsbD 5 = true →
      (kind.following (kind.address { guest with pc := guest.pc + 1 }
        ((guest.mem.ram guest.pc).getLsbD 6))).toNat < ramSize) :
    ∃ guest' final, Uxn.step guest = .done (.next guest') ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, address.toNat < ramBase → ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
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
  have dispatchPC : dispatched.pc = kind.storeEntry := by
    rw [opcode] at pc
    apply pc.trans
    cases kind <;>
      rw [boundary.code _ (by decide) (by decide) (by simp [MutableCode, AddressMode.storeOpcode]),
        boundary.code _ (by decide) (by decide) (by simp [MutableCode, AddressMode.storeOpcode])] <;> rfl
  have nativeAddress : kind.nativeAddress (guest.pc + 1)
      (stackOperand dispatched.mem.ram (stackBase ret) (guestStack guest ret).ptr
        (kind.operandKind.short short)) = address := by
    rw [rep.operand]
    cases kind <;> simp [AddressMode.nativeAddress, AddressMode.operandKind, OperandKind.short,
      address, AddressMode.address, advanced, guestStack_pc, operand, ← join_bytes]

  obtain ⟨computed, storeRun, storePC, storeWorking, storeReturning,
    storeMemory, storeCode, storeFrame, storeReturnFrame⟩ :=
    handler_store kind dispatched.mem.ram (stackBase ret) (guest.pc + 1)
      (guestStack guest ret).ptr (if keep then 1 else 0) short dispatched.mem.wstk
      { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170
      (by cases ret <;> simp [stackBase]) rep.code sourceHigh sourceLow mode rep.pcHigh rep.pcLow kept
      (by cases keep <;> decide) cursor
      (by rw [nativeAddress]; exact firstBound)
      (by intro isShort; rw [nativeAddress, AddressMode.following_mask]; exact secondBound isShort)
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches outer computed := by
    apply headerRun.trans
    simpa only [returnShape, ← dispatchPC, machine] using storeRun
  have nonzero : guest.mem.ram guest.pc ≠ 0#8 := by
    intro zero
    cases kind <;> simp [zero, AddressMode.storeOpcode] at opcode
  have computedTop : computed.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [storeFrame _ (by simp [working])]
    exact top
  let final : Uxn.State := { computed with pc := 0x16d, mem.wstk.ptr := 0 }
  have loop : Uxn.step computed = .done (.next final) :=
    return_to_loop computed storeCode storePC (storeWorking.trans working)
      (computedTop ▸ nonzero)
  let value := operand (guestStack guest ret) ((guestStack guest ret).ptr - kind.consumed) short
  let guest' := storeResult kind advanced ret short keep
  have represented : Represents guest' final := by
    apply ((rep.popStack ret keep (kind.consumed + operandSize short)).storeBytes
      address (kind.following address) value short firstBound secondBound).transport
    change computed.mem.ram = _
    rw [storeMemory, nativeAddress, rep.operand]
    simp only [guestStack_pc, BitVec.ofNat_eq_ofNat]
    dsimp only [value]
    cases short <;> cases keep <;>
      simp [pokeMemory, storeBytes, AddressMode.following_mask, operandSize,
        BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
  refine ⟨guest', final, guest_store kind guest opcode,
    run.trans (.next loop (.refl _)), ⟨represented, rfl, rfl, ?_⟩, ?_, ?_, storeReturning, ?_⟩
  · change computed.mem.rstk.ptr.toNat ≤ 245
    rw [storeReturning]
    exact boundary.returnSpace
  · apply boundary.toRepresents.ne_of_pc_next represented
    have preserved (state : Uxn.State) (ret short keep : Bool) :
        (storeResult kind state ret short keep).pc = state.pc := by
      cases ret <;> cases short <;> cases keep <;> rfl
    exact preserved advanced ret short keep
  · intro location before outside
    change computed.mem.ram location = outer.mem.ram location
    have separate (index : Word) (bound : index.toNat < ramSize) : location ≠ relocate index := by
      dsimp [ramBase] at before
      dsimp [relocate, ramSize] at *
      bv_omega
    rw [storeMemory, nativeAddress]
    have exterior (memory : Word → Byte) (value : Word) :
        pokeMemory memory address kind.mask value short location = memory location := by
      cases mode : short with
      | false => simp [pokeMemory, Function.update_of_ne (separate address firstBound)]
      | true =>
        simp only [pokeMemory, if_true, BitVec.ofNat_eq_ofNat]
        rw [AddressMode.following_mask, Function.update_of_ne (separate _ (secondBound mode)),
          Function.update_of_ne (separate address firstBound)]
    rw [exterior]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [Function.update_of_ne (StackScratch.cursor_separate outside ret keep)]
    exact headerMemory location (fun scratch => outside (.inl scratch))
  · intro index below
    change computed.mem.rstk.data index = outer.mem.rstk.data index
    rw [storeReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
