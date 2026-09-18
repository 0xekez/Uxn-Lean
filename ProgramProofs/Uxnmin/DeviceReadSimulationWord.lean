import ProgramProofs.Uxnmin.DeviceReadHandlerWord
import ProgramProofs.Uxnmin.GuestDeviceRead
import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.Boundary
import ProgramProofs.Uxnmin.RepresentationStack

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- DEI2, DEI2k, DEI2r, and DEI2kr return to the next represented guest boundary. -/
theorem device_read_word_simulation {guest outer : Uxn.State} (host : Uxn.Host.State)
    (boundary : EvaluationBoundary guest outer) (devices : DeviceImage host outer)
    (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x16)
    (wordMode : (guest.mem.ram guest.pc).getLsbD 5 = true) :
    ∃ guest' final, Uxn.Host.step guest host = pure (.next guest', host) ∧ Reaches outer final ∧
      EvaluationBoundary guest' final ∧ outer ≠ final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ := instruction_header boundary confined
  have tableHigh : outer.mem.ram 0x541#16 = 0x04#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x542#16 = 0xb1#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x4b1 := by
    rw [opcode] at pc
    simpa [tableHigh, tableLow] using pc
  obtain ⟨pushed, handlerRun, handlerPC, handlerWorking, handlerReturning, handlerMemory, handlerFrame, handlerReturnFrame⟩ :=
    handler_device_read_word dispatched.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6))
      (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr
      (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0) dispatched.mem.wstk
      {dispatched.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170
      (by cases (guest.mem.ram guest.pc).getLsbD 6 <;> simp [stackBase]) rep.code sourceHigh sourceLow
      (by simpa only [wordMode, if_true, BitVec.ofNat_eq_ofNat] using short) keep
      (by cases (guest.mem.ram guest.pc).getLsbD 7 <;> decide) cursor
      (by simpa using rep.stackPointer ((guest.mem.ram guest.pc).getLsbD 6))
      (by simp [working]) (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have run : Reaches outer pushed := by
    apply headerRun.trans
    simpa only [returnShape, ← dispatchPC, machine] using handlerRun
  have handlerCode : CodeImage pushed.mem.ram := by
    rw [handlerMemory]
    have abovePointer : 0x555 ≤ (stackBase ((guest.mem.ram guest.pc).getLsbD 6) + 0x100#16).toNat := by
      cases (guest.mem.ram guest.pc).getLsbD 6 <;> decide
    have aboveData (index : Byte) : 0x555 ≤ (stackBase ((guest.mem.ram guest.pc).getLsbD 6) + index.setWidth 16).toNat := by
      cases (guest.mem.ram guest.pc).getLsbD 6 <;> dsimp [stackBase] <;> bv_omega
    have aboveCursor : 0x555 ≤ (stackBase ((guest.mem.ram guest.pc).getLsbD 6) +
        (0x100#16 + (if (guest.mem.ram guest.pc).getLsbD 7 then 1#8 else 0#8).setWidth 16)).toNat := by
      cases (guest.mem.ram guest.pc).getLsbD 6 <;> cases (guest.mem.ram guest.pc).getLsbD 7 <;> decide
    exact ((((rep.code.write _ _ (.inr (.inl aboveCursor))).write _ _ (.inr (.inl abovePointer))).write _ _
      (.inr (.inl (aboveData _)))).write _ _ (.inr (.inl abovePointer))).write _ _ (.inr (.inl (aboveData _)))
  have pushedTop : pushed.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [handlerFrame _ (by simp [working])]
    exact top
  let final : Uxn.State := {pushed with pc := 0x16d, mem.wstk.ptr := 0}
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed handlerCode handlerPC (handlerWorking.trans working) (by
      rw [pushedTop]
      intro zero
      simp [zero] at opcode)
  have readValue (port : Byte) :
      (if port = 0x12 then dispatched.mem.ram 0x199 else if port = 0x17 then dispatched.mem.ram 0x1a4
       else dispatched.mem.ram (0x759 + port.setWidth 16)) = host.read port := by
    have input : dispatched.mem.ram 0x199 = host.read Uxn.Host.Port.Console.read := by
      rw [headerMemory _ (by simp [PopScratch])]
      exact devices.consoleRead
    have kind : dispatched.mem.ram 0x1a4 = host.read Uxn.Host.Port.Console.type := by
      rw [headerMemory _ (by simp [PopScratch])]
      exact devices.consoleType
    have shadow : dispatched.mem.ram (0x759 + port.setWidth 16) = host.read port := by
      rw [headerMemory _ (by
        simp only [PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
        repeat' constructor <;> bv_omega)]
      exact devices.ports port
    split <;> rename_i special
    · subst port; exact input
    · split <;> rename_i special'
      · subst port; exact kind
      · exact shadow
  have shadowValue (port : Byte) : dispatched.mem.ram (0x759 + port.setWidth 16) = host.read port := by
    rw [headerMemory _ (by
      simp only [PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
      repeat' constructor <;> bv_omega)]
    exact devices.ports port
  have portValue := rep.stackData ((guest.mem.ram guest.pc).getLsbD 6)
    ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr - 1#8)
  simp only [guestStack_pc] at portValue
  let guest' := deviceReadNext guest host ((guest.mem.ram guest.pc).getLsbD 6) true
    ((guest.mem.ram guest.pc).getLsbD 7)
  have represented : Represents guest' final := by
    have result := (((rep.popStack ((guest.mem.ram guest.pc).getLsbD 6)
      ((guest.mem.ram guest.pc).getLsbD 7) 1).pushStack ((guest.mem.ram guest.pc).getLsbD 6) false
      ((host.read ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).data
        ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr - 1))).setWidth 16)).pushStack
      ((guest.mem.ram guest.pc).getLsbD 6) false
      ((host.read (((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).data
        ((guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr - 1)) + 1)).setWidth 16))
    have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
      rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
    have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
    have transported := result.transport (replacement := final) (by
      change pushed.mem.ram = _
      rw [handlerMemory, portValue, readValue, shadowValue]
      cases hr : (guest.mem.ram guest.pc).getLsbD 6 <;> cases hk : (guest.mem.ram guest.pc).getLsbD 7 <;>
        simp [popStack, guestStack, pushStack, Stack.push, BitVec.add_assoc])
    change Represents (deviceReadNext guest host _ true _) final
    cases hr : (guest.mem.ram guest.pc).getLsbD 6 <;> cases hk : (guest.mem.ram guest.pc).getLsbD 7
    all_goals
      simp only [hr, hk] at transported
      simp only [deviceReadNext, hr, hk]
      simpa [popStack, guestStack, pushStack, Host.State.readWord, Stack.pushWord, Stack.push,
        byteHigh, byteLow] using transported
  have nextPC : guest'.pc = guest.pc + 1 := by
    dsimp [guest', deviceReadNext]
    cases (guest.mem.ram guest.pc).getLsbD 6 <;> cases (guest.mem.ram guest.pc).getLsbD 7 <;> rfl
  refine ⟨guest', final, ?_, run.trans (.next loop (.refl _)),
    ⟨represented, rfl, rfl, ?_⟩, boundary.toRepresents.ne_of_pc_next represented nextPC,
    ?_, handlerReturning, ?_⟩
  · simpa only [wordMode] using guest_device_read guest host opcode
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [handlerReturning]
    exact boundary.returnSpace
  · intro address outside
    have noPop : ¬ PopScratch address := fun h => outside (.inl h)
    have outsideStack : address.toNat < 0x555 ∨ 0x759 ≤ address.toNat := by
      have excluded : ¬ (0x555 ≤ address.toNat ∧ address.toNat < 0x759) := fun h => outside (.inr h)
      omega
    change pushed.mem.ram address = outer.mem.ram address
    rw [handlerMemory]
    cases hr : (guest.mem.ram guest.pc).getLsbD 6 <;> cases hk : (guest.mem.ram guest.pc).getLsbD 7 <;>
      simp only [stackBase, Bool.false_eq_true, if_false, if_true]
    all_goals simp (disch := bv_omega) only [Function.update_of_ne]
    all_goals exact headerMemory address noPop
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [handlerReturnFrame _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
