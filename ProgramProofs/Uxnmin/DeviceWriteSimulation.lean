import ProgramProofs.Uxnmin.DeviceWriteHandler
import ProgramProofs.Uxnmin.DeviceRepresentation
import ProgramProofs.Uxnmin.GuestDeviceWrite
import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.RepresentationPop

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- Every supported DEO mode returns to a represented guest boundary with the same IO action. -/
theorem device_write_simulation {guest outer : Uxn.State} (guestHost outerHost : Uxn.Host.State)
    (boundary : EvaluationBoundary guest outer) (devices : DeviceImage guestHost outer)
    (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x17) :
    let ret := (guest.mem.ram guest.pc).getLsbD 6
    let short := (guest.mem.ram guest.pc).getLsbD 5
    let kept := (guest.mem.ram guest.pc).getLsbD 7
    let stack := guestStack guest ret
    let port := stack.data (stack.ptr - 1)
    let low := stack.data (stack.ptr - 2)
    let outputPort := port + (if short then 1 else 0)
    port ≠ Port.Console.read → port ≠ Port.Console.type →
    outputPort ≠ Port.Console.read → outputPort ≠ Port.Console.type → outputPort ∉ Port.File.ports →
    ∃ stage resume final finalHost,
      Uxn.Host.step guest guestHost = (do
        deviceOutput outputPort low
        pure (.next (deviceWriteNext guest ret short kept), deviceWriteHost guest guestHost ret short)) ∧
      Reaches outer stage ∧
      Uxn.Host.step stage outerHost = (do deviceOutput outputPort low; pure (.next resume, finalHost)) ∧
      Reaches resume final ∧ EvaluationBoundary (deviceWriteNext guest ret short kept) final ∧
      DeviceImage (deviceWriteHost guest guestHost ret short) final ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) := by
  intro ret short kept stack port low outputPort input kind outputInput outputKind supported
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    mode, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ := instruction_header boundary confined
  have tableHigh : outer.mem.ram 0x543#16 = 0x04#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x544#16 = 0xb7#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x4b7 := by
    rw [opcode] at pc
    simpa [tableHigh, tableLow] using pc
  obtain ⟨handled, handlerRun, handlerPC, handlerRAM, handlerWP, handlerValue, handlerPort,
    handlerRP, handlerReturn, handlerWF, handlerRF⟩ :=
    handler_device_write dispatched.mem.ram (stackBase ret) stack.ptr (if kept then 1 else 0) short
      dispatched.mem.wstk {dispatched.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170
      (by cases ret <;> simp [stackBase]) rep.code sourceHigh sourceLow mode keep
      (by cases kept <;> decide) cursor (by simp [working])
      (by change outer.mem.rstk.ptr.toNat ≤ 247; have := boundary.returnSpace; omega)
  have beforeHandler : Reaches outer handled := by
    apply headerRun.trans
    simpa only [returnShape, ← dispatchPC, machine] using handlerRun
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  have stackValue (index : Byte) : dispatched.mem.ram (stackBase ret + index.setWidth 16) = stack.data index := by
    simpa only [guestStack_pc] using rep.stackData ret index
  have portValue : dispatched.mem.ram (stackBase ret + (stack.ptr - 1#8).setWidth 16) = port := stackValue _
  have valueLow : (stackOperand dispatched.mem.ram (stackBase ret) (stack.ptr - 1#8) short).setWidth 8 = low := by
    simp [stackOperand, byteLow, BitVec.sub_eq_add_neg, BitVec.add_assoc, stackValue, low]
  have valueHigh : (stackOperand dispatched.mem.ram (stackBase ret) (stack.ptr - 1#8) short >>> 8).setWidth 8 =
      if short then stack.data (stack.ptr - 3#8) else 0 := by
    simp [stackOperand, byteHigh, BitVec.sub_eq_add_neg, BitVec.add_assoc, stackValue]
  rw [valueLow] at handlerValue
  rw [portValue] at handlerPort
  rw [portValue, valueHigh] at handlerRAM
  have cursorLower : 0x555 ≤ (stackBase ret + (0x100#16 + (if kept then 1#8 else 0).setWidth 16)).toNat := by
    cases ret <;> cases kept <;> decide
  have cursorUpper : (stackBase ret + (0x100#16 + (if kept then 1#8 else 0).setWidth 16)).toNat < 0x759 := by
    cases ret <;> cases kept <;> decide
  have handlerCode : CodeImage handled.mem.ram := by
    rw [handlerRAM]
    split
    · exact (rep.code.write _ _ (.inr (.inl cursorLower))).write _ _ (.inr (.inl (by bv_omega)))
    · exact rep.code.write _ _ (.inr (.inl cursorLower))
  simp only [BitVec.ofNat_eq_ofNat] at handlerWP handlerValue handlerPort
  have pair : Stack.push (Stack.push {handled.mem.wstk with ptr := dispatched.mem.wstk.ptr} low) outputPort = handled.mem.wstk := by
    simpa [handlerWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, handlerValue, handlerPort,
      outputPort, Stack.pushWord, byteHigh, byteLow] using Stack.asPushWord handled.mem.wstk
  obtain ⟨stage, resume, pushed, finalHost, helperBefore, action, helperAfter, helperPC, helperRAM,
    helperWP, helperRP, helperWF, helperRF⟩ :=
    device_write_helper handled.mem.ram handlerCode outputPort low
      {handled.mem.wstk with ptr := dispatched.mem.wstk.ptr}
      {handled.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170 outerHost
      (by simp [working]) (by have := boundary.returnSpace; dsimp; omega)
  have before : Reaches outer stage := by
    apply beforeHandler.trans
    have shape : handled = machine handled.mem.ram handled.pc handled.mem.wstk handled.mem.rstk := rfl
    rw [handlerPC] at shape
    rw [shape]
    simpa only [pair, handlerReturn] using helperBefore
  have represented : Represents (deviceWriteNext guest ret short kept) pushed := by
    have popped := rep.popStack ret kept (1 + (if short then 2 else 1))
    have prepare : Represents (deviceWriteNext guest ret short kept) handled := by
      cases modeEq : short
      · have target := popped.transport (replacement := handled) (by
          rw [handlerRAM]
          simp only [modeEq, Bool.false_eq_true, if_false]
          dsimp only [stack]
          cases kept <;> cases ret <;> simp [guestStack, BitVec.sub_eq_add_neg, BitVec.add_assoc])
        simpa [deviceWriteNext, modeEq] using target
      · have written := popped.writeDevice (0x759 + port.setWidth 16) (stack.data (stack.ptr - 3))
          (.inr (.inr (by constructor <;> bv_omega)))
        have target := written.transport (replacement := handled) (by
          rw [handlerRAM]
          simp only [modeEq, if_true]
          dsimp only [stack]
          cases kept <;> cases ret <;> simp [guestStack, BitVec.sub_eq_add_neg, BitVec.add_assoc])
        simpa [deviceWriteNext, modeEq] using target
    exact (prepare.deviceRam outputPort low).transport helperRAM
  have dispatchedDevices : DeviceImage guestHost dispatched := by
    constructor
    · intro address
      rw [headerMemory _ (by
        simp only [PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
        repeat' constructor <;> bv_omega)]
      exact devices.ports address
    · rw [headerMemory _ (by simp [PopScratch])]; exact devices.consoleRead
    · rw [headerMemory _ (by simp [PopScratch])]; exact devices.consoleType
  have finalDevices : DeviceImage (deviceWriteHost guest guestHost ret short) pushed := by
    have popped := dispatchedDevices.writeStack _ (stack.ptr - 1 - (if short then 2 else 1)) cursorLower cursorUpper
    cases modeEq : short
    · have prepared := popped.transport (replacement := handled) (by simpa only [modeEq, Bool.false_eq_true, if_false, BitVec.ofNat_eq_ofNat] using handlerRAM)
      have written := (prepared.deviceRam outputPort low outputInput outputKind).transport helperRAM
      simpa [deviceWriteHost, modeEq, outputPort, stack, port, low] using written
    · have prepared := (popped.write port (stack.data (stack.ptr - 3)) input kind).transport (replacement := handled)
          (by simpa only [modeEq, if_true, BitVec.ofNat_eq_ofNat] using handlerRAM)
      have written := (prepared.deviceRam outputPort low outputInput outputKind).transport helperRAM
      simpa [deviceWriteHost, modeEq, outputPort, stack, port, low] using written
  have pushedTop : pushed.mem.wstk.data 0#8 = guest.mem.ram guest.pc := by
    rw [helperWF _ (by simp [working]), handlerWF _ (by simp [working])]
    exact top
  let final : Uxn.State := {pushed with pc := 0x16d, mem.wstk.ptr := 0}
  have loop : Uxn.step pushed = .done (.next final) :=
    return_to_loop pushed represented.code helperPC (helperWP.trans working) (by
      rw [pushedTop]
      intro zero
      simp [zero] at opcode)
  refine ⟨stage, resume, final, finalHost, guest_device_write guest guestHost opcode supported,
    before, action, helperAfter.trans (.next loop (.refl _)), ⟨represented.transport rfl, rfl, rfl, ?_⟩,
    finalDevices.transport rfl, helperRP, ?_⟩
  · change pushed.mem.rstk.ptr.toNat ≤ 245
    rw [helperRP]
    exact boundary.returnSpace
  · intro index below
    change pushed.mem.rstk.data index = outer.mem.rstk.data index
    rw [helperRF _ below, handlerRF _ below]
    exact returnFrame index below

end ProgramProofs.Uxnmin
