import ProgramProofs.Uxnmin.DeviceWriteRoute
import ProgramProofs.Uxnmin.DeviceWriteTail
import ProgramProofs.Uxnmin.DeviceOutputStep
import ProgramProofs.Uxnmin.StackView

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

def deviceRam (ram : Word → Byte) (port value : Byte) : Word → Byte :=
  let shadow := Function.update ram (0x759 + port.setWidth 16) value
  if port = 0x11 then Function.update (Function.update shadow 0x175 (shadow 0x769)) 0x176 value else shadow

/-- The native output helper has exactly one host action, surrounded by pure VM steps. -/
theorem device_write_helper (ram : Word → Byte) (code : CodeImage ram)
    (port value : Byte) (working returning : Uxn.Stack) (returnAddress : Word) (host : Uxn.Host.State)
    (workingSpace : working.ptr.toNat ≤ 248) (returnSpace : returning.ptr.toNat ≤ 253) :
    ∃ stage resume final finalHost,
      Reaches (machine ram 0x1af (Stack.push (Stack.push working value) port)
        (Stack.pushWord returning returnAddress)) stage ∧
      Uxn.Host.step stage host = (do deviceOutput port value; pure (.next resume, finalHost)) ∧
      Reaches resume final ∧
      final.pc = returnAddress ∧ final.mem.ram = deviceRam ram port value ∧
      final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  obtain ⟨shadow, shadowRun, shadowPC, shadowRAM, shadowWP, shadowValue, shadowPort, shadowRS, shadowWF⟩ :=
    device_write_shadow ram code port value working (Stack.pushWord returning returnAddress) workingSpace
  have shadowCode : CodeImage shadow.mem.ram := by
    rw [shadowRAM]
    exact code.write _ _ (.inr (.inl (by bv_omega)))
  have byteHigh (a b : Byte) : ((a ++ b) >>> 8).setWidth 8 = a := by
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left]
  have byteLow (a b : Byte) : (a ++ b).setWidth 8 = b := BitVec.setWidth_append_eq_right
  simp only [BitVec.ofNat_eq_ofNat] at shadowWP shadowValue shadowPort
  have shadowEta : Stack.push (Stack.push {shadow.mem.wstk with ptr := working.ptr} value) port = shadow.mem.wstk := by
    simpa [shadowWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, shadowValue, shadowPort, Stack.pushWord, byteHigh, byteLow]
      using Stack.asPushWord shadow.mem.wstk
  obtain ⟨routed, routeRun, routePC, routeRAM, routeWP, routeValue, routePort, routeRS, routeWF⟩ :=
    device_write_route shadow.mem.ram shadowCode port value {shadow.mem.wstk with ptr := working.ptr} shadow.mem.rstk (by dsimp; omega)
  have before : Reaches (machine ram 0x1af (Stack.push (Stack.push working value) port)
      (Stack.pushWord returning returnAddress)) routed := by
    apply shadowRun.trans
    have shape : shadow = machine shadow.mem.ram shadow.pc shadow.mem.wstk shadow.mem.rstk := rfl
    rw [shadowPC] at shape
    rw [shape]
    simpa only [shadowEta] using routeRun
  have routedCode : CodeImage routed.mem.ram := routeRAM ▸ shadowCode
  have routedReturning : routed.mem.rstk = Stack.pushWord returning returnAddress := routeRS.trans shadowRS
  simp only [BitVec.ofNat_eq_ofNat] at routeWP routeValue routePort
  have routedEta : Stack.push (Stack.push {routed.mem.wstk with ptr := working.ptr} value) port = routed.mem.wstk := by
    simpa [routeWP, BitVec.sub_eq_add_neg, BitVec.add_assoc, routeValue, routePort, Stack.pushWord, byteHigh, byteLow]
      using Stack.asPushWord routed.mem.wstk
  have routedFrame (index : Byte) (before : index.toNat < working.ptr.toNat) :
      routed.mem.wstk.data index = working.data index := by rw [routeWF _ before, shadowWF _ before]
  by_cases external : port = 0x0e ∨ port = 0x0f ∨ port = 0x18 ∨ port = 0x19
  · have notVector : port ≠ 0x11 := by rcases external with rfl | rfl | rfl | rfl <;> decide
    have opcode : routed.mem.ram routed.pc = 0x17 := by
      rcases external with rfl | rfl | rfl | rfl <;>
        simp only [ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.reduceEq] at routePC
      all_goals rw [routePC]; exact routedCode _ (by decide) (by decide) (by simp [MutableCode])
    have returnCode : routed.mem.ram (routed.pc + 1) = 0x6c := by
      rcases external with rfl | rfl | rfl | rfl <;>
        simp only [ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.reduceEq] at routePC
      all_goals rw [routePC]; exact routedCode _ (by decide) (by decide) (by simp [MutableCode])
    let resume : Uxn.State := {routed with pc := routed.pc + 1, mem.wstk.ptr := working.ptr}
    let final : Uxn.State := {resume with pc := returnAddress, mem.rstk.ptr := returning.ptr}
    have action : Uxn.Host.step routed host = (do deviceOutput port value; pure (.next resume, deviceHost host port value)) := by
      have native := device_output_step routed.mem.ram routed.pc opcode port value
        {routed.mem.wstk with ptr := working.ptr} routed.mem.rstk host (by
          rcases external with rfl | rfl | rfl | rfl <;> change ¬(0xa0#8 ≤ _ ∧ _ < 0xc0#8) <;> decide)
      simpa only [routedEta, machine] using native
    have returnStep : Uxn.step resume = .done (.next final) := by
      have native := device_output_return routed.mem.ram (routed.pc + 1) returnCode
        {routed.mem.wstk with ptr := working.ptr} returning returnAddress
      simpa only [← routedReturning, machine] using native
    refine ⟨routed, resume, final, deviceHost host port value, before, action, .next returnStep (.refl _), rfl, ?_, rfl, rfl, routedFrame, ?_⟩
    · change routed.mem.ram = _
      rw [routeRAM, shadowRAM]
      simp only [deviceRam, if_neg notVector]
    · intro index before
      change routed.mem.rstk.data index = returning.data index
      rw [routedReturning]
      simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]
  · have pureOutput : deviceOutput port value = pure () := by
      have stdout : port ≠ 0x18 := fun same => external (.inr (.inr (.inl same)))
      have stderr : port ≠ 0x19 := fun same => external (.inr (.inr (.inr same)))
      simp only [BitVec.ofNat_eq_ofNat] at stdout stderr
      simp [deviceOutput, Port.Console.write, Port.Console.error, stdout, stderr]
    have silent : ∃ final, Reaches routed final ∧
        final.pc = returnAddress ∧ final.mem.ram = deviceRam ram port value ∧
        final.mem.wstk.ptr = working.ptr ∧ final.mem.rstk.ptr = returning.ptr ∧
        (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
        (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
      by_cases vector : port = 0x11
      · rcases vector with rfl
        simp only [BitVec.ofNat_eq_ofNat] at routedEta
        obtain ⟨final, tail, finalPC, finalRAM, finalWP, finalRP, finalWF, finalRF⟩ :=
          device_write_vector routed.mem.ram routedCode value {routed.mem.wstk with ptr := working.ptr}
            returning returnAddress workingSpace returnSpace
        have steps : Reaches routed final := by
          have shape : routed = machine routed.mem.ram routed.pc routed.mem.wstk routed.mem.rstk := rfl
          rw [routePC] at shape
          simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceEq, if_false, if_true] at shape
          rw [shape, routedReturning]
          simpa only [routedEta, BitVec.ofNat_eq_ofNat] using tail
        refine ⟨final, steps, finalPC, ?_, finalWP, finalRP, ?_, finalRF⟩
        · rw [finalRAM, routeRAM, shadowRAM]
          rfl
        · intro index before
          rw [finalWF _ before, routedFrame _ before]
      · obtain ⟨final, tail, finalPC, finalRAM, finalWP, finalRP, finalWF, finalRF⟩ :=
          device_write_silent routed.mem.ram routedCode port value {routed.mem.wstk with ptr := working.ptr}
            returning returnAddress (by dsimp; omega) returnSpace
        have steps : Reaches routed final := by
          have p14 : port ≠ 0x0e := fun same => external (.inl same)
          have p15 : port ≠ 0x0f := fun same => external (.inr (.inl same))
          have p24 : port ≠ 0x18 := fun same => external (.inr (.inr (.inl same)))
          have p25 : port ≠ 0x19 := fun same => external (.inr (.inr (.inr same)))
          have shape : routed = machine routed.mem.ram routed.pc routed.mem.wstk routed.mem.rstk := rfl
          rw [routePC] at shape
          simp only [if_neg p14, if_neg p15, if_neg vector, if_neg p24, if_neg p25] at shape
          rw [shape, routedReturning]
          simpa only [routedEta, BitVec.ofNat_eq_ofNat] using tail
        refine ⟨final, steps, finalPC, ?_, finalWP, finalRP, ?_, finalRF⟩
        · rw [finalRAM, routeRAM, shadowRAM]
          simp only [deviceRam, if_neg vector]
        · intro index before
          rw [finalWF _ before, routedFrame _ before]
    obtain ⟨final, tail, finalPC, finalRAM, finalWP, finalRP, finalWF, finalRF⟩ := silent
    cases tail with
    | refl => have impossible : working.ptr + 2#8 = working.ptr := routeWP.symm.trans finalWP; bv_omega
    | @next _ resume _ step rest =>
      refine ⟨routed, resume, final, host, before, ?_, rest, finalPC, finalRAM, finalWP, finalRP, finalWF, finalRF⟩
      simp only [Uxn.Host.step, step, pureOutput]
      rfl

end ProgramProofs.Uxnmin
