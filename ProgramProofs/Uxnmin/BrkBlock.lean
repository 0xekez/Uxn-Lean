import ProgramProofs.Uxnmin.Callback
import ProgramProofs.Uxnmin.Cleanup
import ProgramProofs.Uxnmin.PureBlocks
import ProgramProofs.Uxnmin.ConsoleInput
import ProgramProofs.Uxnmin.BrkPrefix

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem next_halted_input {state : Uxn.Host.State}
    (control : state.control = .console .input) (halted : state.read Port.System.state ≠ 0) :
    state.next = some (pure {state with control := .delivering 10 4 .done}) := by
  simp only [BitVec.ofNat_eq_ofNat] at halted
  simp [Uxn.Host.State.next, control, halted]

theorem brk_block {filename : String} {initialWorld : Void IO.RealWorld}
    (confined : Confined (.starting (Uxn.Host.file filename) initialWorld))
    {invocation : Invocation} {guest outer : Uxn.Host.State} (world : Void IO.RealWorld)
    (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
    (image : Evaluation invocation guest outer) (opcode : guest.vm.mem.ram guest.vm.pc = 0) :
    Block (Boundary filename initialWorld) (.running guest world) (.running outer world) := by
  obtain ⟨first, stage, native, suffix, pc, working, rep, memory, returning, frame⟩ :=
    brk_prefix image.core (confined.pc_lt guest world invocation.directReturn reachable image.guestControl) opcode
  have before : PureReaches outer {outer with vm := stage} :=
    evaluating_reaches (.next native suffix) outer invocation.outerReturn image.outerControl
  have stageShape : machine stage.mem.ram 0x173 stage.mem.wstk stage.mem.rstk = stage := by
    rw [← pc]
    exact machine_self stage
  have deviceMemory (address : Word) (available : DeviceAddress address) :
      stage.mem.ram address = outer.vm.mem.ram address := by
    apply memory
    rcases available with special | bound
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at special
      rcases special with rfl | rfl | rfl | rfl <;> simp [PopScratch]
    · simp only [PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
      bv_omega
  have vector : stage.mem.ram 0x175 ++ stage.mem.ram 0x176 = guest.consoleVector := by
    rw [deviceMemory _ (.inl (by simp)), deviceMemory _ (.inl (by simp))]
    exact image.devices.vector
  have live := label_evaluating guest _ image.guestControl world
  have firstFrame : stage.mem.rstk.data 0 ++ stage.mem.rstk.data 1 = invocation.firstReturn := by
    rw [frame 0 (by rw [image.pointer]; cases invocation <;> simp [Invocation.pointer]),
      frame 1 (by rw [image.pointer]; cases invocation <;> simp [Invocation.pointer])]
    exact image.firstReturn
  cases invocation with
  | callback last =>
    obtain ⟨penultimate, cleanup, control, finalPC, finalRAM, wp, rp, outerVector, ports⟩ :=
      callback_cleanup stage.mem.ram stage.mem.wstk stage.mem.rstk outer (remaining last) rep.code
        working (returning.trans image.pointer) firstFrame
    rw [stageShape] at cleanup
    have cleanup : PureReaches {outer with vm := stage} penultimate := by
      simpa only [image.outerControl, Invocation.outerReturn] using cleanup
    have finalOpcode : penultimate.vm.mem.ram penultimate.vm.pc = 0 := by
      rw [finalRAM, finalPC]
      exact rep.code _ (by decide) (by decide) (by simp [MutableCode])
    have direct := configuration_pure world (next_brk (.console (remaining last)) image.guestControl opcode)
    let final := {penultimate with vm.pc := penultimate.vm.pc + 1, control := .console (remaining last)}
    have run : PureReaches outer final := before.trans (cleanup.trans
      (.head (next_brk (.console (remaining last)) control finalOpcode) (.refl _)))
    have system : penultimate.read Port.System.state = guest.read Port.System.state := by
      change penultimate.ports.get _ = _
      rw [ports]
      exact image.system
    apply pure_last_block world live direct run
    · intro same
      have impossible := congrArg Uxn.Host.State.control same
      rw [image.outerControl] at impossible
      cases impossible
    · cases last
      · apply Boundary.input (reachable.tail direct) _ rfl rfl
        refine ⟨rep.transport finalRAM, ?_, ?_, system, wp, rp, outerVector.trans image.outerVector⟩
        · intro port input type
          change penultimate.vm.mem.ram (0x759 + port.setWidth 16) = guest.read port
          rw [finalRAM, deviceMemory _ (.inr (by constructor <;> bv_omega))]
          exact image.devices.ports port input type
        · change penultimate.vm.mem.ram 0x175 ++ penultimate.vm.mem.ram 0x176 = guest.consoleVector
          rw [finalRAM]
          exact vector
      · refine Boundary.stopped rfl rfl ?_
        have exit : guest.exitCode = penultimate.exitCode :=
          congrArg (fun byte : Byte => (byte &&& 0x7f).toNat.toUInt32) system.symm
        change EST.Out.ok (some guest.exitCode) world = EST.Out.ok (some penultimate.exitCode) world
        rw [exit]
  | reset =>
    have resetFrame : stage.mem.rstk.data 2 ++ stage.mem.rstk.data 3 = 0x154#16 := by
      rw [frame 2 (by rw [image.pointer]; decide), frame 3 (by rw [image.pointer]; decide)]
      exact image.resetReturn rfl
    obtain ⟨penultimate, cleanup, control, finalPC, finalRAM, wp, rp, outerVector, system⟩ :=
      reset_cleanup stage.mem.ram stage.mem.wstk stage.mem.rstk outer rep.code working
        (returning.trans image.pointer) firstFrame resetFrame
    rw [stageShape] at cleanup
    have cleanup : PureReaches {outer with vm := stage} penultimate := by
      simpa only [image.outerControl, Invocation.outerReturn] using cleanup
    have finalOpcode : penultimate.vm.mem.ram penultimate.vm.pc = 0 := by
      rw [finalRAM, finalPC]
      exact rep.code _ (by decide) (by decide) (by simp [MutableCode])
    have nativeBrk := next_brk (.console .input) control finalOpcode
    by_cases zero : guest.consoleVector = 0
    · have test : stage.mem.ram 0x176 ||| stage.mem.ram 0x175 = 0 :=
        (pair_zero _ _).mpr (vector.trans zero)
      simp only [test, ↓reduceIte, image.outerVector, Invocation.outerVector] at outerVector system
      have direct := configuration_pure world (next_brk (.arguments []) image.guestControl opcode)
      simp only [zero, beq_self_eq_true, ↓reduceIte] at direct
      let idle := {penultimate with vm.pc := penultimate.vm.pc + 1, control := .console .input}
      let ending := {idle with control := .delivering 10 4 .done}
      let final := {(ending.write Port.Console.read 10).write Port.Console.type 4 with control := .console .done}
      have halted : idle.read Port.System.state ≠ 0 := by
        change penultimate.read Port.System.state ≠ 0
        rw [system]
        intro equal
        have impossible := (BitVec.or_eq_zero_iff).mp equal
        exact (by decide : (0x80#8) ≠ 0) impossible.2
      have run : PureReaches outer final := before.trans (cleanup.trans
        (.head nativeBrk (.head (next_halted_input rfl halted)
          (.head (next_delivery_zero 10 4 .done rfl outerVector) (.refl _)))))
      apply pure_last_block world live direct run
      · intro same
        have impossible := congrArg Uxn.Host.State.control same
        rw [image.outerControl] at impossible
        cases impossible
      · refine Boundary.stopped rfl rfl ?_
        have masked (byte : Byte) : ((byte ||| 0x80) &&& 0x7f) = byte &&& 0x7f := by
          rw [BitVec.and_or_distrib_right]
          simp
        have exit : final.exitCode = guest.exitCode := by
          change (((ending.write Port.Console.read 10).write Port.Console.type 4).read Port.System.state &&& 0x7f).toNat.toUInt32 = _
          simp only [host_write_read]
          change (penultimate.read Port.System.state &&& 0x7f).toNat.toUInt32 = _
          rw [system, masked, image.system]
          rfl
        change EST.Out.ok (some guest.exitCode) world = EST.Out.ok (some final.exitCode) world
        rw [exit]
    · have test : stage.mem.ram 0x176 ||| stage.mem.ram 0x175 ≠ 0 :=
        fun same => zero (vector.symm.trans ((pair_zero _ _).mp same))
      simp only [test, ↓reduceIte] at outerVector system
      have direct := configuration_pure world (next_brk (.arguments []) image.guestControl opcode)
      have selected : (guest.consoleVector == 0) = false := beq_eq_false_iff_ne.mpr zero
      simp only [selected, Bool.false_eq_true, ↓reduceIte, Console.arguments] at direct
      let final := {penultimate with vm.pc := penultimate.vm.pc + 1, control := .console .input}
      have run : PureReaches outer final := before.trans (cleanup.trans (.head nativeBrk (.refl _)))
      apply pure_last_block world live direct run
      · intro same
        have impossible := congrArg Uxn.Host.State.control same
        rw [image.outerControl] at impossible
        cases impossible
      · apply Boundary.input (reachable.tail direct) _ rfl rfl
        refine ⟨rep.transport finalRAM, ?_, ?_, system.trans image.system, wp, rp, outerVector⟩
        · intro port input type
          change penultimate.vm.mem.ram (0x759 + port.setWidth 16) = guest.read port
          rw [finalRAM, deviceMemory _ (.inr (by constructor <;> bv_omega))]
          exact image.devices.ports port input type
        · change penultimate.vm.mem.ram 0x175 ++ penultimate.vm.mem.ram 0x176 = guest.consoleVector
          rw [finalRAM]
          exact vector

end ProgramProofs.Uxnmin.Model
