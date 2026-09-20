import ProgramProofs.Uxnmin.DeliveryImage
import ProgramProofs.Uxnmin.PureBlocks

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem stack_zero (stack : Uxn.Stack) (pointer : stack.ptr = 0) :
    ({data := stack.data, ptr := 0} : Uxn.Stack) = stack := by
  cases stack
  simp_all

theorem delivery_block {filename : String} {initialWorld : Void IO.RealWorld}
    {guest outer : Uxn.Host.State} (world : Void IO.RealWorld) (value kind : Byte) (last : Bool)
    (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
    (image : ConsoleImage guest outer)
    (guestControl : guest.control = .delivering value kind (remaining last))
    (outerControl : outer.control = .delivering value kind (remaining last)) :
    Block (Boundary filename initialWorld) (.running guest world) (.running outer world) := by
  have outerStep := next_delivery_vector value kind (remaining last) outerControl
    (show outer.consoleVector ≠ 0 by rw [image.outerVector]; decide)
  have outerShape : machine outer.vm.mem.ram 0x174
      ⟨outer.vm.mem.wstk.data, 0⟩ ⟨outer.vm.mem.rstk.data, 0⟩ = {outer.vm with pc := outer.consoleVector} := by
    rw [stack_zero _ image.working, stack_zero _ image.returning, image.outerVector]
    rfl
  have live : label (.running guest world) = .ok none world := by
    simp only [label, Uxn.Host.State.next, guestControl, Option.isNone_some, Bool.false_eq_true, if_false]
  by_cases zero : guest.consoleVector = 0
  · have direct := configuration_pure world (next_delivery_zero value kind (remaining last) guestControl zero)
    obtain ⟨penultimate, steps, shape, working, returning⟩ := callback_skip outer.vm.mem.ram image.core.code
      outer.vm.mem.wstk.data outer.vm.mem.rstk.data (deliver outer value kind) (remaining last)
      (image.vector.trans zero)
    have control : penultimate.control = .evaluating (.console (remaining last)) := by rw [shape]
    have memory : penultimate.vm.mem.ram = outer.vm.mem.ram := by rw [shape]; rfl
    have pc : penultimate.vm.pc = 0x17c := by rw [shape]; rfl
    have opcode : penultimate.vm.mem.ram penultimate.vm.pc = 0 := by
      rw [memory, pc]
      exact image.core.code _ (by decide) (by decide) (by simp [MutableCode])
    have ports : penultimate.ports = (deliver outer value kind).ports := by simpa only using congrArg Uxn.Host.State.ports shape
    have vector : penultimate.consoleVector = outer.consoleVector := by simpa only [deliver, Uxn.Host.State.write] using congrArg Uxn.Host.State.consoleVector shape
    have system : penultimate.read Port.System.state = (deliver guest value kind).read Port.System.state := by
      change penultimate.ports.get _ = _
      rw [ports]
      exact (image.deliver value kind).system
    have brk := next_brk (.console (remaining last)) control opcode
    let final := {penultimate with vm.pc := penultimate.vm.pc + 1, control := .console (remaining last)}
    have run : PureReaches outer final := by
      apply PureReaches.head outerStep
      change PureReaches {deliver outer value kind with
        vm.pc := outer.consoleVector, control := .evaluating (.console (remaining last))} final
      rw [outerShape] at steps
      exact steps.trans (.head brk (.refl _))
    apply pure_last_block world live direct run
    · intro same
      have impossible := congrArg Uxn.Host.State.control same
      simp only [outerControl, final] at impossible
      cases impossible
    · cases last
      · apply Boundary.input (reachable.tail direct) _ rfl rfl
        refine ⟨image.core.transport memory, ?_, ?_, ?_, working, returning, ?_⟩
        · intro port input type
          change penultimate.vm.mem.ram (0x759 + port.setWidth 16) = (deliver guest value kind).read port
          rw [memory]
          exact (image.deliver value kind).ports port input type
        · change penultimate.vm.mem.ram 0x175 ++ penultimate.vm.mem.ram 0x176 = guest.consoleVector
          rw [memory]
          exact image.vector
        · exact system
        · exact vector.trans image.outerVector
      · apply Boundary.stopped
        · rfl
        · rfl
        · have exit : (deliver guest value kind).exitCode = penultimate.exitCode :=
            congrArg (fun byte : Byte => (byte &&& 0x7f).toNat.toUInt32) system.symm
          change EST.Out.ok (some ((deliver guest value kind).exitCode)) world =
            EST.Out.ok (some penultimate.exitCode) world
          rw [exit]

  · have direct := configuration_pure world (next_delivery_vector value kind (remaining last) guestControl zero)
    obtain ⟨final, steps, control, ports, vector, pc, working, returning, frame, memory⟩ :=
      callback_enter outer.vm.mem.ram image.core.code outer.vm.mem.wstk.data outer.vm.mem.rstk.data
        (deliver outer value kind) (remaining last) (by rw [image.vector]; exact zero)
    have run : PureReaches outer final := by
      apply PureReaches.head outerStep
      change PureReaches {deliver outer value kind with
        vm.pc := outer.consoleVector, control := .evaluating (.console (remaining last))} final
      rw [outerShape] at steps
      exact steps
    apply pure_last_block world live direct run
    · intro same
      have impossible := congrArg Uxn.Host.State.control same
      rw [outerControl, control] at impossible
      cases impossible
    · apply Boundary.evaluating (.callback last) (reachable.tail direct)
      exact callback_image (image.deliver value kind) last
        (by simp [deliver, host_write_read]) (by simp [deliver, host_write_read])
        control ports vector pc working returning frame memory

end ProgramProofs.Uxnmin.Model
