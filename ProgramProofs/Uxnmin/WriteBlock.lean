import ProgramProofs.Uxnmin.Chunks
import ProgramProofs.Uxnmin.WriteCompatible
import ProgramProofs.Uxnmin.WriteImage

set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem configuration_next_action {state updated : Uxn.Host.State} {vm : Uxn.State}
    (after : ReturnTo) (world : Void IO.RealWorld) (output : IO Unit)
    (control : state.control = .evaluating after)
    (step : Uxn.Host.step state.vm state = (do output; pure (.next vm, updated))) :
    Configuration.next (.running state world) = some (match output world with
      | .ok _ later => .running {updated with vm} later
      | .error error later => .failed error later) := by
  simp only [Configuration.next, Uxn.Host.State.next, control, step, bind_assoc, pure_bind, Option.map_some]
  change some (Configuration.ofResult (EST.bind output (fun _ => EST.pure {updated with vm}) world)) = _
  rw [EST.bind.eq_def]
  cases output world <;> rfl

theorem nativeHost_vm (host : Uxn.Host.State) (port value : Byte) (vm : Uxn.State) :
    nativeHost {host with vm} port value = {nativeHost host port value with vm} := by
  unfold nativeHost
  split
  · unfold deviceHost
    split <;> rfl
  · rfl

/-- Match the exact output action, including a possible IO failure, between silent instruction fragments. -/
theorem write_block {filename : String} {initialWorld : Void IO.RealWorld}
    (confined : Confined (.starting (Uxn.Host.file filename) initialWorld))
    (compatible : CompatibleDevices (.starting (Uxn.Host.file filename) initialWorld))
    {invocation : Invocation} {guest outer : Uxn.Host.State} (world : Void IO.RealWorld)
    (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
    (image : Evaluation invocation guest outer)
    (opcode : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 0x17) :
    Block (Boundary filename initialWorld) (.running guest world) (.running outer world) := by
  obtain ⟨input, kind, outputInput, outputKind, supported, high⟩ :=
    device_write_compatible compatible guest world invocation.directReturn reachable image.guestControl opcode
  obtain ⟨stage, resume, final, direct, before, action, after, core, devices, pointer, frame⟩ :=
    device_write_simulation guest image.core image.devices
      (confined.pc_lt guest world invocation.directReturn reachable image.guestControl)
      opcode input kind outputInput outputKind supported
  let ret := (guest.vm.mem.ram guest.vm.pc).getLsbD 6
  let short := (guest.vm.mem.ram guest.vm.pc).getLsbD 5
  let kept := (guest.vm.mem.ram guest.vm.pc).getLsbD 7
  let stack := guestStack guest.vm ret
  let port := stack.data (stack.ptr - 1) + (if short then 1 else 0)
  let low := stack.data (stack.ptr - 2)
  let output := deviceOutput port low
  have directStep := configuration_next_action invocation.directReturn world output image.guestControl direct
  have nativeStep := configuration_next_action invocation.outerReturn world output
    (state := {outer with vm := stage}) (updated := {nativeHost outer port low with vm := stage})
    image.outerControl (by simpa only [nativeHost_vm] using action {outer with vm := stage})
  refine ⟨.running {outer with vm := stage} world, ?_, ?_, ?_⟩
  · exact (evaluating_reaches before outer _ image.outerControl).silent world _
      (label_evaluating guest _ image.guestControl world)
  · rw [label_evaluating guest _ image.guestControl,
        label_evaluating {outer with vm := stage} _ image.outerControl]
  · rw [directStep, nativeStep]
    cases effect : output world with
    | ok result later =>
      apply Option.Rel.some
      refine ⟨.running {nativeHost outer port low with vm := final} later, ?_,
        .evaluating invocation ?_ (write_evaluation image ret short kept high core devices pointer frame)⟩
      · exact (evaluating_reaches after (nativeHost outer port low) invocation.outerReturn
          ((nativeHost_control _ _ _).trans image.outerControl)).silent later _
          (label_evaluating _ invocation.directReturn (by
            simp only [deviceWriteHost, deviceHost_control]
            split <;> exact image.guestControl) later)
      · exact reachable.tail (by simpa only [effect] using directStep)
    | error error later =>
      exact .some ⟨.failed error later, .refl, .stopped rfl rfl rfl⟩

end ProgramProofs.Uxnmin.Model
