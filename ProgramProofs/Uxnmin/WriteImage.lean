import ProgramProofs.Uxnmin.Boundary
import ProgramProofs.Uxnmin.DeviceWriteSimulation

set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem deviceHost_control (host : Uxn.Host.State) (port value : Byte) :
    (deviceHost host port value).control = host.control := by
  unfold deviceHost
  split <;> rfl

theorem nativeHost_control (host : Uxn.Host.State) (port value : Byte) :
    (nativeHost host port value).control = host.control := by
  unfold nativeHost
  split
  · exact deviceHost_control _ _ _
  · rfl

theorem nativeHost_vector (host : Uxn.Host.State) (port value : Byte) :
    (nativeHost host port value).consoleVector = host.consoleVector := by
  unfold nativeHost
  split
  · rename_i forwarded
    have low : port ≠ Port.Console.vectorLow := by rcases forwarded with rfl | rfl | rfl | rfl <;> decide
    simp [deviceHost, low, Uxn.Host.State.write]
  · rfl

theorem nativeHost_system (host : Uxn.Host.State) (port value : Byte) :
    (nativeHost host port value).read Port.System.state =
      if Port.System.state = port then value else host.read Port.System.state := by
  unfold nativeHost
  split
  · exact deviceHost_read _ _ _ _
  · rename_i quiet
    have different : Port.System.state ≠ port := by intro same; apply quiet; exact .inr (.inl same.symm)
    simp [different]

theorem write_evaluation {invocation : Invocation} {guest outer : Uxn.Host.State}
    (image : Evaluation invocation guest outer) (ret short kept : Bool)
    (high : short = true → (guestStack guest.vm ret).data ((guestStack guest.vm ret).ptr - 1) ≠ Port.System.state)
    {final : Uxn.State}
    (core : EvaluationBoundary (deviceWriteNext guest.vm ret short kept) final)
    (devices : DeviceImage (deviceWriteHost guest.vm guest ret short) final)
    (pointer : final.mem.rstk.ptr = outer.vm.mem.rstk.ptr)
    (frame : ∀ index : Byte, index.toNat < outer.vm.mem.rstk.ptr.toNat →
      final.mem.rstk.data index = outer.vm.mem.rstk.data index) :
    Evaluation invocation
      {deviceWriteHost guest.vm guest ret short with vm := deviceWriteNext guest.vm ret short kept}
      {nativeHost outer ((guestStack guest.vm ret).data ((guestStack guest.vm ret).ptr - 1) +
        (if short then 1 else 0)) ((guestStack guest.vm ret).data ((guestStack guest.vm ret).ptr - 2)) with vm := final} := by
  refine ⟨core, ?_, ?_, ?_, ?_, ?_, pointer.trans image.pointer, ?_, ?_⟩
  · exact ⟨devices.ports, devices.consoleRead, devices.consoleType, devices.vector⟩
  · change (nativeHost outer ((guestStack guest.vm ret).data ((guestStack guest.vm ret).ptr - 1) +
        (if short then 1 else 0)) ((guestStack guest.vm ret).data ((guestStack guest.vm ret).ptr - 2))).read Port.System.state =
        (deviceWriteHost guest.vm guest ret short).read Port.System.state
    simp only [nativeHost_system, deviceWriteHost, deviceHost_read]
    cases short
    · simp [image.system]
    · have different := Ne.symm (high rfl)
      simp only [BitVec.ofNat_eq_ofNat] at different
      simp [host_write_read, different, image.system]
  · simp only [deviceWriteHost, deviceHost_control]
    cases short <;> exact image.guestControl
  · exact (nativeHost_control _ _ _).trans image.outerControl
  · exact (nativeHost_vector _ _ _).trans image.outerVector
  · rw [frame 0 (by rw [image.pointer]; cases invocation <;> simp [Invocation.pointer]),
        frame 1 (by rw [image.pointer]; cases invocation <;> simp [Invocation.pointer])]
    exact image.firstReturn
  · intro reset
    subst invocation
    rw [frame 2 (by rw [image.pointer]; decide), frame 3 (by rw [image.pointer]; decide)]
    exact image.resetReturn rfl

end ProgramProofs.Uxnmin.Model
