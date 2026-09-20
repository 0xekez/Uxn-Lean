import ProgramProofs.Uxnmin.ImmediateObservation
import ProgramProofs.Uxnmin.Confinement

set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Every immediate byte actually read by the direct instruction is confined.
The untaken JCI branch has no operand-read premise to discharge. -/
theorem Confined.immediate_address_lt {start : Configuration}
    (confined : Confined start) (kind : ImmediateKind)
    (vm : Uxn.State) (host : Uxn.Host.State) (world : Void IO.RealWorld)
    (after : ReturnTo) (control : host.control = .evaluating after)
    (reachable : Reachable start (.running {host with vm} world))
    (opcode : vm.mem.ram vm.pc = kind.opcode) (second : Bool) (read : kind.reads vm second) :
    (vm.pc + 1 + if second then 1 else 0).toNat < ramSize := by
  let observe : Configuration → Byte
    | .running state _ => immediateObserve kind vm second state.vm
    | _ => 0
  have stable (ram : Word → Byte) (result : Uxn.State) :
      immediateObserve kind vm second (replaceRAM ram result) =
        immediateObserve kind vm second result := by
    cases kind with
    | jci | jmi | jsi => rfl
    | lit short ret => cases ret <;> rfl
  have unchanged (ram : Word → Byte) (state : Configuration) :
      observe (replaceOutside ram state) = observe state := by
    cases state with
    | starting => rfl
    | failed => rfl
    | running state _ => exact stable ram state.vm
  have fetch := confined.pc_lt {host with vm} world after reachable control
  have recover (ram : Word → Byte) :
      (Configuration.next (replaceOutside ram (.running {host with vm} world))).map observe =
        some ((replaceRAM ram vm).mem.ram
          (vm.pc + 1 + if second then 1 else 0)) := by
    have step := guest_immediate kind (replaceRAM ram vm)
      (by simpa [replaceRAM, fetch] using opcode)
    dsimp only [replaceRAM] at step
    simp only [replaceOutside, Configuration.next, Uxn.Host.State.next, control, Uxn.Host.step, step]
    change some (immediateObserve kind vm second
      (immediateNext kind (replaceRAM ram vm))) = _
    have reads : kind.reads (replaceRAM ram vm) second := by
      cases kind <;> exact read
    have observed := immediate_observed kind (replaceRAM ram vm) second reads
    have source (result : Uxn.State) :
        immediateObserve kind (replaceRAM ram vm) second result =
          immediateObserve kind vm second result := by
      cases kind with
      | jci | jmi | jsi => rfl
      | lit short ret => cases ret <;> rfl
    rw [source] at observed
    exact congrArg some observed
  by_contra outside
  have same := (confined.observe reachable observe unchanged (fun _ => 0)).trans
    (confined.observe reachable observe unchanged (fun _ => 1)).symm
  rw [recover, recover] at same
  simp only [replaceRAM, if_neg outside] at same
  contradiction

end ProgramProofs.Uxnmin.Model
