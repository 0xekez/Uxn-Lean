import ProgramProofs.Uxnmin.ImmediateObservation
import ProgramProofs.Uxnmin.Confinement

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host ProgramProofs.Uxnmin

/-- Every immediate byte actually read by the direct instruction is confined.
The untaken JCI branch has no operand-read premise to discharge. -/
theorem Semantics.Confined.immediate_address_lt {start : Configuration}
    (confined : ProgramProofs.Uxnmin.Semantics.Confined start) (kind : ImmediateKind)
    (vm : Uxn.State) (host : Uxn.Host.State) (world : Void IO.RealWorld)
    (reachable : Reachable start (.ok (.next vm, host) world))
    (opcode : vm.mem.ram vm.pc = kind.opcode) (second : Bool) (read : kind.reads vm second) :
    (vm.pc + 1 + if second then 1 else 0).toNat < ProgramProofs.Uxnmin.ramSize := by
  let observe : Configuration → Byte
    | .ok (.next result, _) _ | .ok (.brk result, _) _ => immediateObserve kind vm second result
    | .error _ _ => 0
  have stable (ram : Word → Byte) (result : Uxn.State) :
      immediateObserve kind vm second (replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram result) =
        immediateObserve kind vm second result := by
    cases kind with
    | jci | jmi | jsi => rfl
    | lit short ret => cases ret <;> rfl
  have unchanged (ram : Word → Byte) (state : Configuration) :
      observe (replaceOutside ProgramProofs.Uxnmin.ramSize ram state) = observe state := by
    cases state with
    | error => rfl
    | ok pair world =>
      cases pair with | mk outcome host => cases outcome <;> exact stable ram _
  have fetch := confined.pc_lt vm host world reachable
  have recover (ram : Word → Byte) :
      (next (replaceOutside ProgramProofs.Uxnmin.ramSize ram (.ok (.next vm, host) world))).map observe =
        some ((replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram vm).mem.ram
          (vm.pc + 1 + if second then 1 else 0)) := by
    have step := guest_immediate kind (replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram vm)
      (by simpa [replaceOutside.replace, fetch] using opcode)
    simp only [replaceOutside, next, Uxn.Host.step, step]
    change some (immediateObserve kind vm second
      (immediateNext kind (replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram vm))) = _
    have reads : kind.reads (replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram vm) second := by
      cases kind <;> exact read
    have observed := immediate_observed kind (replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram vm) second reads
    have source (result : Uxn.State) :
        immediateObserve kind (replaceOutside.replace ProgramProofs.Uxnmin.ramSize ram vm) second result =
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
  simp only [replaceOutside.replace, if_neg outside] at same
  contradiction

end ProgramProofs.Uxnmin
