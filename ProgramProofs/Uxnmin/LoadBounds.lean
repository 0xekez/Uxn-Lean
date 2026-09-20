import ProgramProofs.Uxnmin.LoadObservation
import ProgramProofs.Uxnmin.Confinement

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Every byte read by a load is within the guest RAM region. -/
theorem Confined.load_address_lt {start : Configuration}
    (confined : Confined start) (kind : AddressMode) (vm : Uxn.State) (host : Uxn.Host.State)
    (world : Void IO.RealWorld) (after : ReturnTo)
    (reachable : Reachable start (.running {host with vm} world))
    (control : host.control = .evaluating after)
    (opcode : vm.mem.ram vm.pc &&& 0x1f = kind.loadOpcode)
    (second : Bool) (short : second = true → (vm.mem.ram vm.pc).getLsbD 5 = true) :
    ((if second then kind.following else id)
      (kind.address { vm with pc := vm.pc + 1 } ((vm.mem.ram vm.pc).getLsbD 6))).toNat < ramSize := by
  let ret := (vm.mem.ram vm.pc).getLsbD 6
  let keep := (vm.mem.ram vm.pc).getLsbD 7
  let index := (if keep then (guestStack vm ret).ptr else (guestStack vm ret).ptr - kind.consumed) +
    (if second then 1 else 0)
  let observe : Configuration → Byte
    | .running state _ => (guestStack state.vm ret).data index
    | _ => 0
  have unchanged (ram : Word → Byte) (state : Configuration) :
      observe (replaceOutside ram state) = observe state := by
    cases state with
    | starting => rfl
    | failed => rfl
    | running => cases ret <;> rfl
  have fetch := confined.pc_lt {host with vm} world after reachable control
  have read (ram : Word → Byte) :
      (Configuration.next (replaceOutside ram (.running {host with vm} world))).map observe =
        some ((replaceRAM ram vm).mem.ram
          ((if second then kind.following else id) (kind.address { vm with pc := vm.pc + 1 } ret))) := by
    have step := guest_load kind (replaceRAM ram vm)
      (by simpa [replaceRAM, fetch] using opcode)
    change (Configuration.next (.running {host with vm := replaceRAM ram vm} world)).map observe = _
    rw [configuration_next_pure (state := {host with vm := replaceRAM ram vm}) after world control step]
    have fetched : (replaceRAM ram vm).mem.ram (replaceRAM ram vm).pc = vm.mem.ram vm.pc := by
      simp [replaceRAM, fetch]
    rw [fetched]
    change some ((guestStack (loadResult kind
      { replaceRAM ram vm with pc := vm.pc + 1 }
      ret ((vm.mem.ram vm.pc).getLsbD 5) keep) ret).data index) = _
    have stack : guestStack { replaceRAM ram vm with pc := vm.pc + 1 } ret =
        guestStack vm ret := by cases ret <;> rfl
    have address : kind.address { replaceRAM ram vm with pc := vm.pc + 1 } ret =
        kind.address { vm with pc := vm.pc + 1 } ret := by cases kind <;> cases ret <;> rfl
    cases second
    · have first := loadResult_first kind { replaceRAM ram vm with pc := vm.pc + 1 }
        ret ((vm.mem.ram vm.pc).getLsbD 5) keep
      rw [stack, address] at first
      simpa [index] using congrArg some first
    · rw [short rfl]
      have last := loadResult_second kind { replaceRAM ram vm with pc := vm.pc + 1 } ret keep
      rw [stack, address] at last
      exact congrArg some last
  by_contra outside
  have same := (confined.observe reachable observe unchanged (fun _ => 0)).trans
    (confined.observe reachable observe unchanged (fun _ => 1)).symm
  rw [read, read] at same
  simp only [replaceRAM, ret, if_neg outside] at same
  contradiction

end ProgramProofs.Uxnmin.Model
