import ProgramProofs.Uxnmin.LoadObservation
import ProgramProofs.Uxnmin.Confinement

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host

/-- Every byte read by a load is within the guest RAM region. -/
theorem Semantics.Confined.load_address_lt {start : Configuration}
    (confined : Confined start) (kind : AddressMode) (vm : Uxn.State) (host : Uxn.Host.State)
    (world : Void IO.RealWorld) (reachable : Reachable start (.ok (.next vm, host) world))
    (opcode : vm.mem.ram vm.pc &&& 0x1f = kind.loadOpcode)
    (second : Bool) (short : second = true → (vm.mem.ram vm.pc).getLsbD 5 = true) :
    ((if second then kind.following else id)
      (kind.address { vm with pc := vm.pc + 1 } ((vm.mem.ram vm.pc).getLsbD 6))).toNat < ramSize := by
  let ret := (vm.mem.ram vm.pc).getLsbD 6
  let keep := (vm.mem.ram vm.pc).getLsbD 7
  let index := (if keep then (guestStack vm ret).ptr else (guestStack vm ret).ptr - kind.consumed) +
    (if second then 1 else 0)
  let observe : Configuration → Byte
    | .ok (.next vm', _) _ | .ok (.brk vm', _) _ => (guestStack vm' ret).data index
    | .error _ _ => 0
  have unchanged (ram : Word → Byte) (state : Configuration) :
      observe (replaceOutside ramSize ram state) = observe state := by
    cases state with
    | error => rfl
    | ok pair world => cases pair with | mk outcome host => cases outcome <;> cases ret <;> rfl
  have fetch := confined.pc_lt vm host world reachable
  have read (ram : Word → Byte) :
      (next (replaceOutside ramSize ram (.ok (.next vm, host) world))).map observe =
        some ((replaceOutside.replace ramSize ram vm).mem.ram
          ((if second then kind.following else id) (kind.address { vm with pc := vm.pc + 1 } ret))) := by
    have step := guest_load kind (replaceOutside.replace ramSize ram vm)
      (by simpa [replaceOutside.replace, fetch] using opcode)
    simp only [replaceOutside, next, Uxn.Host.step, step]
    have fetched : (replaceOutside.replace ramSize ram vm).mem.ram (replaceOutside.replace ramSize ram vm).pc = vm.mem.ram vm.pc := by
      simp [replaceOutside.replace, fetch]
    rw [fetched]
    change some ((guestStack (loadResult kind
      { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 }
      ret ((vm.mem.ram vm.pc).getLsbD 5) keep) ret).data index) = _
    have stack : guestStack { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 } ret =
        guestStack vm ret := by cases ret <;> rfl
    have address : kind.address { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 } ret =
        kind.address { vm with pc := vm.pc + 1 } ret := by cases kind <;> cases ret <;> rfl
    cases second
    · have first := loadResult_first kind { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 }
        ret ((vm.mem.ram vm.pc).getLsbD 5) keep
      rw [stack, address] at first
      simpa [index] using congrArg some first
    · rw [short rfl]
      have last := loadResult_second kind { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 } ret keep
      rw [stack, address] at last
      exact congrArg some last
  by_contra outside
  have same := (confined.observe reachable observe unchanged (fun _ => 0)).trans
    (confined.observe reachable observe unchanged (fun _ => 1)).symm
  rw [read, read] at same
  simp only [replaceOutside.replace, ret, if_neg outside] at same
  contradiction

end ProgramProofs.Uxnmin
