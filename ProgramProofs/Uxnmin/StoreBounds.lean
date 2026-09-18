import ProgramProofs.Uxnmin.StoreObservation
import ProgramProofs.Uxnmin.Confinement

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host

/-- Every byte written by a store is within the guest RAM region. -/
theorem Semantics.Confined.store_address_lt {start : Configuration}
    (confined : Confined start) (kind : AddressMode) (vm : Uxn.State) (host : Uxn.Host.State)
    (world : Void IO.RealWorld) (reachable : Reachable start (.ok (.next vm, host) world))
    (opcode : vm.mem.ram vm.pc &&& 0x1f = kind.storeOpcode)
    (second : Bool) (short : second = true → (vm.mem.ram vm.pc).getLsbD 5 = true) :
    ((if second then kind.following else id)
      (kind.address { vm with pc := vm.pc + 1 } ((vm.mem.ram vm.pc).getLsbD 6))).toNat < ramSize := by
  let ret := (vm.mem.ram vm.pc).getLsbD 6
  let width := (vm.mem.ram vm.pc).getLsbD 5
  let keep := (vm.mem.ram vm.pc).getLsbD 7
  let address := (if second then kind.following else id) (kind.address { vm with pc := vm.pc + 1 } ret)
  let value := ((if width && !second then fun value : Word => value >>> 8 else id)
    (operand (guestStack vm ret) ((guestStack vm ret).ptr - kind.consumed) width)).setWidth 8
  have fetch := confined.pc_lt vm host world reachable
  have stored (ram : Word → Byte) :
      (storeResult kind { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 }
        ret width keep).mem.ram address = value := by
    have write := storeResult_byte kind { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 }
      ret width keep second short
    have stack : guestStack { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 } ret =
        guestStack vm ret := by cases ret <;> rfl
    have place : kind.address { replaceOutside.replace ramSize ram vm with pc := vm.pc + 1 } ret =
        kind.address { vm with pc := vm.pc + 1 } ret := by cases kind <;> cases ret <;> rfl
    rw [stack, place] at write
    exact write
  by_contra outside
  have same := confined _ reachable (fun _ => value + 1)
  have step := guest_store kind (replaceOutside.replace ramSize (fun _ => value + 1) vm)
    (by simpa [replaceOutside.replace, fetch] using opcode)
  simp only [replaceOutside, next, Uxn.Host.step, step, guest_store kind vm opcode] at same
  have fetched : (replaceOutside.replace ramSize (fun _ => value + 1) vm).mem.ram
      (replaceOutside.replace ramSize (fun _ => value + 1) vm).pc = vm.mem.ram vm.pc := by
    simp [replaceOutside.replace, fetch]
  rw [fetched] at same
  have memory := congrArg (fun state : Configuration => match state with
    | .ok (.next vm', _) _ | .ok (.brk vm', _) _ => vm'.mem.ram address
    | .error _ _ => 0) (Option.some.inj same)
  change (storeResult kind { replaceOutside.replace ramSize (fun _ => value + 1) vm with pc := vm.pc + 1 }
    ret width keep).mem.ram address =
      (if address.toNat < ramSize then (storeResult kind { vm with pc := vm.pc + 1 } ret width keep).mem.ram address
       else value + 1) at memory
  rw [stored, if_neg outside] at memory
  bv_omega

end ProgramProofs.Uxnmin
