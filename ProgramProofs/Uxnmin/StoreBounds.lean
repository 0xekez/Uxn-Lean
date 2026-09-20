import ProgramProofs.Uxnmin.StoreObservation
import ProgramProofs.Uxnmin.Confinement

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Every byte written by a store is within the guest RAM region. -/
theorem Confined.store_address_lt {start : Configuration}
    (confined : Confined start) (kind : AddressMode) (vm : Uxn.State) (host : Uxn.Host.State)
    (world : Void IO.RealWorld) (after : ReturnTo)
    (reachable : Reachable start (.running {host with vm} world))
    (control : host.control = .evaluating after)
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
  have fetch := confined.pc_lt {host with vm} world after reachable control
  have stored (ram : Word → Byte) :
      (storeResult kind { replaceRAM ram vm with pc := vm.pc + 1 }
        ret width keep).mem.ram address = value := by
    have write := storeResult_byte kind { replaceRAM ram vm with pc := vm.pc + 1 }
      ret width keep second short
    have stack : guestStack { replaceRAM ram vm with pc := vm.pc + 1 } ret =
        guestStack vm ret := by cases ret <;> rfl
    have place : kind.address { replaceRAM ram vm with pc := vm.pc + 1 } ret =
        kind.address { vm with pc := vm.pc + 1 } ret := by cases kind <;> cases ret <;> rfl
    rw [stack, place] at write
    exact write
  by_contra outside
  have same := confined _ _ reachable (fun _ => value + 1)
  have step := guest_store kind (replaceRAM (fun _ => value + 1) vm)
    (by simpa [replaceRAM, fetch] using opcode)
  change Configuration.next (.running {host with vm := replaceRAM (fun _ => value + 1) vm} world) =
    (Configuration.next (.running {host with vm} world)).map (replaceOutside (fun _ => value + 1)) at same
  rw [configuration_next_pure (state := {host with vm := replaceRAM (fun _ => value + 1) vm})
      after world control step,
    configuration_next_pure (state := {host with vm}) after world control (guest_store kind vm opcode)] at same
  have fetched : (replaceRAM (fun _ => value + 1) vm).mem.ram
      (replaceRAM (fun _ => value + 1) vm).pc = vm.mem.ram vm.pc := by
    simp [replaceRAM, fetch]
  rw [fetched] at same
  have memory := congrArg (fun state : Configuration => match state with
    | .running state _ => state.vm.mem.ram address
    | _ => 0) (Option.some.inj same)
  change (storeResult kind { replaceRAM (fun _ => value + 1) vm with pc := vm.pc + 1 }
    ret width keep).mem.ram address =
      (if address.toNat < ramSize then (storeResult kind { vm with pc := vm.pc + 1 } ret width keep).mem.ram address
       else value + 1) at memory
  rw [stored, if_neg outside] at memory
  bv_omega

end ProgramProofs.Uxnmin.Model
