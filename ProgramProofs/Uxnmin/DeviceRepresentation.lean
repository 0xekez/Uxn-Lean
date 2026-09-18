import ProgramProofs.Uxnmin.DeviceWriteHelper
import ProgramProofs.Uxnmin.Boundary

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- Device effects leave the represented read value equal to the last written byte. -/
theorem deviceHost_read (host : Uxn.Host.State) (port value address : Byte) :
    (deviceHost host port value).read address = if address = port then value else host.read address := by
  simp only [deviceHost]
  split <;> simp [Host.State.read, Host.State.write, Vector.get, Vector.getElem_set,
    Array.getElem_set, BitVec.toNat_inj, eq_comm]


/-- A raw high-byte device write changes only its shadow port. -/
theorem host_write_read (host : Uxn.Host.State) (port value address : Byte) :
    (host.write port value).read address = if address = port then value else host.read address := by
  simp [Host.State.read, Host.State.write, Vector.get, Vector.getElem_set,
    Array.getElem_set, BitVec.toNat_inj, eq_comm]

/-- Shadow ports and the self-modified console vector are outside represented guest state. -/
theorem Represents.writeDevice {guest outer : Uxn.State} (rep : Represents guest outer)
    (address : Word) (value : Byte)
    (available : address = 0x175 ∨ address = 0x176 ∨ (0x759 ≤ address.toNat ∧ address.toNat < 0x859)) :
    Represents guest {outer with mem.ram := Function.update outer.mem.ram address value} := by
  constructor
  · apply rep.code.write
    rcases available with rfl | rfl | after
    · exact .inr (.inr (by simp [MutableCode]))
    · exact .inr (.inr (by simp [MutableCode]))
    · exact .inr (.inl (by omega))
  · intro location confined
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.ram location confined
    · rcases available with rfl | rfl | bounds <;> dsimp [relocate, ramSize] at * <;> bv_omega
  · intro ret index
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.stackData ret index
    · rcases available with rfl | rfl | bounds <;> cases ret <;> dsimp [stackBase] <;> bv_omega
  · intro ret
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.stackPointer ret
    · rcases available with rfl | rfl | bounds <;> cases ret <;> dsimp [stackBase] <;> bv_omega
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.pcHigh
    · rcases available with rfl | rfl | bounds <;> bv_omega
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne]
    · exact rep.pcLow
    · rcases available with rfl | rfl | bounds <;> bv_omega

theorem Represents.deviceRam {guest outer : Uxn.State} (rep : Represents guest outer)
    (port value : Byte) : Represents guest {outer with mem.ram := deviceRam outer.mem.ram port value} := by
  have shadow := rep.writeDevice (0x759 + port.setWidth 16) value (.inr (.inr (by constructor <;> bv_omega)))
  unfold ProgramProofs.Uxnmin.deviceRam
  split
  · exact (shadow.writeDevice _ _ (.inl rfl)).writeDevice _ _ (.inr (.inl rfl))
  · exact shadow

/-- One shadow byte preserves the complete device image for a raw host write. -/
theorem DeviceImage.write {host : Uxn.Host.State} {outer : Uxn.State} (rep : DeviceImage host outer)
    (port value : Byte) (input : port ≠ Port.Console.read) (kind : port ≠ Port.Console.type) :
    DeviceImage (host.write port value)
      {outer with mem.ram := Function.update outer.mem.ram (0x759 + port.setWidth 16) value} := by
  constructor
  · intro address
    change Function.update _ _ _ _ = _
    rw [host_write_read]
    by_cases same : address = port
    · subst address; simp
    · rw [if_neg same, Function.update_of_ne (by bv_omega)]
      exact rep.ports address
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by bv_omega), host_write_read, if_neg (Ne.symm input)]
    exact rep.consoleRead
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by bv_omega), host_write_read, if_neg (Ne.symm kind)]
    exact rep.consoleType

/-- The output helper's shadow and vector updates preserve the device image. -/
theorem DeviceImage.deviceRam {host : Uxn.Host.State} {outer : Uxn.State} (rep : DeviceImage host outer)
    (port value : Byte) (input : port ≠ Port.Console.read) (kind : port ≠ Port.Console.type) :
    DeviceImage (deviceHost host port value) {outer with mem.ram := deviceRam outer.mem.ram port value} := by
  have image := rep.write port value input kind
  have sameRead (address : Byte) : (deviceHost host port value).read address = (host.write port value).read address := by
    rw [deviceHost_read, host_write_read]
  constructor
  · intro address
    rw [sameRead]
    change ProgramProofs.Uxnmin.deviceRam outer.mem.ram port value _ = _
    unfold ProgramProofs.Uxnmin.deviceRam
    split
    · rw [Function.update_of_ne (by bv_omega), Function.update_of_ne (by bv_omega)]
      exact image.ports address
    · exact image.ports address
  · rw [sameRead]
    change ProgramProofs.Uxnmin.deviceRam outer.mem.ram port value _ = _
    unfold ProgramProofs.Uxnmin.deviceRam
    split
    · simp only [Function.update_of_ne (by decide : (0x199 : Word) ≠ 0x176),
        Function.update_of_ne (by decide : (0x199 : Word) ≠ 0x175)]
      exact image.consoleRead
    · exact image.consoleRead
  · rw [sameRead]
    change ProgramProofs.Uxnmin.deviceRam outer.mem.ram port value _ = _
    unfold ProgramProofs.Uxnmin.deviceRam
    split
    · simp only [Function.update_of_ne (by decide : (0x1a4 : Word) ≠ 0x176),
        Function.update_of_ne (by decide : (0x1a4 : Word) ≠ 0x175)]
      exact image.consoleType
    · exact image.consoleType


/-- Device bytes survive changes to the interpreter's software-stack region. -/
theorem DeviceImage.writeStack {host : Uxn.Host.State} {outer : Uxn.State} (rep : DeviceImage host outer)
    (address : Word) (value : Byte) (lower : 0x555 ≤ address.toNat) (upper : address.toNat < 0x759) :
    DeviceImage host {outer with mem.ram := Function.update outer.mem.ram address value} := by
  constructor
  · intro port
    change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by bv_omega)]
    exact rep.ports port
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by bv_omega)]
    exact rep.consoleRead
  · change Function.update _ _ _ _ = _
    rw [Function.update_of_ne (by bv_omega)]
    exact rep.consoleType

theorem DeviceImage.transport {host : Uxn.Host.State} {outer replacement : Uxn.State}
    (rep : DeviceImage host outer) (ram : replacement.mem.ram = outer.mem.ram) : DeviceImage host replacement := by
  constructor
  · intro port; rw [ram]; exact rep.ports port
  · rw [ram]; exact rep.consoleRead
  · rw [ram]; exact rep.consoleType

end ProgramProofs.Uxnmin
