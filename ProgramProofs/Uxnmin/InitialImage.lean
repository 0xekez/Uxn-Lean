import ProgramProofs.Uxnmin.Loading
import ProgramProofs.Uxnmin.Representation

set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- Before execution, the native image contains the ROM and zeroed interpreter data. -/
theorem initial_image :
    CodeImage (initialState rom).vm.mem.ram ∧
    (∀ address : Word, 0x555 ≤ address.toNat → (initialState rom).vm.mem.ram address = 0) ∧
    (initialState rom).vm.mem.ram 0x199 = 0 ∧
    (initialState rom).vm.mem.ram 0x1a4 = 0 := by
  have zeroes (memory : Word → Byte) (code : Code rom rom.size memory) :
      memory 0x555 = 0 ∧ memory 0x199 = 0 ∧ memory 0x1a4 = 0 := by
    exact ⟨code ⟨0x455, by decide⟩, code ⟨0x99, by decide⟩, code ⟨0xa4, by decide⟩⟩
  have code := Code.initial rom rom.size (Nat.le_refl _) (by decide)
  have size : rom.size = 0x456 := rfl
  obtain ⟨lastByte, consoleRead, consoleType⟩ := zeroes _ code
  refine ⟨?_, ?_, consoleRead, consoleType⟩
  · intro address lower upper _
    exact code.read address lower (by rw [size]; omega)
  · intro address lower
    by_cases last : address.toNat = 0x555
    · have same : address = 0x555 := by bv_omega
      exact (congrArg (initialState rom).vm.mem.ram same).trans lastByte
    · rw [initial_ram_eq, if_neg]
      rw [size]
      omega

/-- The loader's RAM patch and PC initialization establish the complete guest representation. -/
theorem loaded_representation (program : ByteArray) (input outer : Uxn.State)
    (fits : program.size ≤ ramSize - 0x100)
    (code : CodeImage input.mem.ram)
    (empty : ∀ address : Word, 0x555 ≤ address.toNat → input.mem.ram address = 0)
    (memory : outer.mem.ram = Function.update (Function.update
      (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
        (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} input).mem.ram 0x45 1) 0x46 0) :
    Represents (initialState program).vm outer := by
  obtain ⟨guest, before⟩ := file_patch_loads_guest program input fits (fun address bound => empty address (by omega))
  have unchanged (address : Word) (bound : address.toNat < 0x959)
      (high : address ≠ 0x45) (low : address ≠ 0x46) :
      outer.mem.ram address = input.mem.ram address := by
    rw [memory, Function.update_of_ne low, Function.update_of_ne high]
    exact before address bound
  constructor
  · intro address lower upper immutable
    rw [unchanged address (by omega) (by bv_omega) (by bv_omega)]
    exact code address lower upper immutable
  · intro address bound
    have large : 0x859 ≤ (relocate address).toNat := by
      dsimp [relocate, ramSize] at *
      bv_omega
    rw [memory, Function.update_of_ne (by bv_omega : relocate address ≠ 0x46),
      Function.update_of_ne (by bv_omega : relocate address ≠ 0x45)]
    exact guest address bound
  · intro ret index
    rw [unchanged]
    · rw [empty]
      · cases ret <;> rfl
      · cases ret <;> dsimp [stackBase] <;> bv_omega
    · cases ret <;> dsimp [stackBase] <;> bv_omega
    · cases ret <;> dsimp [stackBase] <;> bv_omega
    · cases ret <;> dsimp [stackBase] <;> bv_omega
  · intro ret
    rw [unchanged]
    · rw [empty]
      · cases ret <;> rfl
      · cases ret <;> decide
    · cases ret <;> decide
    · cases ret <;> decide
    · cases ret <;> decide
  · rw [memory]
    simp [initialState, Uxn.Host.State.write]
  · rw [memory]
    simp [initialState, Uxn.Host.State.write]

/-- The same load leaves the zeroed shadow devices and input literals intact. -/
theorem loaded_devices (program : ByteArray) (input outer : Uxn.State)
    (fits : program.size ≤ ramSize - 0x100)
    (empty : ∀ address : Word, 0x555 ≤ address.toNat → input.mem.ram address = 0)
    (consoleRead : input.mem.ram 0x199 = 0) (consoleType : input.mem.ram 0x1a4 = 0)
    (memory : outer.mem.ram = Function.update (Function.update
      (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
        (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} input).mem.ram 0x45 1) 0x46 0) :
    (∀ port : Byte, outer.mem.ram (0x759 + port.setWidth 16) = (initialState program).read port) ∧
    outer.mem.ram 0x199 = (initialState program).read Port.Console.read ∧
    outer.mem.ram 0x1a4 = (initialState program).read Port.Console.type := by
  have before := (file_patch_loads_guest program input fits
    (fun address bound => empty address (by omega))).2
  have unchanged (address : Word) (bound : address.toNat < 0x959)
      (high : address ≠ 0x45) (low : address ≠ 0x46) :
      outer.mem.ram address = input.mem.ram address := by
    rw [memory, Function.update_of_ne low, Function.update_of_ne high]
    exact before address bound
  refine ⟨?_, ?_, ?_⟩
  · intro port
    rw [unchanged _ (by bv_omega) (by bv_omega) (by bv_omega), empty _ (by bv_omega)]
    simp [initialState, Uxn.Host.State.write, Uxn.Host.State.read, Vector.get]
  · rw [unchanged _ (by decide) (by decide) (by decide), consoleRead]
    simp [initialState, Uxn.Host.State.write, Uxn.Host.State.read, Vector.get]
  · rw [unchanged _ (by decide) (by decide) (by decide), consoleType]
    rfl

end ProgramProofs.Uxnmin
