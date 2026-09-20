import ProgramProofs.Uxnmin.Loader.Boot
import ProgramProofs.Uxnmin.PureBlocks
import ProgramProofs.Uxnmin.DeliveryBlock
import ProgramProofs.Uxnmin.Loading

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem loader_after_file (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index : Byte) (input loaded : Uxn.Host.State) (program : ByteArray)
    (fits : program.size ≤ ramSize - 0x100)
    (inputMemory : input.vm.mem.ram = Function.update ram 0x13e index)
    (inputReturning : input.vm.mem.rstk.ptr = 0)
    (control : loaded.control = .evaluating (.console .input))
    (loadedVM : loaded.vm = ({ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
      (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} : Patch).apply
        {input.vm with pc := 0x136, mem.wstk.ptr := 0}) :
    ∃ final : Uxn.Host.State, PureReaches loaded final ∧
      final.control = .evaluating (.console .input) ∧ final.read 0x0f = loaded.read 0x0f ∧
      final.vm.pc = 0x16d ∧ final.consoleVector = 0 ∧
      final.vm.mem.ram = Function.update (Function.update
        (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
          (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} input.vm).mem.ram 0x45 1) 0x46 0 ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 4 ∧
      final.vm.mem.rstk.data 0 = 1 ∧ final.vm.mem.rstk.data 1 = 0x39 ∧
      final.vm.mem.rstk.data 2 = 1 ∧ final.vm.mem.rstk.data 3 = 0x54 := by
  let loadedRAM : Word → Byte := fun address =>
    if 0x959 ≤ address.toNat ∧ address.toNat < 0x959 + program.size then
      program.data[address.toNat - 0x959]!.toBitVec else ram address
  have space : (0x959#16).toNat + program.size ≤ 0x10000 := by
    change 0x959 + program.size ≤ 0x10000
    dsimp [ramSize] at fits
    omega
  have loadedMemory : loaded.vm.mem.ram = Function.update loadedRAM 0x13e index := by
    funext address
    rw [loadedVM]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [file_patch_ram _ _ _ _ space]
    simp only [inputMemory]
    by_cases same : address = 0x13e
    · subst address; simp [loadedRAM]
    · simp only [BitVec.ofNat_eq_ofNat] at same
      simp only [loadedRAM, Function.update_of_ne same, BitVec.ofNat_eq_ofNat,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have loadedCode : Code rom rom.size loadedRAM := by
    intro i
    have small : (0x100 + BitVec.ofNat 16 i.val).toNat < 0x959 := by
      have bound : i.val < 0x456 := i.isLt
      bv_omega
    dsimp only [loadedRAM]
    rw [if_neg (by omega)]
    exact hc i
  have shape : machine (Function.update loadedRAM 0x13e index) 0x136
      ⟨loaded.vm.mem.wstk.data, 0⟩ ⟨loaded.vm.mem.rstk.data, 0⟩ = loaded.vm := by
    have returning : loaded.vm.mem.rstk.ptr = 0 := by simpa [loadedVM, Patch.apply] using inputReturning
    have working : loaded.vm.mem.wstk.ptr = 0 := by simp [loadedVM, Patch.apply]
    have pc : loaded.vm.pc = 0x136 := by simp [loadedVM, Patch.apply]
    rw [stack_zero _ working, stack_zero _ returning, ← loadedMemory, ← pc]
    exact machine_self loaded.vm
  obtain ⟨final, boot, finalControl, halt, pc, vector, memory, wp, rp, frame0, frame1, frame2, frame3⟩ :=
    loader_boot loadedRAM loadedCode index loaded.vm.mem.wstk.data loaded.vm.mem.rstk.data loaded
  have outputRAM : Function.update (Function.update (Function.update loadedRAM 0x13e index) 0x45 1) 0x46 0 =
      Function.update (Function.update (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
        (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} input.vm).mem.ram 0x45 1) 0x46 0 := by
    rw [← loadedMemory]
    congr 2
    funext address
    rw [loadedVM]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [file_patch_ram _ _ _ _ space, file_patch_ram _ _ _ _ space]
  refine ⟨final, ?_, finalControl, halt, pc, vector, memory.trans outputRAM, wp, rp, frame0, frame1, frame2, frame3⟩
  rw [shape] at boot
  simpa only [← control] using boot

end ProgramProofs.Uxnmin.Model
