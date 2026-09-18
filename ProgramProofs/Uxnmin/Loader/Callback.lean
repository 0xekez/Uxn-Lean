import ProgramProofs.Uxnmin.Loader.Prefix
import ProgramProofs.Uxnmin.Loader.FileInstruction
import ProgramProofs.Uxnmin.Loader.Boot
import ProgramProofs.Uxnmin.Loading

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private Uxn.Host.fileName from Uxn.Host

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- The final argument callback reaches the file-reading instruction. -/
theorem argument_terminator (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index : Byte) (host : Uxn.Host.State) (fuel : Nat)
    (vector : host.consoleVector = 0x118)
    (memory : host.vm.mem.ram = Function.update ram 0x13e index)
    (working : host.vm.mem.wstk.ptr = 0) (returning : host.vm.mem.rstk.ptr = 0) :
    ∃ vm : Uxn.State, ∃ final : Uxn.Host.State,
      run.consoleInput 10 4 {host with fuel := some (fuel + 14)} = evalLoop (.next vm) final ∧
      final.fuel = some fuel ∧ final.read 0x0f = host.read 0x0f ∧ vm.pc = 0x135 ∧
      final.file.name = some 0 ∧ final.file.length = 0xf6a7 ∧ final.file.handle = none ∧
      vm.mem.ram = Function.update ram 0x13e index ∧
      vm.mem.wstk.ptr = 3 ∧ vm.mem.rstk.ptr = 0 ∧
      vm.mem.wstk.data 0 = 0x09 ∧ vm.mem.wstk.data 1 = 0x59 ∧
      vm.mem.wstk.data 2 = 0xac := by
  have read_eq (host : Uxn.Host.State) (port : Byte) : host.read port = host.ports[port.toNat] := rfl
  obtain ⟨vm, final, executed, budget, halt, pc, name, length, handle, ram', wptr, rptr, high, low, port⟩ :=
    load_prefix_continue ram hc index host.vm.mem.wstk.data host.vm.mem.rstk.data
      ((host.write 0x12 10).write 0x17 4) fuel
      (by simp [read_eq, Host.State.write])
  have machine_eq : {host.vm with pc := 0x118} = machine (Function.update ram 0x13e index) 0x118
      ⟨host.vm.mem.wstk.data, 0⟩ ⟨host.vm.mem.rstk.data, 0⟩ := by
    cases hvm : host.vm with
    | mk pc mem =>
      cases mem with
      | mk ram w r =>
        cases w
        cases r
        simp_all [machine]
  refine ⟨vm, final, ?_, budget, ?_, pc, name, length, handle, ram', wptr, rptr, high, low, port⟩
  · unfold run.consoleInput eval
    simp only [uxn_state]
    simp only [BitVec.ofNat_eq_ofNat] at machine_eq
    simp [uxn_state, vector, Host.State.write] at executed ⊢
    rw [machine_eq]
    exact executed
  · simpa [read_eq, Host.State.write, Vector.getElem_set] using halt

/-- The final filename callback reads the guest file and establishes the evaluation loop. -/
theorem console_load (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index : Byte) (host : Uxn.Host.State) (filename : String) (program : ByteArray)
    (before after : Void IO.RealWorld)
    (fits : program.size ≤ ramSize - 0x100)
    (vector : host.consoleVector = 0x118)
    (memory : host.vm.mem.ram = Function.update ram 0x13e index)
    (working : host.vm.mem.wstk.ptr = 0) (returning : host.vm.mem.rstk.ptr = 0)
    (decode : Uxn.Host.fileName host.vm.mem 0 = some filename)
    (read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) before =
      .ok program after) :
    ∃ final : Uxn.Host.State,
      run.consoleInput 10 4 {host with fuel := some 25} before = .ok ((), final) after ∧
      final.fuel = some 0 ∧ final.read 0x0f = host.read 0x0f ∧
      final.vm.pc = 0x16d ∧ final.consoleVector = 0 ∧
      final.vm.mem.ram = Function.update (Function.update
        (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
          (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} host.vm).mem.ram 0x45 1) 0x46 0 ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 4 ∧
      final.vm.mem.rstk.data 0 = 1 ∧ final.vm.mem.rstk.data 1 = 0x39 ∧
      final.vm.mem.rstk.data 2 = 1 ∧ final.vm.mem.rstk.data 3 = 0x54 := by
  obtain ⟨vm, prepared, startBlock, budget, halt, pc, name, length, handle, ram', wptr, rptr,
      high, low, port⟩ := argument_terminator ram hc index host 11 vector memory working returning
  have instruction : vm.mem.ram 0x135 = 0x37 := by
    rw [ram']
    change Function.update ram 0x13e#16 index 0x135#16 = 0x37#8
    rw [Function.update_of_ne (by decide : 0x135#16 ≠ 0x13e#16)]
    exact hc ⟨53, by decide⟩
  have decode' : Uxn.Host.fileName vm.mem 0 = some filename := by
    have same : vm.mem.ram = host.vm.mem.ram := ram'.trans memory.symm
    simpa only [Uxn.Host.fileName, same] using decode
  obtain ⟨loadedHost, load, loadedBudget, loadedHalt, loadedVector, loadedVM⟩ :=
    file_deo_continue vm prepared filename program before after 10 pc instruction wptr high low port
      name length handle decode' read
  let patched := Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
      (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} {vm with pc := 0x136, mem.wstk.ptr := 0}
  let loadedRAM : Word → Byte := fun address =>
    if 0x959 ≤ address.toNat ∧ address.toNat < 0x959 + program.size then
      program.data[address.toNat - 0x959]!.toBitVec
    else ram address
  have space : (0x959#16).toNat + program.size ≤ 0x10000 := by
    change 0x959 + program.size ≤ 0x10000
    dsimp [ramSize] at fits
    omega
  have loadedMemory : patched.mem.ram = Function.update loadedRAM 0x13e index := by
    funext address
    dsimp only [patched]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [file_patch_ram _ _ _ _ space]
    simp only [ram']
    by_cases same : address = 0x13e
    · subst address
      simp [loadedRAM]
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
  have shape : patched = machine (Function.update loadedRAM 0x13e index) 0x136
      ⟨patched.mem.wstk.data, 0⟩ ⟨patched.mem.rstk.data, 0⟩ := by
    have : patched.mem.rstk.ptr = 0 := by simpa [patched, Patch.apply] using rptr
    have : patched.mem.wstk.ptr = 0 := by simp [patched, Patch.apply]
    have : patched.pc = 0x136 := by simp [patched, Patch.apply]
    cases hvm : patched with
    | mk pc mem =>
      cases mem with
      | mk ram w r =>
        cases w
        cases r
        simp_all [machine]
  obtain ⟨bootVM, bootHost, boot, bootBudget, bootHalt, bootPC, bootVector, bootRAM,
      bootWptr, bootRptr, frame0, frame1, frame2, frame3⟩ :=
    post_load_boot_continue loadedRAM loadedCode index patched.mem.wstk.data patched.mem.rstk.data loadedHost 0
  have outputRAM : Function.update (Function.update (Function.update loadedRAM 0x13e index) 0x45 1) 0x46 0 =
      Function.update (Function.update (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
        (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} host.vm).mem.ram 0x45 1) 0x46 0 := by
    rw [← loadedMemory]
    congr 2
    funext address
    dsimp only [patched]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [file_patch_ram _ _ _ _ space, file_patch_ram _ _ _ _ space]
    simp only [ram', memory]
  refine ⟨{bootHost with vm := bootVM}, ?_, bootBudget, bootHalt.trans (loadedHalt.trans halt),
    bootPC, bootVector, bootRAM.trans outputRAM, bootWptr, bootRptr, frame0, frame1, frame2, frame3⟩
  have pause : evalLoop (.next bootVM) bootHost = pure ((), {bootHost with vm := bootVM}) := by
    rw [evalLoop.eq_def]
    simp [uxn_state, bootBudget]
  rw [← loadedBudget] at boot
  rw [← shape] at boot
  rw [← budget] at load
  change evalLoop (.next vm) prepared before = evalLoop (.next patched) loadedHost after at load
  rw [startBlock, load, boot, pause]
  rfl

end ProgramProofs.Uxnmin
