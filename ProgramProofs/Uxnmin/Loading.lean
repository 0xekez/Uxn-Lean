import ProgramProofs.Uxnmin.Rom
import ProgramProofs.Host.Memory

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host

/-- The RAM patch produced by File/read has the expected byte-for-byte contents. -/
theorem file_patch_ram (bytes : ByteArray) (destination address : Word) (vm : Uxn.State)
    (fits : destination.toNat + bytes.size ≤ 0x10000) :
    (Patch.apply
      { ramWrites := bytes.data.toList.zipIdx.map fun (byte, i) =>
          (destination + BitVec.ofNat 16 i, byte.toBitVec) } vm).mem.ram address =
      if destination.toNat ≤ address.toNat ∧ address.toNat < destination.toNat + bytes.size then
        bytes.data[address.toNat - destination.toNat]!.toBitVec
      else vm.mem.ram address := by
  have load_bytes (bytes : List UInt8) (start : Nat) (ram : Word → Byte)
      (fits : start + bytes.length ≤ 0x10000) (address : Word) :
      (bytes.zipIdx start).foldl
        (fun memory (byte, index) => Function.update memory (BitVec.ofNat 16 index) byte.toBitVec) ram address =
      if start ≤ address.toNat ∧ address.toNat < start + bytes.length then
        bytes[address.toNat - start]!.toBitVec
      else ram address := by
    induction bytes generalizing start ram with
    | nil => simp only [List.zipIdx_nil, List.foldl_nil]; rw [if_neg (by simp)]
    | cons byte bytes ih =>
      have bound : start < 0x10000 := by simp only [List.length_cons] at fits; omega
      have same : address = BitVec.ofNat 16 start ↔ address.toNat = start := by
        rw [← BitVec.toNat_inj]
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
      rw [List.zipIdx_cons, List.foldl_cons, ih (start + 1) _ (by simp only [List.length_cons] at fits; omega)]
      by_cases head : address.toNat = start
      · simp [head, Function.update_apply, same, Nat.not_succ_le_self]
      · by_cases inside : start ≤ address.toNat ∧ address.toNat < start + (byte :: bytes).length
        · have tail : start + 1 ≤ address.toNat ∧ address.toNat < start + 1 + bytes.length := by
            simp only [List.length_cons] at inside; omega
          have index : address.toNat - start = address.toNat - (start + 1) + 1 := by omega
          simp only [if_pos tail, if_pos inside, index, List.getElem!_cons_succ]
        · have tail : ¬ (start + 1 ≤ address.toNat ∧ address.toNat < start + 1 + bytes.length) := by
            simp only [List.length_cons] at inside; omega
          rw [if_neg tail, if_neg inside]
          exact Function.update_of_ne (mt same.mp head) _ _

  have read := load_bytes bytes.data.toList destination.toNat vm.mem.ram
    (by simpa using fits) address
  rw [List.zipIdx_eq_map_add] at read
  simp only [List.foldl_map, BitVec.ofNat_add,
    BitVec.ofNat_toNat, Array.length_toList, Array.getElem!_toList] at read
  simpa only [Patch.apply, List.foldl_map, BitVec.setWidth_eq, ByteArray.size] using read

/-- File/read places a ROM into the interpreter's guest RAM without touching
its code, stacks, device cache, or guest zero page. -/
theorem file_patch_loads_guest (program : ByteArray) (vm : Uxn.State)
    (fits : program.size ≤ ramSize - 0x100)
    (empty : ∀ address : Word, 0x859 ≤ address.toNat → vm.mem.ram address = 0) :
    let loaded := Patch.apply
      { ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
          (0x959 + BitVec.ofNat 16 i, byte.toBitVec) } vm
    (∀ address : Word, address.toNat < ramSize →
      loaded.mem.ram (0x859 + address) = (initialState program).vm.mem.ram address) ∧
    (∀ address : Word, address.toNat < 0x959 → loaded.mem.ram address = vm.mem.ram address) := by
  have space : (0x959#16).toNat + program.size ≤ 0x10000 := by
    change 0x959 + program.size ≤ 0x10000
    dsimp [ramSize] at fits
    omega
  dsimp only
  constructor
  · intro address bound
    have relocated : (0x859 + address).toNat = 0x859 + address.toNat := by
      dsimp [ramSize] at bound
      bv_omega
    rw [file_patch_ram program 0x959 (0x859 + address) vm space, ProgramProofs.Host.initial_ram_eq, relocated]
    have condition : 0x959 ≤ 0x859 + address.toNat ∧
        0x859 + address.toNat < 0x959 + program.size ↔
        0x100 ≤ address.toNat ∧ address.toNat - 0x100 < program.size := by omega
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, condition]
    split
    · exact congrArg (fun i : Nat => (program.data[i]! : UInt8).toBitVec) (by omega)
    · apply empty
      have := address.isLt
      dsimp [ramSize] at bound
      bv_omega
  · intro address bound
    rw [file_patch_ram program 0x959 address vm space, if_neg]
    change ¬ (0x959 ≤ address.toNat ∧ address.toNat < 0x959 + program.size)
    omega

end ProgramProofs.Uxnmin
