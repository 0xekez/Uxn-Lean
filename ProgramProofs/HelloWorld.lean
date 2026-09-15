import ProgramProofs.Host.Host

set_option maxHeartbeats 1000000

namespace ProgramProofs.HelloWorld

open Uxn Uxn.Host ProgramProofs.Host

/-- The hello-world program with an arbitrary zero-terminated byte string. -/
def rom (s : List Byte) : ByteArray :=
  ⟨#[0xa0, 0x01, 0x12, 0x94, 0x06, 0x20, 0x00, 0x03,
     0x02, 0x22, 0x00, 0x80, 0x18, 0x17, 0x21, 0x40,
     0xff, 0xf1] ++ (s.map UInt8.ofBitVec).toArray ++ #[0]⟩

/-- The ROM prints the provided string. -/
theorem correct (s : List Byte)
    (hsize : s.length < 0xfeee) (hnoZero : 0 ∉ s) :
    ∃ final : Uxn.Host.State,
      Uxn.Host.run (rom s) =
        (do
          for byte in s do (← IO.getStdout).write ⟨#[UInt8.ofBitVec byte]⟩
          pure (0, final)) ∧
      final.vm.pc = 0x10b ∧ final.vm.mem.wstk.ptr = 0 := by
  generalize hram : (initialState (rom s)).vm.mem.ram = ram
  have codeImage : Code (rom []) 18 ram := by
    intro i
    have hi := i.isLt
    rw [← hram]
    rw [initial_ram_byte _ _ (by simp [← ByteArray.size_data, rom] <;> omega) (by omega)]
    unfold rom
    rw [getElem!_pos _ _ (by simp <;> omega), getElem!_pos _ _ (by simp <;> omega)]
    rw [Array.getElem_append_left (by simp <;> omega), Array.getElem_append_left (by exact hi)]
    rw [Array.getElem_append_left (by simp)]
    simp
  have code (address : Word) (hlo : 0x100#16 ≤ address) (hhi : address < 0x112#16) :
      ram address = (rom []).data[address.toNat - 0x100]!.toBitVec :=
    codeImage.read address hlo hhi
  have string (i : Nat) (hi : i < s.length) :
      ram (0x112 + BitVec.ofNat 16 i) = s[i] := by
    have address : 0x112 + BitVec.ofNat 16 i =
        0x100 + BitVec.ofNat 16 (18 + i) := by bv_omega
    rw [← hram]
    rw [address, initial_ram_byte _ _ (by simp [← ByteArray.size_data, rom] <;> omega) (by omega)]
    unfold rom
    rw [getElem!_pos _ _ (by simp <;> omega)]
    rw [Array.getElem_append_left (by simp <;> omega), Array.getElem_append_right (by simp)]
    simp
  have terminator : ram (0x112 + BitVec.ofNat 16 s.length) = 0 := by
    have address : 0x112 + BitVec.ofNat 16 s.length =
        0x100 + BitVec.ofNat 16 (18 + s.length) := by bv_omega
    rw [← hram]
    rw [address, initial_ram_byte _ _ (by simp [← ByteArray.size_data, rom] <;> omega) (by omega)]
    unfold rom
    rw [getElem!_pos _ _ (by simp <;> omega)]
    rw [Array.getElem_append_right (by simp <;> omega)]
    simp

  -- The return stack and RAM are unchanged. Only the two live pointer bytes
  -- are prescribed; arbitrary backing cells absorb the loop's discarded bytes.
  let machine (pc : Word) (ptr : Byte) (data : Byte → Byte) : Uxn.State :=
    ProgramProofs.Host.machine ram pc ⟨data, ptr⟩ Stack.empty
  let pointer (p : Word) (data : Byte → Byte) : Byte → Byte :=
    (Stack.pushWord ⟨data, 0⟩ p).data

  -- LDAk, DUP, JCI: read without consuming the pointer, duplicate the byte,
  -- and choose the cleanup path or the output path according to whether it is zero.
  have branch (p : Word) (data : Byte → Byte) (host : Uxn.Host.State)
      (hfuel : host.fuel = none) :
      evalLoop (.next (machine 0x103 2 (pointer p data))) host =
        evalLoop
          (.next (machine (if ram p = 0 then 0x108 else 0x10b) 3
            (Function.update (Function.update (pointer p data) 2 (ram p)) 3 (ram p)))) host := by
    by_cases hzero : ram p = 0#8 <;>
      (symbolic_steps 3 hfuel [machine, pointer, code, rom, hzero])
    all_goals simp [uxn_step, machine, pointer, hzero]

  -- POP, POP2, BRK: discard the zero byte and pointer, then stop at PC 0x10b.
  have stop (data : Byte → Byte) (host : Uxn.Host.State)
      (hfuel : host.fuel = none) :
      evalLoop (.next (machine 0x108 3 data)) host =
        pure ((), { host with vm := machine 0x10b 0 data }) := by
    symbolic_steps 3 hfuel [machine, pointer, code, rom]
    rw [evalLoop.eq_def]
    rfl

  -- LIT 0x18, DEO, INC2, JMI: emit one byte and return to LDAk with p + 1.
  have emit (p : Word) (data : Byte → Byte) (host : Uxn.Host.State)
      (hfuel : host.fuel = none) :
      ∃ data',
        evalLoop
            (.next (machine 0x10b 3
              (Function.update (Function.update (pointer p data) 2 (ram p)) 3 (ram p)))) host =
          (do
            writeStdout (ram p)
            evalLoop (.next (machine 0x103 2 (pointer (p + 1) data')))
              (host.write 0x18 (ram p))) := by
    refine ⟨Function.update (Function.update (pointer p data) 2 (ram p)) 3 0x18, ?_⟩
    symbolic_steps 4 hfuel [machine, pointer, code, rom, respond, deo_stdout, bind_assoc]
    simp [uxn_step, machine, pointer, State.write, writeStdout, bind_assoc]

  have next_address (p : Word) (i : Nat) :
      p + 1 + BitVec.ofNat 16 i = p + BitVec.ofNat 16 (i + 1) := by
    rw [BitVec.ofNat_add]
    change (p + 1) + BitVec.ofNat 16 i = p + (BitVec.ofNat 16 i + 1)
    rw [BitVec.add_assoc, BitVec.add_comm (1 : Word)]

  -- Generalize the pointer, backing stack, and host. Besides
  -- the result, preserve the host fields inspected after the initial evaluation.
  have loop (rest : List Byte) :
      ∀ (p : Word) (data : Byte → Byte) (host : Uxn.Host.State),
        (∀ i (hi : i < rest.length), ram (p + BitVec.ofNat 16 i) = rest[i]) →
        ram (p + BitVec.ofNat 16 rest.length) = 0 →
        0 ∉ rest → host.fuel = none →
        ∃ final,
          evalLoop (.next (machine 0x103 2 (pointer p data))) host =
            (do
              for byte in rest do writeStdout byte
              pure ((), final)) ∧
          final.vm.pc = 0x10b ∧ final.vm.mem.wstk.ptr = 0 ∧
          final.fuel = none ∧ final.consoleVector = host.consoleVector ∧
          final.read 0x0f = host.read 0x0f := by
    induction rest with
    | nil =>
      intro p data host _ hzero _ hfuel
      have hz : ram p = 0 := by simpa using hzero
      refine ⟨{ host with
        vm := machine 0x10b 0
          (Function.update (Function.update (pointer p data) 2 (ram p)) 3 (ram p)) }, ?_⟩
      refine ⟨?_, rfl, rfl, hfuel, rfl, rfl⟩
      rw [branch _ _ _ hfuel, if_pos hz, stop _ _ hfuel]
      simp
    | cons byte rest ih =>
      intro p data host hread hzero hnonzero hfuel
      have hb : ram p = byte :=
        (congrArg ram (BitVec.add_zero p)).symm.trans (hread 0 (by simp))
      simp only [List.mem_cons, not_or] at hnonzero
      have hn : ram p ≠ 0 := fun h => hnonzero.1 (hb.symm.trans h).symm
      obtain ⟨data', hstep⟩ := emit p data host hfuel
      obtain ⟨final, hrun, hpc, hptr, hf, hv, hh⟩ := ih (p + 1) data'
        (host.write 0x18 (ram p))
        (by
          intro i hi
          rw [next_address]
          exact hread (i + 1) (by simpa using hi))
        (by rw [next_address]; exact hzero)
        hnonzero.2
        hfuel
      refine ⟨final, ?_, hpc, hptr, hf, hv, ?_⟩
      · rw [branch _ _ _ hfuel, if_neg hn, hstep]
        rw [hrun, hb]
        simp only [List.forIn_cons, bind_assoc, pure_bind]
      · exact hh.trans (Vector.getElem_set_ne (xs := host.ports) (x := ram p)
          (i := 0x18) (j := 0x0f) (by decide) (by decide) (by decide))

  -- The initial LIT2 installs the string pointer. The host starts with a zero
  -- console vector and halt port, so it performs no input and returns zero.
  have start (host : Uxn.Host.State) (hfuel : host.fuel = none) :
      evalLoop (.next (machine 0x100 0 (fun _ => 0))) host =
        evalLoop
          (.next (machine 0x103 2 (pointer 0x112 (fun _ => 0)))) host := by
    symbolic_steps 1 hfuel [machine, code, rom]
    simp [uxn_step, machine, pointer]

  let host : Uxn.Host.State := { vm := machine 0 0 (fun _ => 0) }
  obtain ⟨final, hrun, hpc, hptr, hfuel, hvector, hhalt⟩ :=
    loop s 0x112 (fun _ => 0) host string terminator hnoZero rfl
  have hboot :
      evalLoop (.next (machine 0x100 0 (fun _ => 0))) host =
        (do
          for byte in s do writeStdout byte
          pure ((), final)) := by
    rw [start host rfl]
    exact hrun
  refine ⟨final, ?_, hpc, hptr⟩
  apply run_of_evalLoop (rom s) final _ ?_ hvector hhalt
  rw [← initial_shape (rom s), hram]
  exact hboot


-- Keep the concrete example tied to the verified code and string layout.
run_cmd do
  unless (← IO.FS.readBinFile
      ((System.FilePath.mk (← Lean.getFileName)).parent.get! /
        ".." / "examples" / "binaries" / "hello_world.rom")) ==
      rom ("Hello World!".toUTF8.data.toList.map UInt8.toBitVec) do
    throwError "Hello-world ROM differs from ProgramProofs.HelloWorld.rom"

end ProgramProofs.HelloWorld
