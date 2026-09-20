import ProgramProofs.Uxnmin.Loader.Ready
import ProgramProofs.Uxnmin.Loader.FileInstruction
import ProgramProofs.Uxnmin.Loader.AfterFile
import ProgramProofs.Uxnmin.InitialImage

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.NameBytes
open private Uxn.Host.fileName from Uxn.Host
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem initial_read (program : ByteArray) (port : Byte) : (initialState program).read port = 0 := by
  simp [initialState, Uxn.Host.State.read, Uxn.Host.State.write, Vector.get]

theorem loaded_evaluation (filename : String) (program : ByteArray) (input final : Uxn.Host.State)
    (filenameFits : filename.utf8ByteSize < 0x40) (programFits : program.size ≤ ramSize - 0x100)
    (inputRAM : input.vm.mem.ram = Function.update
      (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram)
      0x13e (BitVec.ofNat 8 filename.utf8ByteSize))
    (control : final.control = .evaluating (.console .input)) (halt : final.read 0x0f = 0)
    (pc : final.vm.pc = 0x16d) (vector : final.consoleVector = 0)
    (memory : final.vm.mem.ram = Function.update (Function.update
      (Patch.apply {ramWrites := program.data.toList.zipIdx.map fun (byte, i) =>
        (0x959 + BitVec.ofNat 16 i, byte.toBitVec)} input.vm).mem.ram 0x45 1) 0x46 0)
    (working : final.vm.mem.wstk.ptr = 0) (returning : final.vm.mem.rstk.ptr = 4)
    (frame0 : final.vm.mem.rstk.data 0 = 1) (frame1 : final.vm.mem.rstk.data 1 = 0x39)
    (frame2 : final.vm.mem.rstk.data 2 = 1) (frame3 : final.vm.mem.rstk.data 3 = 0x54) :
    Evaluation .reset (initialState program) final := by
  have initial := initial_image
  have length : filename.toUTF8.data.toList.length = filename.utf8ByteSize := rfl
  have nameFrame := (writeName_spec filename.toUTF8.data.toList 0 (initialState rom).vm.mem.ram
    (by rw [length]; omega)).2
  have stable (address : Word) (outside : 0x40 ≤ address.toNat) (cursor : address ≠ 0x13e) :
      input.vm.mem.ram address = (initialState rom).vm.mem.ram address := by
    rw [inputRAM, Function.update_of_ne cursor]
    exact nameFrame address (.inr (by rw [length]; omega))
  have code : CodeImage input.vm.mem.ram := by
    intro address lower upper immutable
    rw [stable address (by omega) (by rintro rfl; exact immutable (.inl rfl))]
    exact initial.1 address lower upper immutable
  have empty (address : Word) (bound : 0x555 ≤ address.toNat) : input.vm.mem.ram address = 0 := by
    rw [stable address (by omega) (by bv_omega)]
    exact initial.2.1 address bound
  have represented := loaded_representation program input.vm final.vm programFits code empty memory
  obtain ⟨ports, consoleRead, consoleType⟩ := loaded_devices program input.vm final.vm programFits empty
    (by rw [stable _ (by decide) (by decide)]; exact initial.2.2.1)
    (by rw [stable _ (by decide) (by decide)]; exact initial.2.2.2) memory
  have before := (file_patch_loads_guest program input.vm programFits
    (fun address bound => empty address (by omega))).2
  simp only [BitVec.ofNat_eq_ofNat] at before
  have cacheZero (ram : Word → Byte) (code : Code rom rom.size ram) : ram 0x175#16 = 0#8 ∧ ram 0x176#16 = 0#8 :=
    ⟨code ⟨0x75, by decide⟩, code ⟨0x76, by decide⟩⟩
  have zeroVector (address : Word) (chosen : address = 0x175 ∨ address = 0x176) : final.vm.mem.ram address = 0 := by
    rw [memory]
    rcases chosen with rfl | rfl
    all_goals simp only [BitVec.ofNat_eq_ofNat]
    all_goals rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), before _ (by decide),
      stable _ (by decide) (by decide)]
    · exact (cacheZero _ (Code.initial rom rom.size (Nat.le_refl _) (by decide))).1
    · exact (cacheZero _ (Code.initial rom rom.size (Nat.le_refl _) (by decide))).2
  refine ⟨⟨represented, pc, working, by rw [returning]; decide⟩,
    ⟨fun port _ _ => ports port, consoleRead, consoleType, ?_⟩, ?_, rfl, control, vector, returning, ?_, ?_⟩
  · rw [zeroVector _ (.inl rfl), zeroVector _ (.inr rfl)]
    rfl
  · exact halt.trans (initial_read program _).symm
  · rw [frame0, frame1]
    rfl
  · intro _
    rw [frame2, frame3]
    rfl

/-- Match direct loading at the file action, with pure setup on either side of it. -/
theorem loading_block (filename : String) (world : Void IO.RealWorld)
    (fits : filename.utf8ByteSize < 0x40) (noNul : 0 ∉ filename.toUTF8.data)
    (loadable : Loadable filename world) :
    Block (Boundary filename world) (.starting (Uxn.Host.file filename) world)
      (.running (initialState rom [filename]) world) := by
  cases read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) world with
  | error error after => simp [Loadable, read] at loadable
  | ok program after =>
    obtain ⟨programFits, direct⟩ : program.size ≤ ramSize - 0x100 ∧
        Uxn.Host.file filename [] world = .ok (initialState program) after := by
      simpa only [Loadable, read] using loadable
    obtain ⟨ready, startup, readyControl, readyHalt, pc, name, length, handle, readyRAM, wp, rp, high, low, port⟩ :=
      loader_ready filename fits noNul
    have code : Code rom rom.size (ProgramProofs.Uxnmin.writeName filename.toUTF8.data.toList 0
        (initialState rom).vm.mem.ram) :=
      writeName_code _ _ _ (by simpa using fits) (Code.initial rom rom.size (Nat.le_refl _) (by decide))
    have zero : (initialState rom).vm.mem.ram (BitVec.ofNat 16 filename.utf8ByteSize) = 0 := by
      rw [initial_ram_eq]
      have small : (BitVec.ofNat 16 filename.utf8ByteSize).toNat < 0x100 := by bv_omega
      rw [if_neg (by omega)]
    have decode : Uxn.Host.fileName ready.vm.mem 0 = some filename := by
      have name := (filename_memory filename (initialState rom).vm.mem.ram ready.vm.mem.wstk ready.vm.mem.rstk fits noNul zero).2
      simpa only [Uxn.Host.fileName, readyRAM] using name
    have instruction : ready.vm.mem.ram 0x135 = 0x37 := by
      rw [readyRAM]
      simp only [BitVec.ofNat_eq_ofNat]
      rw [Function.update_of_ne (by decide : 0x135#16 ≠ 0x13e#16)]
      exact code ⟨53, by decide⟩
    obtain ⟨loaded, step, loadedControl, loadedHalt, _, loadedVM⟩ :=
      loader_file ready filename program world after readyControl pc instruction wp high low port name length handle decode read
    obtain ⟨final, boot, finalControl, finalHalt, finalPC, finalVector, memory, working, returning,
      frame0, frame1, frame2, frame3⟩ := loader_after_file _ code _ ready loaded program programFits readyRAM rp loadedControl loadedVM
    refine ⟨.running ready world, startup.silent world _ rfl, ?_, ?_⟩
    · exact (label_evaluating ready _ readyControl world).symm
    · rw [Configuration.next, direct, step]
      apply Option.Rel.some
      refine ⟨.running final after, boot.silent after _ (label_evaluating _ _ rfl after),
        .evaluating .reset (.single ?_) ?_⟩
      · simp only [Configuration.next, direct]
        rfl
      · exact loaded_evaluation filename program ready final fits programFits readyRAM finalControl
          (finalHalt.trans (loadedHalt.trans readyHalt)) finalPC finalVector memory working returning frame0 frame1 frame2 frame3

end ProgramProofs.Uxnmin.Model
