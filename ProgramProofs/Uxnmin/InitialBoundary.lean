import ProgramProofs.Uxnmin.Boundary
import ProgramProofs.Uxnmin.InitialImage
import ProgramProofs.Uxnmin.Startup

open private ProgramProofs.Uxnmin.writeName from ProgramProofs.Uxnmin.Loader.Filename
namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host

/-- The complete loader establishes the relation used by the instruction proof. -/
theorem loaded_boundary (filename : String) (program : ByteArray)
    (before after : Void IO.RealWorld)
    (filenameFits : filename.utf8ByteSize < 0x40)
    (filenameNoNul : 0 ∉ filename.toUTF8.data)
    (programFits : program.size ≤ ramSize - 0x100)
    (read : (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) before = .ok program after) :
    let initial := initialState program
    let start : Configuration := .ok (.next initial.vm, initial) after
    ∃ steps host,
      Uxn.Host.run rom [filename] (some steps) before = .ok (0, host) after ∧
      host.fuel = some 0 ∧ Boundary start start (.ok (.next host.vm, host) after) := by
  dsimp only
  obtain ⟨input, final, run, inputRAM, fuel, _, pc, _, memory, working, returning,
    frame0, frame1, frame2, frame3⟩ :=
    run_bootstrap filename program before after filenameFits filenameNoNul programFits read
  have length : filename.toUTF8.data.toList.length = filename.utf8ByteSize := rfl
  have nameFrame := (writeName_spec filename.toUTF8.data.toList 0
    (initialState rom).vm.mem.ram (by rw [length]; omega)).2
  have stable (address : Word) (outside : 0x40 ≤ address.toNat) (cursor : address ≠ 0x13e) :
      input.vm.mem.ram address = (initialState rom).vm.mem.ram address := by
    rw [inputRAM, Function.update_of_ne cursor]
    exact nameFrame address (.inr (by rw [length]; omega))
  have code : CodeImage input.vm.mem.ram := by
    intro address lower upper immutable
    rw [stable address (by omega) (by rintro rfl; exact immutable (.inl rfl))]
    exact initial_image.1 address lower upper immutable
  have empty (address : Word) (bound : 0x555 ≤ address.toNat) : input.vm.mem.ram address = 0 := by
    rw [stable address (by omega) (by bv_omega)]
    exact initial_image.2.1 address bound
  have represented := loaded_representation program input.vm final.vm programFits code empty memory
  obtain ⟨ports, consoleRead, consoleType⟩ := loaded_devices program input.vm final.vm programFits empty
    (by rw [stable _ (by decide) (by decide)]; exact initial_image.2.2.1)
    (by rw [stable _ (by decide) (by decide)]; exact initial_image.2.2.2) memory
  refine ⟨32 + 12 * filename.utf8ByteSize, final, run, fuel,
    .evaluating .refl ⟨represented, pc, working, ?_⟩
      ⟨ports, consoleRead, consoleType⟩ returning ?_ ?_⟩
  · rw [returning]
    decide
  · rw [frame0, frame1]
    rfl
  · rw [frame2, frame3]
    rfl

end ProgramProofs.Uxnmin
