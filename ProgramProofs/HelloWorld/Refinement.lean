import ProgramProofs.HelloWorld
import ProgramProofs.Uxnmin.Correctness

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.HelloWorld
open Uxn Uxn.Host ProgramProofs.Host ProgramProofs.Uxnmin

/-- Hello World stays within uxnmin's guest RAM and uses only supported devices.
The bound includes the terminating NUL; the string itself may contain NUL bytes. -/
theorem refinement_conditions (s : List Byte) (size : 0x112 + s.length < ramSize)
    (world : Void IO.RealWorld) :
    Confined (.running (initialState (rom s)) world) ∧
      CompatibleDevices (.running (initialState (rom s)) world) := by
  let pointer (vm : Uxn.State) : Word := vm.mem.wstk.data 0#8 ++ vm.mem.wstk.data 1#8

  -- Instruction boundaries constrain only the live working-stack bytes.
  let Shape (limit : Nat) (vm : Uxn.State) : Prop :=
    match vm.pc with
    | 0x100 => vm.mem.wstk.ptr = 0#8
    | 0x103 => vm.mem.wstk.ptr = 2#8 ∧ (pointer vm).toNat ≤ limit
    | 0x104 => vm.mem.wstk.ptr = 3#8 ∧ (pointer vm).toNat ≤ limit ∧
        vm.mem.wstk.data 2#8 = vm.mem.ram (pointer vm)
    | 0x105 => vm.mem.wstk.ptr = 4#8 ∧ (pointer vm).toNat ≤ limit ∧
        vm.mem.wstk.data 2#8 = vm.mem.ram (pointer vm) ∧
        vm.mem.wstk.data 3#8 = vm.mem.wstk.data 2#8
    | 0x108 => vm.mem.wstk.ptr = 3#8
    | 0x109 => vm.mem.wstk.ptr = 2#8
    | 0x10a => vm.mem.wstk.ptr = 0#8
    | 0x10b => vm.mem.wstk.ptr = 3#8 ∧ (pointer vm).toNat < limit
    | 0x10d => vm.mem.wstk.ptr = 4#8 ∧ (pointer vm).toNat < limit ∧ vm.mem.wstk.data 3#8 = 0x18#8
    | 0x10e => vm.mem.wstk.ptr = 2#8 ∧ (pointer vm).toNat < limit
    | 0x10f => vm.mem.wstk.ptr = 2#8 ∧ (pointer vm).toNat ≤ limit
    | _ => False

  let Invariant (limit : Nat) (state : Uxn.Host.State) : Prop :=
    Code (rom []) 18 state.vm.mem.ram ∧
    state.vm.mem.ram (BitVec.ofNat 16 limit) = 0 ∧ state.consoleVector = 0 ∧
    (state.control = .console .done ∨
      state.control = .evaluating (.arguments []) ∧ Shape limit state.vm)

  let Valid (limit : Nat) : Configuration → Prop
    | .running state _ => Invariant limit state
    | .failed _ _ => True
    | .starting _ _ => False

  have preserved (limit : Nat) (bound : 0x112 ≤ limit ∧ limit < ramSize)
      (state : Uxn.Host.State) (valid : Invariant limit state)
      (world : Void IO.RealWorld) (next : Configuration)
      (step : Configuration.next (.running state world) = some next) : Valid limit next := by
    rcases valid with ⟨image, terminator, vector, done | ⟨control, shape⟩⟩
    · simp [Configuration.next, State.next, done] at step
    have code (address : Word) (lo : 0x100 ≤ address.toNat) (hi : address.toNat < 0x112) :
        state.vm.mem.ram address = (rom []).data[address.toNat - 0x100]!.toBitVec :=
      image.read address lo hi
    have pure_step (updated : Uxn.Host.State) (hstep : state.next = some (pure updated))
        (hvalid : Invariant limit updated) : Valid limit next := by
      have equality : Configuration.running updated world = next := by
        rw [Configuration.next, hstep] at step
        exact Option.some.inj step
      subst next
      exact hvalid
    unfold Shape at shape
    split at shape
    all_goals try contradiction
    all_goals rename_i pc
    case h_4 =>
      -- JCI reaches the output path only strictly before the terminator.
      have ptr := shape.1
      have byte := shape.2.2.1
      have dup := shape.2.2.2
      by_cases zero : state.vm.mem.ram (pointer state.vm) = 0#8
      · apply pure_step
        · simp [BitVec.ofNat_eq_ofNat, State.next, control, Uxn.Host.step,
            uxn_state, uxn_step, pc, code, rom, ptr, dup, byte, vector, zero]
          rfl
        · simp [BitVec.ofNat_eq_ofNat, Invariant, Shape, image, terminator]
      · have inside : (pointer state.vm).toNat < limit := by
          have ne : (pointer state.vm).toNat ≠ limit := by
            intro eq
            have same : pointer state.vm = BitVec.ofNat 16 limit := by
              apply BitVec.eq_of_toNat_eq
              simp [← eq]
            exact zero (same ▸ terminator)
          omega
        apply pure_step
        · simp [BitVec.ofNat_eq_ofNat, State.next, control, Uxn.Host.step,
            uxn_state, uxn_step, pc, code, rom, ptr, dup, byte, vector, zero]
          rfl
        · simpa [BitVec.ofNat_eq_ofNat, Invariant, Shape, pointer, image, terminator, vector, control] using inside
    case h_9 =>
      -- DEO writes stdout; either its updated state or its IO error is valid.
      obtain ⟨updated, action, invariant⟩ : ∃ updated,
          state.next = some (do writeStdout (state.vm.mem.wstk.data 2#8); pure updated) ∧
          Invariant limit updated := by
        simp [BitVec.ofNat_eq_ofNat, State.next, control, Uxn.Host.step, uxn_state, uxn_step, pc, code, rom,
          shape.1, shape.2.2, respond, deo_stdout, bind_assoc, Patch.apply]
        refine ⟨_, rfl, ?_⟩
        simpa [BitVec.ofNat_eq_ofNat, Invariant, Shape, pointer, image, terminator, vector, control, State.write]
          using shape.2.1
      rw [Configuration.next, action] at step
      change some (Configuration.ofResult
        (EST.bind (writeStdout (state.vm.mem.wstk.data 2#8))
          (fun _ => EST.pure updated) world)) = some next at step
      rw [EST.bind.eq_def] at step
      generalize effect : writeStdout (state.vm.mem.wstk.data 2#8) world = result at step
      cases result with
      | ok result later =>
        have equality : Configuration.running updated later = next := Option.some.inj step
        subst next
        exact invariant
      | error error later =>
        have equality : Configuration.failed error later = next := Option.some.inj step
        subst next
        trivial
    all_goals apply pure_step
    all_goals try
      simp [BitVec.ofNat_eq_ofNat, State.next, control, Uxn.Host.step,
        uxn_state, uxn_step, pc, code, rom, shape, vector]
      rfl
    all_goals try dsimp only [pointer] at shape
    all_goals try simp [BitVec.ofNat_eq_ofNat, Invariant, Shape, pointer, image, terminator, bound.1, shape]
    all_goals try
      simp only [append_split]
      have := shape.2
      dsimp only [ramSize] at bound
      bv_omega

  have reachable_invariant (config : Configuration)
      (reachable : Reachable (.running (initialState (rom s)) world) config) :
      Valid (0x112 + s.length) config := by
    induction reachable with
    | refl =>
      refine ⟨rom_code s, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
      · generalize hram : (initialState (rom s)).vm.mem.ram = ram
        have terminator := rom_terminator s (by dsimp [ramSize] at size; omega)
        rw [hram] at terminator
        simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using terminator
      all_goals rw [← initial_shape (rom s)]
      all_goals rfl
    | @tail before after path step ih =>
      cases before with
      | starting => exact False.elim ih
      | failed => simp [Configuration.next] at step
      | running state later =>
        exact preserved _ ⟨by omega, size⟩ state ih later after step
  constructor
  -- All RAM reads stay below ramSize; stdout does not inspect RAM.
  · intro state later
    dsimp only
    intro reachable outside
    rcases reachable_invariant _ reachable with ⟨image, _, vector, done | ⟨control, shape⟩⟩
    · simp [replaceOutside, Configuration.next, State.next, done]
    have code (address : Word) (lo : 0x100 ≤ address.toNat) (hi : address.toNat < 0x112) :
        state.vm.mem.ram address = (rom []).data[address.toNat - 0x100]!.toBitVec :=
      image.read address lo hi
    unfold Shape at shape
    split at shape
    all_goals try contradiction
    all_goals rename_i pc
    case h_2 =>
      have inside : (pointer state.vm).toNat < ramSize := Nat.lt_of_le_of_lt shape.2 size
      simp [BitVec.ofNat_eq_ofNat, replaceOutside, Configuration.next, State.next, control, Uxn.Host.step,
        uxn_state, uxn_step, pc, code, rom, shape.1, pointer, ramSize] at inside ⊢
      simp only [inside, if_true]
      rfl
    case h_4 =>
      by_cases zero : state.vm.mem.wstk.data 3#8 = 0#8 <;>
        simp [BitVec.ofNat_eq_ofNat, replaceOutside, Configuration.next, State.next, control, Uxn.Host.step,
          uxn_state, uxn_step, pc, code, rom, shape.1, zero, ramSize]
      all_goals rfl
    case h_9 =>
      simp [BitVec.ofNat_eq_ofNat, replaceOutside, Configuration.next, State.next, control, Uxn.Host.step,
        uxn_state, uxn_step, pc, code, rom, shape.1, shape.2.2, ramSize,
        respond, deo_stdout, Patch.apply, bind_assoc]
      have apply_output (f : Unit → Uxn.Host.State) :
          (f <$> writeStdout (state.vm.mem.wstk.data 2#8)) later =
            match writeStdout (state.vm.mem.wstk.data 2#8) later with
            | .ok result later => .ok (f result) later
            | .error error later => .error error later := by
        change EST.bind _ _ later = _
        rw [EST.bind.eq_def]
        cases writeStdout (state.vm.mem.wstk.data 2#8) later <;> rfl
      rw [apply_output, apply_output]
      cases writeStdout (state.vm.mem.wstk.data 2#8) later <;>
        simp [Configuration.ofResult, State.write, control]
    all_goals simp [BitVec.ofNat_eq_ofNat, replaceOutside, Configuration.next, State.next, control, Uxn.Host.step,
      uxn_state, uxn_step, pc, code, rom, shape, vector, ramSize]
    all_goals rfl

  · intro state later after reachable evaluating
    rcases reachable_invariant _ reachable with ⟨image, _, _, done | ⟨control, shape⟩⟩
    · simp [evaluating] at done
    have code (address : Word) (lo : 0x100 ≤ address.toNat) (hi : address.toNat < 0x112) :
        state.vm.mem.ram address = (rom []).data[address.toNat - 0x100]!.toBitVec :=
      image.read address lo hi
    unfold Shape at shape
    split at shape
    all_goals try contradiction
    all_goals rename_i pc
    case h_4 =>
      by_cases zero : state.vm.mem.wstk.data 3#8 = 0#8 <;>
        simp [uxn_state, uxn_step, pc, code, rom, shape.1, zero]
    case h_9 =>
      simp [uxn_state, uxn_step, pc, code, rom, shape.1, shape.2.2, Port.File.ports]
      change ¬ (0xa0#8 ≤ 0x18#8 ∧ 0x18#8 < 0xc0#8)
      decide
    all_goals simp [uxn_state, uxn_step, pc, code, rom, shape]

/-- The same conditions hold from the file-loading state used by `Uxnmin.correct`. -/
theorem refinement_conditions_file (s : List Byte) (size : 0x112 + s.length < ramSize)
    (filename : String) (before world : Void IO.RealWorld)
    (loaded : Uxn.Host.file filename [] before = .ok (initialState (rom s)) world) :
    Confined (.starting (Uxn.Host.file filename) before) ∧
      CompatibleDevices (.starting (Uxn.Host.file filename) before) := by
  have suffix (state : Uxn.Host.State) (later : Void IO.RealWorld)
      (reachable : Reachable (.starting (Uxn.Host.file filename) before) (.running state later)) :
      Reachable (.running (initialState (rom s)) world) (.running state later) := by
    rcases reachable.cases_head with equality | ⟨config, step, rest⟩
    · cases equality
    · have equality : Configuration.running (initialState (rom s)) world = config := by
        simpa [Configuration.next, Configuration.ofResult, loaded] using step
      subst config
      exact rest
  obtain ⟨confined, compatible⟩ := refinement_conditions s size world
  exact ⟨fun state later reachable => confined state later (suffix state later reachable),
    fun state later after reachable => compatible state later after (suffix state later reachable)⟩

/-- Apply uxnmin refinement to a Hello World ROM loaded from a file. -/
theorem refines (s : List Byte) (size : 0x112 + s.length < ramSize)
    (filename : String) (before world : Void IO.RealWorld)
    (filenameFits : filename.utf8ByteSize < 0x40)
    (filenameNoNul : 0 ∉ filename.toUTF8.data)
    (loadable : Loadable filename before)
    (loaded : Uxn.Host.file filename [] before = .ok (initialState (rom s)) world) :
    let direct := Configuration.starting (Uxn.Host.file filename) before
    ∃ R, R direct (.running (initialState Uxnmin.rom [filename]) before) ∧
      Uxnmin.RankedSimulation R := by
  obtain ⟨confined, compatible⟩ := refinement_conditions_file s size filename before world loaded
  exact Uxnmin.correct filename before filenameFits filenameNoNul loadable confined compatible

/-- The checked-in Hello World ROM is a concrete, nonempty example. -/
theorem hello_world_refinement_conditions (world : Void IO.RealWorld) :
    let program := rom ("Hello World!".toUTF8.data.toList.map UInt8.toBitVec)
    Confined (.running (initialState program) world) ∧
      CompatibleDevices (.running (initialState program) world) :=
  refinement_conditions _ (by decide) world

end ProgramProofs.HelloWorld
