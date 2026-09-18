-- uxnmin.tal is a simulation refinement of Uxn.lean when
-- running programs which respect its more limited memory size and
-- don't use devices not supported by it.
import ProgramProofs.Uxnmin.InitialBoundary
import ProgramProofs.Uxnmin.Confinement
import ProgramProofs.Uxnmin.PopChunk
import ProgramProofs.Uxnmin.IncChunk
import ProgramProofs.Uxnmin.JumpChunk
import ProgramProofs.Uxnmin.TransferChunk
import ProgramProofs.Uxnmin.DeviceReadChunk
import ProgramProofs.Uxnmin.ArithmeticChunk
import ProgramProofs.Uxnmin.ComparisonChunk
import ProgramProofs.Uxnmin.ShiftChunk
import ProgramProofs.Uxnmin.DeviceReadChunkWord
import ProgramProofs.Uxnmin.ConditionalJumpChunk
import ProgramProofs.Uxnmin.SubroutineChunk
import ProgramProofs.Uxnmin.BrkChunk
import ProgramProofs.Uxnmin.LoadChunk
import ProgramProofs.Uxnmin.LoadBounds
import ProgramProofs.Uxnmin.StoreChunk
import ProgramProofs.Uxnmin.StoreBounds
import ProgramProofs.Uxnmin.DeviceWriteBlock
import ProgramProofs.Uxnmin.PermutationChunk
import ProgramProofs.Uxnmin.ImmediateChunk
import ProgramProofs.Uxnmin.ImmediateBounds
import ProgramProofs.Uxnmin.OpcodeCases

namespace ProgramProofs.Uxnmin.Proof
open Semantics
open Uxn Uxn.Host

-- If the self-hosted VM can load filename, and filename's contents
-- correspond to program, then the self-hosted VM takes some number of
-- steps, and from then on is a simulation refinement of Uxn.Host.
theorem correct (filename : String) (program : ByteArray)
    (before after : Void IO.RealWorld)
    (filenameFits : filename.utf8ByteSize < 0x40)
    (filenameNoNul : 0 ∉ filename.toUTF8.data)
    (programFits : program.size ≤ ramSize - 0x0100)
    (read : (do
      (← File.Handle.open filename).read (ramSize - 0x0100).toUSize) before = .ok program after) :
    let initial := Uxn.Host.initialState program
    let start : Configuration := .ok (.next initial.vm, initial) after
    Confined start → CompatibleDevices start →
    ∃ steps host, ∃ R : Configuration → Configuration → Prop,
      Uxn.Host.run rom [filename] (some steps) before = .ok (0, host) after ∧
      host.fuel = some 0 ∧
      R start (.ok (.next host.vm, host) after) ∧
      RankedSimulation next next label label R := by
  dsimp only
  intro confined compatible
  let start : Configuration := .ok (.next (initialState program).vm, initialState program) after
  apply correct_of_boundary filename program before after (Boundary start)
  · exact loaded_boundary filename program before after filenameFits filenameNoNul programFits read
  · intro direct concrete related
    cases related with
    | stopped directStopped concreteStopped agree =>
      refine ⟨concrete, .refl, agree, ?_⟩
      rw [directStopped, concreteStopped]
      exact .none
    | @evaluating guest outer guestHost outerHost world reachable core devices pointer loaderFrame runFrame =>
      have boundary : Boundary start (.ok (.next guest, guestHost) world) (.ok (.next outer, outerHost) world) :=
        .evaluating reachable core devices pointer loaderFrame runFrame
      have pcBound := confined.pc_lt guest guestHost world reachable
      have chunk {guest' first final : Uxn.State}
          (direct : next (.ok (.next guest, guestHost) world) = some (.ok (.next guest', guestHost) world))
          (native : next (.ok (.next outer, outerHost) world) = some (.ok (.next first, outerHost) world))
          (suffix : Relation.ReflTransGen
            (fun x y => next x = some y ∧ label (.ok (.next guest', guestHost) world) = label x)
            (.ok (.next first, outerHost) world) (.ok (.next final, outerHost) world))
          (represented : EvaluationBoundary guest' final)
          (memory : ∀ address, address = 0x199 ∨ address = 0x1a4 ∨
            (0x759 ≤ address.toNat ∧ address.toNat < 0x859) → final.mem.ram address = outer.mem.ram address)
          (returnPointer : final.mem.rstk.ptr = outer.mem.rstk.ptr)
          (frame : ∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
            final.mem.rstk.data index = outer.mem.rstk.data index) :
          ∃ last,
            Relation.ReflTransGen
              (fun x y => next x = some y ∧ label (.ok (.next guest, guestHost) world) = label x)
              (.ok (.next outer, outerHost) world) last ∧
            label (.ok (.next guest, guestHost) world) = label last ∧
            Option.Rel (fun d' c' => ∃ finish,
              Relation.ReflTransGen (fun x y => next x = some y ∧ label d' = label x) c' finish ∧
              Boundary start d' finish)
              (next (.ok (.next guest, guestHost) world)) (next last) := by
        refine ⟨.ok (.next outer, outerHost) world, .refl, rfl, ?_⟩
        rw [direct, native]
        exact .some ⟨.ok (.next final, outerHost) world, suffix,
          boundary.of_next direct represented memory returnPointer frame⟩
      have deviceAddress (address : Word)
          (preserved : address = 0x199 ∨ address = 0x1a4 ∨ (0x759 ≤ address.toNat ∧ address.toNat < 0x859)) :
          address.toNat < ramBase ∧ ¬ StackScratch address := by
        rcases preserved with rfl | rfl | bound
        · simp [ramBase, StackScratch, PopScratch]
        · simp [ramBase, StackScratch, PopScratch]
        · refine ⟨bound.2, ?_⟩
          simp only [StackScratch, PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
          bv_omega
      have stackMemory {final : Uxn.State}
          (memory : ∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) :
          ∀ address, address = 0x199 ∨ address = 0x1a4 ∨
            (0x759 ≤ address.toNat ∧ address.toNat < 0x859) → final.mem.ram address = outer.mem.ram address :=
        fun address preserved => memory address (deviceAddress address preserved).2
      by_cases brk : guest.mem.ram guest.pc = 0
      · obtain ⟨first, finalVM, finalHost, direct, native, suffix⟩ :=
          brk_chunk guestHost outerHost world core pcBound brk
            pointer loaderFrame runFrame
        refine ⟨.ok (.next outer, outerHost) world, .refl, rfl, ?_⟩
        rw [direct, native]
        exact .some ⟨.ok (.brk finalVM, finalHost) world, suffix, .stopped rfl rfl rfl⟩
      by_cases pop : guest.mem.ram guest.pc &&& 0x1f = 2
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          pop_chunk guestHost outerHost world core pcBound pop
        exact chunk direct native suffix represented
          (stackMemory fun address outside => memory address fun forbidden => outside (.inl forbidden)) pointer frame
      by_cases inc : guest.mem.ram guest.pc &&& 0x1f = 1
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          inc_chunk guestHost outerHost world core pcBound inc
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases jump : guest.mem.ram guest.pc &&& 0x1f = 12
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          jump_chunk guestHost outerHost world core pcBound jump
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases transfer : guest.mem.ram guest.pc &&& 0x1f = 15
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          transfer_chunk guestHost outerHost world core pcBound transfer
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases deviceRead : guest.mem.ram guest.pc &&& 0x1f = 0x16
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          if mode : (guest.mem.ram guest.pc).getLsbD 5 = true then
            device_read_word_chunk guestHost outerHost world core devices
              pcBound deviceRead mode
          else
            device_read_byte_chunk guestHost outerHost world core devices
              pcBound deviceRead (by simpa using mode)
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases arithmetic : ∃ operator : ArithmeticOp, guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode
      · obtain ⟨operator, opcode⟩ := arithmetic
        obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          arithmetic_chunk operator guestHost outerHost world core pcBound opcode
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases comparison : ∃ operator : ComparisonOp, guest.mem.ram guest.pc &&& 0x1f = operator.guestOpcode
      · obtain ⟨operator, opcode⟩ := comparison
        obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          comparison_chunk operator guestHost outerHost world core pcBound opcode
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases shift : guest.mem.ram guest.pc &&& 0x1f = 0x1f
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          shift_chunk guestHost outerHost world core pcBound shift
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases conditional : guest.mem.ram guest.pc &&& 0x1f = 13
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          conditional_jump_chunk guestHost outerHost world core pcBound conditional
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases subroutine : guest.mem.ram guest.pc &&& 0x1f = 14
      · obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          subroutine_chunk guestHost outerHost world core pcBound subroutine
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases load : ∃ kind : AddressMode, guest.mem.ram guest.pc &&& 0x1f = kind.loadOpcode
      · obtain ⟨kind, opcode⟩ := load
        obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          load_chunk kind guestHost outerHost world core pcBound opcode
            (by simpa using confined.load_address_lt kind guest guestHost world reachable opcode false (by simp))
            (by intro short
                simpa using confined.load_address_lt kind guest guestHost world reachable opcode true (fun _ => short))
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      by_cases store : ∃ kind : AddressMode, guest.mem.ram guest.pc &&& 0x1f = kind.storeOpcode
      · obtain ⟨kind, opcode⟩ := store
        obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          store_chunk kind guestHost outerHost world core pcBound opcode
            (by simpa using confined.store_address_lt kind guest guestHost world reachable opcode false (by simp))
            (by intro short
                simpa using confined.store_address_lt kind guest guestHost world reachable opcode true (fun _ => short))
        exact chunk direct native suffix represented
          (fun address preserved => memory address (deviceAddress address preserved).1
            (deviceAddress address preserved).2) pointer frame
      by_cases deviceWrite : guest.mem.ram guest.pc &&& 0x1f = 0x17
      · exact device_write_block compatible guestHost outerHost world reachable core devices
          pointer loaderFrame runFrame pcBound deviceWrite
      by_cases permutation : ∃ operator : StackOp, guest.mem.ram guest.pc &&& 0x1f = operator.opcode
      · obtain ⟨operator, opcode⟩ := permutation
        obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
          stack_chunk operator guestHost outerHost world core pcBound opcode
        exact chunk direct native suffix represented (stackMemory memory) pointer frame
      have base : guest.mem.ram guest.pc &&& 0x1f = 0 := by
        rcases low_opcode_cases (guest.mem.ram guest.pc) with
          opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode |
          opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode |
          opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode |
          opcode | opcode | opcode | opcode | opcode | opcode | opcode | opcode
        · exact opcode
        · exact (inc opcode).elim
        · exact (pop opcode).elim
        · exact (permutation ⟨.nip, opcode⟩).elim
        · exact (permutation ⟨.swp, opcode⟩).elim
        · exact (permutation ⟨.rot, opcode⟩).elim
        · exact (permutation ⟨.dup, opcode⟩).elim
        · exact (permutation ⟨.ovr, opcode⟩).elim
        · exact (comparison ⟨.equ, opcode⟩).elim
        · exact (comparison ⟨.neq, opcode⟩).elim
        · exact (comparison ⟨.gth, opcode⟩).elim
        · exact (comparison ⟨.lth, opcode⟩).elim
        · exact (jump opcode).elim
        · exact (conditional opcode).elim
        · exact (subroutine opcode).elim
        · exact (transfer opcode).elim
        · exact (load ⟨.zero, opcode⟩).elim
        · exact (store ⟨.zero, opcode⟩).elim
        · exact (load ⟨.relative, opcode⟩).elim
        · exact (store ⟨.relative, opcode⟩).elim
        · exact (load ⟨.absolute, opcode⟩).elim
        · exact (store ⟨.absolute, opcode⟩).elim
        · exact (deviceRead opcode).elim
        · exact (deviceWrite opcode).elim
        · exact (arithmetic ⟨.add, opcode⟩).elim
        · exact (arithmetic ⟨.sub, opcode⟩).elim
        · exact (arithmetic ⟨.mul, opcode⟩).elim
        · exact (arithmetic ⟨.div, opcode⟩).elim
        · exact (arithmetic ⟨.and, opcode⟩).elim
        · exact (arithmetic ⟨.ora, opcode⟩).elim
        · exact (arithmetic ⟨.eor, opcode⟩).elim
        · exact (shift opcode).elim
      obtain ⟨kind, opcode⟩ := immediate_of_zero_opcode (guest.mem.ram guest.pc) base brk
      obtain ⟨guest', first, final, direct, native, suffix, represented, memory, pointer, frame⟩ :=
        immediate_chunk kind guestHost outerHost world core pcBound opcode
          (fun second read => confined.immediate_address_lt kind guest guestHost world reachable opcode second read)
      exact chunk direct native suffix represented (stackMemory memory) pointer frame

end ProgramProofs.Uxnmin.Proof
