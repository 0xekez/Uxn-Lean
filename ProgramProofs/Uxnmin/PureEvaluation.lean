import ProgramProofs.Uxnmin.PopSimulation
import ProgramProofs.Uxnmin.IncSimulation
import ProgramProofs.Uxnmin.JumpSimulation
import ProgramProofs.Uxnmin.TransferSimulation
import ProgramProofs.Uxnmin.DeviceReadSimulation
import ProgramProofs.Uxnmin.DeviceReadSimulationWord
import ProgramProofs.Uxnmin.ArithmeticSimulation
import ProgramProofs.Uxnmin.ComparisonSimulation
import ProgramProofs.Uxnmin.ShiftSimulation
import ProgramProofs.Uxnmin.ConditionalJumpSimulation
import ProgramProofs.Uxnmin.SubroutineSimulation
import ProgramProofs.Uxnmin.LoadSimulation
import ProgramProofs.Uxnmin.StoreSimulation
import ProgramProofs.Uxnmin.PermutationSimulation
import ProgramProofs.Uxnmin.Compatible
import ProgramProofs.Uxnmin.LoadBounds
import ProgramProofs.Uxnmin.StoreBounds
import ProgramProofs.Uxnmin.ImmediateBounds
import ProgramProofs.Uxnmin.ImmediateSimulation
import ProgramProofs.Uxnmin.OpcodeCases

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

theorem pure_evaluation {start : Configuration} (confined : Confined start)
    (compatible : CompatibleDevices start) {invocation : Invocation}
    {guest outer : Uxn.Host.State} (world : Void IO.RealWorld)
    (reachable : Reachable start (.running guest world))
    (image : Evaluation invocation guest outer)
    (brk : guest.vm.mem.ram guest.vm.pc ≠ 0)
    (deviceWrite : guest.vm.mem.ram guest.vm.pc &&& 0x1f ≠ 0x17) :
    ∃ guestVM first final,
      Uxn.Host.step guest.vm guest = pure (.next guestVM, guest) ∧
      Uxn.step outer.vm = .done (.next first) ∧ Reaches first final ∧
      Evaluation invocation {guest with vm := guestVM} {outer with vm := final} := by
  have pcBound := confined.pc_lt guest world invocation.directReturn reachable image.guestControl
  have deviceAddress (address : Word) (preserved : DeviceAddress address) :
      address.toNat < ramBase ∧ ¬ StackScratch address := by
    rcases preserved with special | bound
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at special
      rcases special with rfl | rfl | rfl | rfl <;> simp [ramBase, StackScratch, PopScratch]
    · refine ⟨bound.2, ?_⟩
      simp only [StackScratch, PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
      bv_omega
  have finish {guestVM first final : Uxn.State}
      (direct : Uxn.Host.step guest.vm guest = pure (.next guestVM, guest))
      (native : Uxn.step outer.vm = .done (.next first)) (suffix : Reaches first final)
      (core : EvaluationBoundary guestVM final)
      (memory : ∀ address, DeviceAddress address → final.mem.ram address = outer.vm.mem.ram address)
      (pointer : final.mem.rstk.ptr = outer.vm.mem.rstk.ptr)
      (frame : ∀ index : Byte, index.toNat < outer.vm.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.vm.mem.rstk.data index) :
    ∃ guestVM first final,
      Uxn.Host.step guest.vm guest = pure (.next guestVM, guest) ∧
      Uxn.step outer.vm = .done (.next first) ∧ Reaches first final ∧
      Evaluation invocation {guest with vm := guestVM} {outer with vm := final} :=
    ⟨guestVM, first, final, direct, native, suffix, image.of_pure core memory pointer frame⟩
  have stackMemory {final : Uxn.State}
      (memory : ∀ address, ¬ StackScratch address → final.mem.ram address = outer.vm.mem.ram address) :
      ∀ address, DeviceAddress address → final.mem.ram address = outer.vm.mem.ram address :=
    fun address preserved => memory address (deviceAddress address preserved).2
  have from_steps {guestVM final : Uxn.State}
      (direct : Uxn.Host.step guest.vm guest = pure (.next guestVM, guest))
      (steps : Reaches outer.vm final) (different : outer.vm ≠ final)
      (core : EvaluationBoundary guestVM final)
      (memory : ∀ address, DeviceAddress address → final.mem.ram address = outer.vm.mem.ram address)
      (pointer : final.mem.rstk.ptr = outer.vm.mem.rstk.ptr)
      (frame : ∀ index : Byte, index.toNat < outer.vm.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.vm.mem.rstk.data index) :
    ∃ guestVM first final,
      Uxn.Host.step guest.vm guest = pure (.next guestVM, guest) ∧
      Uxn.step outer.vm = .done (.next first) ∧ Reaches first final ∧
      Evaluation invocation {guest with vm := guestVM} {outer with vm := final} := by
    cases steps with
    | refl => exact (different rfl).elim
    | next native suffix => exact finish direct native suffix core memory pointer frame
  have guest_step {vm : Uxn.State} (step : Uxn.step guest.vm = .done (.next vm)) :
      Uxn.Host.step guest.vm guest = pure (.next vm, guest) := by
    simp only [Uxn.Host.step, step, uxn_state]
  by_cases pop : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 2
  · obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      pop_simulation image.core pcBound pop
    exact from_steps (guest_step direct) steps different core (stackMemory fun address outside => memory address fun forbidden => outside (.inl forbidden)) pointer frame
  by_cases inc : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 1
  · obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      inc_simulation image.core pcBound inc
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  by_cases jump : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 12
  · obtain ⟨guestVM, first, final, direct, native, suffix, core, memory, pointer, frame⟩ :=
      jump_simulation image.core pcBound jump
    exact finish (guest_step direct) native suffix core (stackMemory memory) pointer frame
  by_cases transfer : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 15
  · obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      transfer_simulation image.core pcBound transfer
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  by_cases deviceRead : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 0x16
  · obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      if mode : (guest.vm.mem.ram guest.vm.pc).getLsbD 5 = true then
        device_read_word_simulation guest image.core image.devices pcBound deviceRead mode
          (compatible.read_word guest world invocation.directReturn reachable image.guestControl deviceRead mode).1
          (compatible.read_word guest world invocation.directReturn reachable image.guestControl deviceRead mode).2
      else
        device_read_byte_simulation guest image.core image.devices pcBound deviceRead (by simpa using mode)
    exact from_steps direct steps different core (stackMemory memory) pointer frame
  by_cases arithmetic : ∃ operator : ArithmeticOp, guest.vm.mem.ram guest.vm.pc &&& 0x1f = operator.guestOpcode
  · obtain ⟨operator, opcode⟩ := arithmetic
    obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      arithmetic_simulation operator image.core pcBound opcode
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  by_cases comparison : ∃ operator : ComparisonOp, guest.vm.mem.ram guest.vm.pc &&& 0x1f = operator.guestOpcode
  · obtain ⟨operator, opcode⟩ := comparison
    obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      comparison_simulation operator image.core pcBound opcode
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  by_cases shift : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 0x1f
  · obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      shift_simulation image.core pcBound shift
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  by_cases conditional : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 13
  · obtain ⟨guestVM, first, final, direct, native, suffix, core, memory, pointer, frame⟩ :=
      conditional_jump_simulation image.core pcBound conditional
    exact finish (guest_step direct) native suffix core (stackMemory memory) pointer frame
  by_cases subroutine : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 14
  · obtain ⟨guestVM, first, final, direct, native, suffix, core, memory, pointer, frame⟩ :=
      subroutine_simulation image.core pcBound subroutine
    exact finish (guest_step direct) native suffix core (stackMemory memory) pointer frame
  by_cases load : ∃ kind : AddressMode, guest.vm.mem.ram guest.vm.pc &&& 0x1f = kind.loadOpcode
  · obtain ⟨kind, opcode⟩ := load
    obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      load_simulation kind image.core pcBound opcode
        (by simpa [ramSize] using confined.load_address_lt kind guest.vm guest world invocation.directReturn
              reachable image.guestControl opcode false (by simp))
        (by intro short; simpa [ramSize] using confined.load_address_lt kind guest.vm guest world invocation.directReturn
              reachable image.guestControl opcode true (fun _ => short))
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  by_cases store : ∃ kind : AddressMode, guest.vm.mem.ram guest.vm.pc &&& 0x1f = kind.storeOpcode
  · obtain ⟨kind, opcode⟩ := store
    obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      store_simulation kind image.core pcBound opcode
        (by simpa [ramSize] using confined.store_address_lt kind guest.vm guest world invocation.directReturn
              reachable image.guestControl opcode false (by simp))
        (by intro short; simpa [ramSize] using confined.store_address_lt kind guest.vm guest world invocation.directReturn
              reachable image.guestControl opcode true (fun _ => short))
    exact from_steps (guest_step direct) steps different core (fun address preserved => memory address (deviceAddress address preserved).1 (deviceAddress address preserved).2) pointer frame
  by_cases permutation : ∃ operator : StackOp, guest.vm.mem.ram guest.vm.pc &&& 0x1f = operator.opcode
  · obtain ⟨operator, opcode⟩ := permutation
    obtain ⟨guestVM, final, direct, steps, core, different, memory, pointer, frame⟩ :=
      stack_simulation operator image.core pcBound opcode
    exact from_steps (guest_step direct) steps different core (stackMemory memory) pointer frame
  have base : guest.vm.mem.ram guest.vm.pc &&& 0x1f = 0 := by
    rcases low_opcode_cases (guest.vm.mem.ram guest.vm.pc) with
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
  obtain ⟨kind, opcode⟩ := immediate_of_zero_opcode (guest.vm.mem.ram guest.vm.pc) base brk
  obtain ⟨first, final, native, suffix, core, memory, pointer, frame⟩ :=
    immediate_simulation kind image.core pcBound opcode
      (fun second read => confined.immediate_address_lt kind guest.vm guest world invocation.directReturn
        image.guestControl reachable opcode second read)
  exact finish (guest_step (guest_immediate kind guest.vm opcode)) native suffix core (stackMemory memory) pointer frame

end ProgramProofs.Uxnmin.Model
