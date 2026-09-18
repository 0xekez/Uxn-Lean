import ProgramProofs.Uxnmin.DeviceReadSimulation
import ProgramProofs.Uxnmin.Simulation

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn ProgramProofs.Host

/-- Byte-mode DEI is a silent native chunk even though its direct instruction
uses a host read request. -/
theorem device_read_byte_chunk {guest outer : Uxn.State}
    (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (boundary : EvaluationBoundary guest outer) (devices : DeviceImage guestHost outer)
    (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x16)
    (byteMode : (guest.mem.ram guest.pc).getLsbD 5 = false) :
    ∃ guest' first final,
      next (.ok (.next guest, guestHost) world) = some (.ok (.next guest', guestHost) world) ∧
      next (.ok (.next outer, outerHost) world) = some (.ok (.next first, outerHost) world) ∧
      Relation.ReflTransGen
        (fun x y => next x = some y ∧ label (.ok (.next guest', guestHost) world) = label x)
        (.ok (.next first, outerHost) world) (.ok (.next final, outerHost) world) ∧
      EvaluationBoundary guest' final ∧
      (∀ address, ¬ StackScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨guest', final, guestStep, steps, related, different, memory, pointer, frame⟩ :=
    device_read_byte_simulation guestHost boundary devices confined opcode byteMode
  cases steps with
  | refl => exact (different rfl).elim
  | @next _ first _ native rest =>
    refine ⟨guest', first, final, ?_, ?_, reaches_chunk rest outerHost world, related, memory, pointer, frame⟩
    · simp only [next, guestStep]
      rfl
    · simp only [next, Uxn.Host.step, native]
      rfl

end ProgramProofs.Uxnmin
