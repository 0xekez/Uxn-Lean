import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.Return
import ProgramProofs.Uxnmin.RepresentationPC

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Guest BRK leaves the native evaluation loop at its return instruction. -/
theorem brk_prefix {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = 0#8) :
    ∃ first final, Uxn.step outer = .done (.next first) ∧ Reaches first final ∧
      final.pc = 0x173 ∧ final.mem.wstk.ptr = 0 ∧
      Represents { guest with pc := guest.pc + 1 } final ∧
      (∀ address, ¬ PopScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, cursor, pc, headerMemory⟩ :=
    instruction_header boundary confined
  obtain ⟨first, firstStep, suffix⟩ := header_progress boundary.toRepresents rep headerRun
  have tableHigh : outer.mem.ram 0x515#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x516#16 = 0x53#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have dispatchPC : dispatched.pc = 0x353 := by simpa [opcode, tableHigh, tableLow] using pc
  have code353 : dispatched.mem.ram 0x353#16 = 0x06#8 := rep.code _ (by decide) (by decide) (by simp [MutableCode])
  have code354 : dispatched.mem.ram 0x354#16 = 0x20#8 := rep.code _ (by decide) (by decide) (by simp [MutableCode])
  have code357 : dispatched.mem.ram 0x357#16 = 0x6c#8 := rep.code _ (by decide) (by decide) (by simp [MutableCode])
  have code170 : dispatched.mem.ram 0x170#16 = 0x20#8 := rep.code _ (by decide) (by decide) (by simp [MutableCode])
  have zero : dispatched.mem.wstk.data 0#8 = 0#8 := top.trans opcode
  have shape : dispatched = machine dispatched.mem.ram 0x353 dispatched.mem.wstk
      (Stack.pushWord { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170) := by
    rw [returnShape, ← dispatchPC]
    rfl
  have finish : ∃ final, Reaches (machine dispatched.mem.ram 0x353 dispatched.mem.wstk
      (Stack.pushWord { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170)) final ∧ final.pc = 0x173 ∧
      final.mem.wstk.ptr = 0 ∧ final.mem.ram = dispatched.mem.ram ∧
      final.mem.rstk.ptr = outer.mem.rstk.ptr ∧
      final.mem.rstk.data = (Stack.pushWord { dispatched.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170).data := by
    iterate 4
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, code353, code354, code357, code170, working, zero]
        rfl
    exact ⟨_, .refl _, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨final, after, finalPC, finalWorking, finalMemory, finalReturning, finalFrame⟩ := finish
  have after' : Reaches dispatched final := by simpa only [← shape] using after
  refine ⟨first, final, firstStep, suffix.trans after', finalPC, finalWorking,
    rep.transport finalMemory, ?_, finalReturning, ?_⟩
  · intro address outside
    rw [finalMemory]
    exact headerMemory address outside
  · intro index below
    rw [finalFrame, returnShape]
    exact returnFrame index below

end ProgramProofs.Uxnmin
