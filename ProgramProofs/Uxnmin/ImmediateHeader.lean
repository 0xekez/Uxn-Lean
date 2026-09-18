import ProgramProofs.Uxnmin.ImmediateDispatch
import ProgramProofs.Uxnmin.Header
import ProgramProofs.Uxnmin.RepresentationPop

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Fetch, decode, and the immediate dispatcher reach the selected native handler. -/
theorem immediate_header (kind : ImmediateKind) {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize)
    (opcode : guest.mem.ram guest.pc = kind.opcode) :
    ∃ final, Reaches outer final ∧
      Represents {guest with pc := guest.pc + 1} final ∧
      final.pc = kind.entry ∧ final.mem.wstk.ptr = 1 ∧ final.mem.wstk.data 0 = kind.opcode ∧
      Stack.pushWord {final.mem.rstk with ptr := outer.mem.rstk.ptr} 0x170 = final.mem.rstk ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat → final.mem.rstk.data index = outer.mem.rstk.data index) ∧
      final.mem.ram 0x44 = (if kind.opcode.getLsbD 5 then 1 else 0) ∧
      final.mem.ram 0x2bf = (if kind.opcode.getLsbD 7 then 1 else 0) ∧
      final.mem.ram 0x40 = (stackBase (kind.opcode.getLsbD 6) >>> 8).setWidth 8 ∧
      final.mem.ram 0x41 = (stackBase (kind.opcode.getLsbD 6)).setWidth 8 ∧
      (∀ address, ¬ PopScratch address → final.mem.ram address = outer.mem.ram address) := by
  obtain ⟨dispatched, headerRun, rep, working, top, returnShape, returnFrame,
    short, keep, sourceHigh, sourceLow, _, pc, memory⟩ := instruction_header boundary confined
  have mask : kind.opcode &&& 0x1f = 0 := by
    cases kind with
    | jci | jmi | jsi => decide
    | lit short ret => cases short <;> cases ret <;> decide
  have tableHigh : outer.mem.ram 0x515#16 = 0x03#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have tableLow : outer.mem.ram 0x516#16 = 0x53#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
  have entry : dispatched.pc = 0x353 := by
    rw [opcode, mask] at pc
    simpa [tableHigh, tableLow] using pc
  have workingEta : Stack.push {dispatched.mem.wstk with ptr := 0} kind.opcode = dispatched.mem.wstk := by
    have update := Function.update_eq_self (0 : Byte) dispatched.mem.wstk.data
    rw [top, opcode] at update
    cases hstack : dispatched.mem.wstk
    simp_all [Stack.push]
  obtain ⟨final, dispatchRun, finalPC, finalRAM, finalWP, finalTop, finalRS, _⟩ :=
    immediate_dispatch kind dispatched.mem.ram {dispatched.mem.wstk with ptr := 0} dispatched.mem.rstk rep.code (by change (0#8).toNat ≤ 253; decide)
  have run : Reaches outer final := by
    apply headerRun.trans
    have shape : dispatched = machine dispatched.mem.ram dispatched.pc dispatched.mem.wstk dispatched.mem.rstk := rfl
    rw [entry] at shape
    rw [shape]
    simpa only [workingEta] using dispatchRun
  refine ⟨final, run, rep.transport finalRAM, finalPC, ?_, finalTop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using finalWP
  · rw [finalRS]; exact returnShape
  · intro index below
    rw [finalRS]; exact returnFrame index below
  · rw [finalRAM]; simpa only [opcode] using short
  · rw [finalRAM]; simpa only [opcode] using keep
  · rw [finalRAM]; simpa only [opcode] using sourceHigh
  · rw [finalRAM]; simpa only [opcode] using sourceLow
  · intro address outside
    rw [finalRAM]; exact memory address outside

end ProgramProofs.Uxnmin
