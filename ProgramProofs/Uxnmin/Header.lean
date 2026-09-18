import Mathlib.Tactic.Tauto
import ProgramProofs.Uxnmin.Representation
import ProgramProofs.Uxnmin.Dispatch
import ProgramProofs.Uxnmin.Decode
import ProgramProofs.Uxnmin.StackView

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Current-ROM fetch and decode, preserving an arbitrary active return frame. -/
theorem instruction_header_full {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize) :
    ∃ final, Reaches outer final ∧
      Represents { guest with pc := guest.pc + 1 } final ∧
      final.mem.wstk.ptr = 1 ∧ final.mem.wstk.data 0 = guest.mem.ram guest.pc ∧
      Stack.pushWord { final.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170 = final.mem.rstk ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) ∧
      final.mem.ram 0x44 = (if (guest.mem.ram guest.pc).getLsbD 5 then 1 else 0) ∧
      final.mem.ram 0x2bf = (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0) ∧
      final.mem.ram 0x40 = (stackBase ((guest.mem.ram guest.pc).getLsbD 6) >>> 8).setWidth 8 ∧
      final.mem.ram 0x41 = (stackBase ((guest.mem.ram guest.pc).getLsbD 6)).setWidth 8 ∧
      final.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6) +
        (0x100 + (if (guest.mem.ram guest.pc).getLsbD 7 then 1#8 else 0#8).setWidth 16)) =
        (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr ∧
      final.pc = outer.mem.ram (0x515 + ((guest.mem.ram guest.pc) &&& 0x1f).setWidth 16 * 2) ++
        outer.mem.ram (0x516 + ((guest.mem.ram guest.pc) &&& 0x1f).setWidth 16 * 2) ∧
      (∀ address, ¬ PopScratch address → final.mem.ram address = outer.mem.ram address) ∧
      final.mem.ram 0x42 = (stackBase (!((guest.mem.ram guest.pc).getLsbD 6)) >>> 8).setWidth 8 ∧
      final.mem.ram 0x43 = (stackBase (!((guest.mem.ram guest.pc).getLsbD 6))).setWidth 8 := by
  obtain ⟨fetched, fetchRun, fetchPC, fetchPtr, fetchedOpcode, fetchReturn, fetchMemory⟩ :=
    fetch outer.mem.ram guest.pc outer.mem.wstk
      (Stack.pushWord outer.mem.rstk 0x170) boundary.code boundary.workingEmpty
      boundary.pcHigh boundary.pcLow confined
  have fetchedCode : CodeImage fetched.mem.ram := by
    rw [fetchMemory]
    exact (boundary.code.write _ _ (.inl (by decide))).write _ _ (.inl (by decide))
  have fetchedShape : fetched = machine fetched.mem.ram 0x22e fetched.mem.wstk fetched.mem.rstk := by
    cases fetched
    simpa [machine] using fetchPC
  have opcode : fetched.mem.wstk.data 0 = guest.mem.ram guest.pc :=
    fetchedOpcode.trans (boundary.ram _ confined)
  obtain ⟨final, decodeRun, working, top, returning, short, keep, pc, source, destination,
      code, cursor, returnFrame, memoryFrame⟩ :=
    decode_modes fetched.mem.ram (guest.mem.ram guest.pc) fetched.mem.wstk fetched.mem.rstk
      fetchedCode fetchPtr opcode (by
        rw [fetchReturn]
        simp only [Stack.pushWord, Stack.push]
        have := boundary.returnSpace
        bv_omega)
  have reached : Reaches outer final := by
    have call : outer.mem.ram 0x16d#16 = 0x60#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
    have high : outer.mem.ram 0x16e#16 = 0x00#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
    have low : outer.mem.ram 0x16f#16 = 0xb2#8 := boundary.code _ (by decide) (by decide) (by simp [MutableCode])
    refine .next ?_ (fetchRun.trans ?_)
    · change Uxn.step (machine outer.mem.ram outer.pc outer.mem.wstk outer.mem.rstk) = _
      rw [boundary.pc]
      simp [uxn_state, uxn_step, call, high, low]
    · rw [fetchedShape]
      exact decodeRun
  have stable (address : Word) (scratch : ¬ PopScratch address) :
      final.mem.ram address = outer.mem.ram address := by
    simp only [PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at scratch
    rw [memoryFrame address (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      tauto), fetchMemory]
    simp only [Function.update_of_ne scratch.2.2.2.2.2.1,
      Function.update_of_ne scratch.2.2.2.2.2.2.1]
  have represented : Represents { guest with pc := guest.pc + 1 } final := by
    constructor
    · exact code
    · intro address bound
      rw [stable (relocate address) (by
        simp only [PopScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
        dsimp [relocate, ramSize] at *
        repeat' constructor <;> bv_omega)]
      exact boundary.ram address bound
    · intro ret index
      rw [stable _ (by
        cases ret <;> simp only [PopScratch, stackBase, Bool.false_eq_true, if_false, if_true,
          List.mem_cons, List.not_mem_nil, or_false, not_or]
        all_goals repeat' constructor <;> bv_omega)]
      exact boundary.stackData ret index
    · intro ret
      rw [memoryFrame _ (by cases ret <;> decide), fetchMemory]
      cases ret
      · simpa [stackBase, guestStack] using boundary.stackPointer false
      · simpa [stackBase, guestStack] using boundary.stackPointer true
    · rw [memoryFrame _ (by decide), fetchMemory]
      simp
    · rw [memoryFrame _ (by decide), fetchMemory]
      simp
  have frame (index : Byte) (smaller : index.toNat < outer.mem.rstk.ptr.toNat) :
      final.mem.rstk.data index = outer.mem.rstk.data index := by
    rw [returnFrame _ (by
      rw [fetchReturn]
      simp only [Stack.pushWord, Stack.push]
      have := boundary.returnSpace
      bv_omega), fetchReturn]
    have space := boundary.returnSpace
    simp (disch := bv_omega) [Stack.pushWord, Stack.push, Function.update_of_ne]
  have modeFacts : ∀ opcode : Byte,
      (if 0#16 = 32#16 &&& opcode.setWidth 16 then 0#8 else 1#8) =
        (if opcode.getLsbD 5 then 1 else 0) ∧
      (if 0#16 = 128#16 &&& opcode.setWidth 16 then 0#8 else 1#8) =
        (if opcode.getLsbD 7 then 1 else 0) ∧
      (64#16 &&& opcode.setWidth 16 = 0 ↔ opcode.getLsbD 6 = false) := by decide
  obtain ⟨shortMode, keepMode, retMode⟩ := modeFacts (guest.mem.ram guest.pc)
  have sourceWord : final.mem.ram 0x40 ++ final.mem.ram 0x41 =
      stackBase ((guest.mem.ram guest.pc).getLsbD 6) := by
    rw [source]
    simp only [retMode]
    cases (guest.mem.ram guest.pc).getLsbD 6 <;> rfl
  have destinationWord : final.mem.ram 0x42 ++ final.mem.ram 0x43 =
      stackBase (!((guest.mem.ram guest.pc).getLsbD 6)) := by
    rw [destination]
    simp only [retMode]
    cases (guest.mem.ram guest.pc).getLsbD 6 <;> rfl
  refine ⟨final, reached, represented, working, top, ?_, frame,
    short.trans shortMode, keep.trans keepMode, ?_, ?_, ?_, ?_, stable, ?_, ?_⟩
  · have pointer : final.mem.rstk.ptr = outer.mem.rstk.ptr + 2 := by
      simpa [fetchReturn, Stack.pushWord, Stack.push, BitVec.add_assoc] using returning
    have high : final.mem.rstk.data outer.mem.rstk.ptr = 1 := by
      rw [returnFrame _ (by
        rw [fetchReturn]
        simp only [Stack.pushWord, Stack.push]
        have := boundary.returnSpace
        bv_omega), fetchReturn]
      simp [Stack.pushWord, Stack.push]
    have low : final.mem.rstk.data (outer.mem.rstk.ptr + 1) = 0x70 := by
      rw [returnFrame _ (by
        rw [fetchReturn]
        simp only [Stack.pushWord, Stack.push]
        have := boundary.returnSpace
        bv_omega), fetchReturn]
      simp [Stack.pushWord, Stack.push]
    have two : final.mem.rstk.ptr - 2 = outer.mem.rstk.ptr := by rw [pointer]; bv_omega
    have one : final.mem.rstk.ptr - 1 = outer.mem.rstk.ptr + 1 := by rw [pointer]; bv_omega
    have joined : (1 : Byte) ++ (0x70 : Byte) = (0x170 : Word) := rfl
    simpa only [two, one, high, low, joined] using Stack.asPushWord final.mem.rstk
  · have high := congrArg (fun word : Word => (word >>> 8).setWidth 8) sourceWord
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left] at high
    exact high
  · have low := congrArg (fun word : Word => word.setWidth 8) sourceWord
    rw [BitVec.setWidth_append_eq_right] at low
    exact low
  · simp only [retMode] at cursor
    cases hr : (guest.mem.ram guest.pc).getLsbD 6 <;>
      cases hk : (guest.mem.ram guest.pc).getLsbD 7 <;>
      simp only [hr, Bool.true_eq_false, if_true, if_false] at cursor
    · exact represented.stackPointer false
    · change final.mem.ram 0x656 = guest.mem.wstk.ptr
      rw [cursor, fetchMemory]
      simpa [stackBase, guestStack] using boundary.stackPointer false
    · exact represented.stackPointer true
    · change final.mem.ram 0x758 = guest.mem.rstk.ptr
      rw [cursor, fetchMemory]
      simpa [stackBase, guestStack] using boundary.stackPointer true
  · rw [pc, fetchMemory]
    have small : ((guest.mem.ram guest.pc) &&& 31#8).toNat ≤ 31 := Nat.and_le_right
    simp (disch := bv_omega) only [Function.update_of_ne]
    rfl

  · have high := congrArg (fun word : Word => (word >>> 8).setWidth 8) destinationWord
    rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_append_eq_left] at high
    exact high
  · have low := congrArg (fun word : Word => word.setWidth 8) destinationWord
    rw [BitVec.setWidth_append_eq_right] at low
    exact low

theorem instruction_header {guest outer : Uxn.State}
    (boundary : EvaluationBoundary guest outer) (confined : guest.pc.toNat < ramSize) :
    ∃ final, Reaches outer final ∧
      Represents { guest with pc := guest.pc + 1 } final ∧
      final.mem.wstk.ptr = 1 ∧ final.mem.wstk.data 0 = guest.mem.ram guest.pc ∧
      Stack.pushWord { final.mem.rstk with ptr := outer.mem.rstk.ptr } 0x170 = final.mem.rstk ∧
      (∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
        final.mem.rstk.data index = outer.mem.rstk.data index) ∧
      final.mem.ram 0x44 = (if (guest.mem.ram guest.pc).getLsbD 5 then 1 else 0) ∧
      final.mem.ram 0x2bf = (if (guest.mem.ram guest.pc).getLsbD 7 then 1 else 0) ∧
      final.mem.ram 0x40 = (stackBase ((guest.mem.ram guest.pc).getLsbD 6) >>> 8).setWidth 8 ∧
      final.mem.ram 0x41 = (stackBase ((guest.mem.ram guest.pc).getLsbD 6)).setWidth 8 ∧
      final.mem.ram (stackBase ((guest.mem.ram guest.pc).getLsbD 6) +
        (0x100 + (if (guest.mem.ram guest.pc).getLsbD 7 then 1#8 else 0#8).setWidth 16)) =
        (guestStack guest ((guest.mem.ram guest.pc).getLsbD 6)).ptr ∧
      final.pc = outer.mem.ram (0x515 + ((guest.mem.ram guest.pc) &&& 0x1f).setWidth 16 * 2) ++
        outer.mem.ram (0x516 + ((guest.mem.ram guest.pc) &&& 0x1f).setWidth 16 * 2) ∧
      (∀ address, ¬ PopScratch address → final.mem.ram address = outer.mem.ram address) := by
  obtain ⟨final, reached, represented, working, top, returning, frame, short, keep,
    high, low, cursor, pc, stable, _, _⟩ := instruction_header_full boundary confined
  exact ⟨final, reached, represented, working, top, returning, frame, short, keep,
    high, low, cursor, pc, stable⟩


end ProgramProofs.Uxnmin
