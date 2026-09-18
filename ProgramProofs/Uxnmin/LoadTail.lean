import ProgramProofs.Uxnmin.Peek
import ProgramProofs.Uxnmin.MemoryAddress

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def AddressMode.loadTail : AddressMode → Word
  | .zero => 0x461 | .relative => 0x47e | .absolute => 0x49b

/-- Reading memory and pushing its result is shared by the three load handlers. -/
theorem load_tail (kind : AddressMode) (memory : Word → Byte)
    (softwareStack : Word) (pointer : Byte) (address : Word) (short : Bool)
    (working returning : Uxn.Stack) (returnAddress : Word)
    (selected : softwareStack = 0x555 ∨ softwareStack = 0x657)
    (code : CodeImage memory)
    (high : memory 0x40#16 = (softwareStack >>> 8).setWidth 8)
    (low : memory 0x41#16 = softwareStack.setWidth 8)
    (mode : memory 0x44#16 = if short then 1 else 0)
    (ptr : memory (softwareStack + 0x100#16) = pointer)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 247) :
    ∃ final, Reaches
      (machine memory kind.loadTail (Stack.pushWord working address)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = storeStackOperand memory softwareStack pointer
        (peekValue memory address kind.mask short) short ∧
      CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat →
        final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat →
        final.mem.rstk.data index = returning.data index) := by
  have call (working returning : Uxn.Stack) : Reaches
      (machine memory kind.loadTail (Stack.pushWord working address) returning)
      (machine memory 0x2f8 (Stack.pushWord (Stack.pushWord working address) kind.mask)
        (Stack.pushWord returning (kind.loadTail + 6))) := by
    cases kind
    case zero =>
      have code461 : memory 0x461#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code462 : memory 0x462#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code463 : memory 0x463#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code464 : memory 0x464#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code465 : memory 0x465#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code466 : memory 0x466#16 = 0x91#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, AddressMode.loadTail, code461, code462, code463, code464, code465, code466]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, AddressMode.loadTail, AddressMode.mask,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSetWidth]
      exact .refl _
    case relative =>
      have code47e : memory 0x47e#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code47f : memory 0x47f#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code480 : memory 0x480#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code481 : memory 0x481#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code482 : memory 0x482#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code483 : memory 0x483#16 = 0x74#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, AddressMode.loadTail, code47e, code47f, code480, code481, code482, code483]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, AddressMode.loadTail, AddressMode.mask,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSetWidth]
      exact .refl _
    case absolute =>
      have code49b : memory 0x49b#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code49c : memory 0x49c#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code49d : memory 0x49d#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code49e : memory 0x49e#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code49f : memory 0x49f#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4a0 : memory 0x4a0#16 = 0x57#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, AddressMode.loadTail, code49b, code49c, code49d, code49e, code49f, code4a0]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, AddressMode.loadTail, AddressMode.mask,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSetWidth]
      exact .refl _
  have jump (working returning : Uxn.Stack) :
      Uxn.step (machine memory (kind.loadTail + 6) working returning) =
        .done (.next (machine memory 0x28c working returning)) := by
    cases kind
    case zero =>
      have code467 : memory 0x467#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code468 : memory 0x468#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code469 : memory 0x469#16 = 0x22#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      simp [uxn_state, uxn_step, AddressMode.loadTail, code467, code468, code469]
    case relative =>
      have code484 : memory 0x484#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code485 : memory 0x485#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code486 : memory 0x486#16 = 0x05#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      simp [uxn_state, uxn_step, AddressMode.loadTail, code484, code485, code486]
    case absolute =>
      have code4a1 : memory 0x4a1#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4a2 : memory 0x4a2#16 = 0xfd#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4a3 : memory 0x4a3#16 = 0xe8#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      simp [uxn_state, uxn_step, AddressMode.loadTail, code4a1, code4a2, code4a3]
  obtain ⟨read, readSteps, readPC, readMemory, readPointer, readShape, readReturnPointer,
    readFrame, readReturnFrame⟩ := peek_operand memory address kind.mask (kind.loadTail + 6)
      short working (Stack.pushWord returning returnAddress) code mode (by omega)
      (by simp only [Stack.pushWord, Stack.push]; bv_omega)
  have returnHigh : read.mem.rstk.data returning.ptr = (returnAddress >>> 8).setWidth 8 := by
    rw [readReturnFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnLow : read.mem.rstk.data (returning.ptr + 1#8) = returnAddress.setWidth 8 := by
    rw [readReturnFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp [Stack.pushWord, Stack.push]
  have returnShape : Stack.pushWord { read.mem.rstk with ptr := returning.ptr }
      returnAddress = read.mem.rstk := by
    have rp : read.mem.rstk.ptr = returning.ptr + 2#8 := by
      simpa [Stack.pushWord, Stack.push, BitVec.add_assoc] using readReturnPointer
    simpa [rp, BitVec.sub_eq_add_neg, BitVec.add_assoc, returnHigh, returnLow, append_split]
      using Stack.asPushWord read.mem.rstk
  obtain ⟨final, pushSteps, pc, wp, rp, ram, frame, returnFrame⟩ := push_operand memory softwareStack pointer
    (peekValue memory address kind.mask short) short
    { read.mem.wstk with ptr := working.ptr } { read.mem.rstk with ptr := returning.ptr }
    returnAddress selected code high low mode ptr workingSpace (by dsimp; omega)
  have readEta : read = machine memory (kind.loadTail + 6) read.mem.wstk read.mem.rstk := by
    cases read with
    | mk pc memory =>
      cases memory
      simp only [machine] at readPC readMemory ⊢
      rw [readPC, readMemory]
  have after : Reaches read final := by
    rw [readEta]
    apply Reaches.next (jump _ _)
    simpa only [readShape, returnShape] using pushSteps
  have finalCode : CodeImage final.mem.ram := by
    have above : 0x555 ≤ softwareStack.toNat := by rcases selected with rfl | rfl <;> decide
    have below : softwareStack.toNat ≤ 0x657 := by rcases selected with rfl | rfl <;> decide
    have ptrAfter : 0x555 ≤ (softwareStack + 0x100#16).toNat := by bv_omega
    have dataAfter (index : Byte) : 0x555 ≤ (softwareStack + index.setWidth 16).toNat := by bv_omega
    rw [ram]
    split <;> first
      | exact ((code.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))).write _ _
          (.inr (.inl (dataAfter _)))
      | exact (code.write _ _ (.inr (.inl ptrAfter))).write _ _ (.inr (.inl (dataAfter _)))
  refine ⟨final, (call _ _).trans (readSteps.trans after), pc, wp, rp, ram, finalCode, ?_, ?_⟩
  · intro index below
    rw [frame _ below, readFrame _ below]
  · intro index below
    rw [returnFrame _ below, readReturnFrame _ (by simp only [Stack.pushWord, Stack.push]; bv_omega)]
    simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
