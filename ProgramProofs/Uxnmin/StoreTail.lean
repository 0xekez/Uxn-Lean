import ProgramProofs.Uxnmin.Poke
import ProgramProofs.Uxnmin.MemoryAddress

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def AddressMode.storeEntry : AddressMode → Word
  | .zero => 0x46a | .relative => 0x487 | .absolute => 0x4a4

def AddressMode.storeTail : AddressMode → Word
  | .zero => 0x471 | .relative => 0x492 | .absolute => 0x4ab

/-- Each store handler supplies its addressing mask to the common memory writer. -/
theorem store_tail (kind : AddressMode) (memory : Word → Byte)
    (address value : Word) (short : Bool) (working returning : Uxn.Stack) (returnAddress : Word)
    (code : CodeImage memory) (mode : memory 0x44#16 = if short then 1 else 0)
    (firstBound : address.toNat < ramSize)
    (secondBound : short = true → ((address + 1#16) &&& kind.mask).toNat < ramSize)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory kind.storeTail (Stack.pushWord (Stack.pushWord working value) address)
        (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.wstk.ptr = working.ptr ∧
      final.mem.rstk.ptr = returning.ptr ∧
      final.mem.ram = pokeMemory memory address kind.mask value short ∧ CodeImage final.mem.ram ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have call : Reaches
      (machine memory kind.storeTail (Stack.pushWord (Stack.pushWord working value) address)
        (Stack.pushWord returning returnAddress))
      (machine memory 0x2d8 (Stack.pushWord (Stack.pushWord (Stack.pushWord working value) address) kind.mask)
        (Stack.pushWord returning returnAddress)) := by
    cases kind
    case zero =>
      have code471 : memory 0x471#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code472 : memory 0x472#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code473 : memory 0x473#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code474 : memory 0x474#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code475 : memory 0x475#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code476 : memory 0x476#16 = 0x61#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, AddressMode.storeTail, code471, code472, code473, code474, code475, code476]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, AddressMode.mask,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSetWidth]
      exact .refl _
    case relative =>
      have code492 : memory 0x492#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code493 : memory 0x493#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code494 : memory 0x494#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code495 : memory 0x495#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code496 : memory 0x496#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code497 : memory 0x497#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, AddressMode.storeTail, code492, code493, code494, code495, code496, code497]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, AddressMode.mask,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSetWidth]
      exact .refl _
    case absolute =>
      have code4ab : memory 0x4ab#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4ac : memory 0x4ac#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4ad : memory 0x4ad#16 = 0xff#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4ae : memory 0x4ae#16 = 0x40#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4af : memory 0x4af#16 = 0xfe#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code4b0 : memory 0x4b0#16 = 0x27#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, AddressMode.storeTail, code4ab, code4ac, code4ad, code4ae, code4af, code4b0]
          rfl
      simp only [machine, Stack.pushWord, Stack.push, AddressMode.mask,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSetWidth]
      exact .refl _
  obtain ⟨final, steps, pc, ram, image, wp, rp, wf, rf⟩ :=
    poke_operand memory address kind.mask value returnAddress short working returning code mode
      firstBound secondBound workingSpace returnSpace
  exact ⟨final, call.trans steps, pc, wp, rp, ram, image, wf, rf⟩

end ProgramProofs.Uxnmin
