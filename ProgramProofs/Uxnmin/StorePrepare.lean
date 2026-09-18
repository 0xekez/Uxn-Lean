import ProgramProofs.Uxnmin.StoreTail
import ProgramProofs.Uxnmin.Pc

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Store operands are reordered, and relative byte addresses are sign extended. -/
theorem store_prepare (kind : AddressMode) (memory : Word → Byte) (pc address value : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (high : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (low : memory 0x46#16 = pc.setWidth 8)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches
      (machine memory (kind.storeEntry + 6) (Stack.pushWord (Stack.pushWord working address) value) returning) final ∧
      final.pc = kind.storeTail ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 4#8 ∧
      Stack.pushWord (Stack.pushWord { final.mem.wstk with ptr := working.ptr } value)
        (kind.nativeAddress pc address) = final.mem.wstk ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  let base : Uxn.Stack := { Stack.pushWord (Stack.pushWord working address) value with ptr := working.ptr }
  let swapped := Stack.pushWord (Stack.pushWord base value) address
  have swappedPointer : swapped.ptr = working.ptr + 4#8 := by
    simp [swapped, base, Stack.pushWord, Stack.push, BitVec.add_assoc]
  have swappedFirst : swapped.data working.ptr ++ swapped.data (working.ptr + 1#8) = value := by
    simp [swapped, base, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
  have swappedSecond : swapped.data (working.ptr + 2#8) ++ swapped.data (working.ptr + 3#8) = address := by
    simp [swapped, base, Stack.pushWord, Stack.push, BitVec.add_assoc, append_split]
  have swappedFrame (index : Byte) (bound : index.toNat < working.ptr.toNat) :
      swapped.data index = working.data index := by
    simp (disch := bv_omega) only [swapped, base, Stack.pushWord, Stack.push, Function.update_of_ne]
  have swap : Uxn.step
      (machine memory (kind.storeEntry + 6) (Stack.pushWord (Stack.pushWord working address) value) returning) =
      .done (.next (machine memory (kind.storeEntry + 7) swapped returning)) := by
    have byte : memory (kind.storeEntry + 6) = 0x24#8 := by
      cases kind <;> exact code _ (by decide) (by decide) (by simp [MutableCode, AddressMode.storeEntry])
    simp only [BitVec.ofNat_eq_ofNat] at byte
    simp [uxn_state, uxn_step, byte, swapped, base]
  cases kind with
  | zero | absolute =>
    refine ⟨_, .next swap (.refl _), rfl, rfl, swappedPointer, ?_, rfl, swappedFrame, ?_⟩
    · simpa [machine, swappedPointer, AddressMode.nativeAddress, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, swappedFirst, swappedSecond] using Stack.asPushPair swapped
    · intro index bound
      rfl
  | relative =>
    let scratch : Uxn.Stack := { swapped with ptr := working.ptr + 2#8 }
    have initial : Reaches (machine memory 0x48e swapped returning)
        (machine memory 0x271 (Stack.push scratch (address.setWidth 8))
          (Stack.pushWord returning 0x492)) := by
      have code48e : memory 0x48e#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code48f : memory 0x48f#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code490 : memory 0x490#16 = 0xfd#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code491 : memory 0x491#16 = 0xdf#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have swappedLow : swapped.data (working.ptr + 3#8) = address.setWidth 8 := by
        simpa only [BitVec.setWidth_append_eq_right] using congrArg (BitVec.setWidth 8) swappedSecond
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, code48e, code48f, code490, code491, swappedPointer, swappedLow]
          rfl
      simpa [machine, scratch, Stack.push, Stack.pushWord, BitVec.add_assoc] using
        (Reaches.refl (machine memory 0x271 (Stack.push scratch (address.setWidth 8))
          (Stack.pushWord returning 0x492)))
    obtain ⟨final, steps, finalPC, ram, pointer, result, returningPointer, frame, returnFrame⟩ :=
      pc_relative memory pc 0x492 (address.setWidth 8) scratch returning code high low
        (by dsimp [scratch]; bv_omega) (by omega)
    have finalPointer : final.mem.wstk.ptr = working.ptr + 4#8 := by
      simpa [scratch, BitVec.add_assoc] using pointer
    have finalFirst : final.mem.wstk.data working.ptr ++ final.mem.wstk.data (working.ptr + 1#8) = value := by
      rw [frame _ (by dsimp [scratch]; bv_omega), frame _ (by dsimp [scratch]; bv_omega)]
      exact swappedFirst
    have finalSecond : final.mem.wstk.data (working.ptr + 2#8) ++ final.mem.wstk.data (working.ptr + 3#8) =
        pc + (address.setWidth 8).signExtend 16 := by
      simpa [scratch, BitVec.add_assoc] using result
    refine ⟨final, .next swap (initial.trans steps), finalPC, ram, finalPointer, ?_, returningPointer, ?_, returnFrame⟩
    · simpa [AddressMode.nativeAddress, finalPointer, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        finalFirst, finalSecond] using Stack.asPushPair final.mem.wstk
    · intro index bound
      rw [frame _ (by dsimp [scratch]; bv_omega)]
      exact swappedFrame index bound

end ProgramProofs.Uxnmin
