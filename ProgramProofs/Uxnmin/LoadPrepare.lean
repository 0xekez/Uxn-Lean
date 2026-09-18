import ProgramProofs.Uxnmin.LoadTail
import ProgramProofs.Uxnmin.Pc

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

def AddressMode.loadEntry : AddressMode → Word
  | .zero => 0x45e | .relative => 0x477 | .absolute => 0x498

/-- Converts the popped address to the load handler's full guest address. -/
theorem load_prepare (kind : AddressMode) (memory : Word → Byte) (pc value : Word)
    (working returning : Uxn.Stack) (code : CodeImage memory)
    (high : memory 0x45#16 = (pc >>> 8).setWidth 8)
    (low : memory 0x46#16 = pc.setWidth 8)
    (workingSpace : working.ptr.toNat ≤ 247) (returnSpace : returning.ptr.toNat ≤ 249) :
    ∃ final, Reaches (machine memory (kind.loadEntry + 3) (Stack.pushWord working value) returning) final ∧
      final.pc = kind.loadTail ∧ final.mem.ram = memory ∧
      final.mem.wstk.ptr = working.ptr + 2#8 ∧
      Stack.pushWord { final.mem.wstk with ptr := working.ptr }
        (kind.nativeAddress pc value) = final.mem.wstk ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat →
        final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat →
        final.mem.rstk.data index = returning.data index) := by
  cases kind with
  | zero | absolute =>
    refine ⟨_, .refl _, rfl, rfl, ?_, ?_, rfl, ?_, ?_⟩
    · simp [machine, Stack.pushWord, Stack.push, BitVec.add_assoc]
    · simp only [machine, AddressMode.nativeAddress, reduceCtorEq, if_false, Stack.pushWord, Stack.push]
      congr 1
      funext index
      simp only [Function.update_apply]
      split_ifs <;> rfl
    · intro index below
      simp (disch := bv_omega) only [machine, Stack.pushWord, Stack.push, Function.update_of_ne]
    · intro index below
      rfl
  | relative =>
    let scratch : Uxn.Stack := { Stack.pushWord working value with ptr := working.ptr }
    have initial : Reaches
        (machine memory 0x47a (Stack.pushWord working value) returning)
        (machine memory 0x271 (Stack.push scratch (value.setWidth 8))
          (Stack.pushWord returning 0x47e)) := by
      have code47a : memory 0x47a#16 = 0x03#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code47b : memory 0x47b#16 = 0x60#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code47c : memory 0x47c#16 = 0xfd#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      have code47d : memory 0x47d#16 = 0xf3#8 := code _ (by decide) (by decide) (by simp [MutableCode])
      iterate 2
        apply Reaches.next
        · simp [uxn_state, uxn_step, code47a, code47b, code47c, code47d]
          rfl
      simpa [machine, scratch, Stack.pushWord, Stack.push, BitVec.add_assoc] using
        (Reaches.refl (machine memory 0x271 (Stack.push scratch (value.setWidth 8))
          (Stack.pushWord returning 0x47e)))
    obtain ⟨final, steps, finalPC, ram, pointer, result, returningPointer, frame, returnFrame⟩ :=
      pc_relative memory pc 0x47e (value.setWidth 8) scratch returning code high low
        (by dsimp [scratch]; omega) (by omega)
    simp only [scratch, BitVec.ofNat_eq_ofNat] at pointer result frame
    refine ⟨final, initial.trans steps, finalPC, ram, pointer, ?_, returningPointer, ?_, returnFrame⟩
    · simpa [pointer, AddressMode.nativeAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc, result]
        using Stack.asPushWord final.mem.wstk
    · intro index below
      rw [frame _ below]
      simp (disch := bv_omega) only [Stack.pushWord, Stack.push, Function.update_of_ne]

end ProgramProofs.Uxnmin
