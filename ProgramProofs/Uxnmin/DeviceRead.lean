import ProgramProofs.Uxnmin.Code
import ProgramProofs.Host.Execution
import ProgramProofs.Host.Reduction

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The native DEI helper reads the two input literals or the shadow port table. -/
theorem device_read (ram : Word → Byte) (code : CodeImage ram)
    (port : Byte) (working returning : Uxn.Stack) (returnAddress : Word)
    (workingSpace : working.ptr.toNat ≤ 251) (returnSpace : returning.ptr.toNat ≤ 253) :
    ∃ final, Reaches (machine ram 0x190 (Stack.push working port)
      (Stack.pushWord returning returnAddress)) final ∧
      final.pc = returnAddress ∧ final.mem.ram = ram ∧
      final.mem.wstk.ptr = working.ptr + 1 ∧
      final.mem.wstk.data working.ptr =
        (if port = 0x12 then ram 0x199 else if port = 0x17 then ram 0x1a4
         else ram (0x759 + port.setWidth 16)) ∧
      final.mem.rstk.ptr = returning.ptr ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) ∧
      (∀ index : Byte, index.toNat < returning.ptr.toNat → final.mem.rstk.data index = returning.data index) := by
  have h190 : ram 0x190#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h191 : ram 0x191#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h192 : ram 0x192#16 = 0x12#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h193 : ram 0x193#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h194 : ram 0x194#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h195 : ram 0x195#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h196 : ram 0x196#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h197 : ram 0x197#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h198 : ram 0x198#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h19a : ram 0x19a#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h19b : ram 0x19b#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h19c : ram 0x19c#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h19d : ram 0x19d#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h19e : ram 0x19e#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h19f : ram 0x19f#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a0 : ram 0x1a0#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a1 : ram 0x1a1#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a2 : ram 0x1a2#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a3 : ram 0x1a3#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a5 : ram 0x1a5#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a6 : ram 0x1a6#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a7 : ram 0x1a7#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a8 : ram 0x1a8#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1a9 : ram 0x1a9#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1aa : ram 0x1aa#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ab : ram 0x1ab#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ac : ram 0x1ac#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ad : ram 0x1ad#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ae : ram 0x1ae#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  by_cases input : port = 0x12
  · subst port
    iterate 7
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, Stack.push, Stack.pushWord, h190, h191, h192, h193, h194, h195, h196, h197, h198, h19a, h19b, h19c, h19d, h19e, h19f, h1a0, h1a1, h1a2, h1a3, h1a5, h1a6, h1a7, h1a8, h1a9, h1aa, h1ab, h1ac, h1ad, h1ae]
        rfl
    refine ⟨_, .refl _, rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
    · simp
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  · simp only [BitVec.ofNat_eq_ofNat] at input
    have inputWide : ¬18#16 = port.setWidth 16 := by bv_omega
    by_cases kind : port = 0x17
    · subst port
      iterate 11
        apply Reaches.prepend
        · simp [uxn_state, uxn_step, Stack.push, Stack.pushWord, h190, h191, h192, h193, h194, h195, h196, h197, h198, h19a, h19b, h19c, h19d, h19e, h19f, h1a0, h1a1, h1a2, h1a3, h1a5, h1a6, h1a7, h1a8, h1a9, h1aa, h1ab, h1ac, h1ad, h1ae, input]
          rfl
      refine ⟨_, .refl _, rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
      · simp
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]
    · simp only [BitVec.ofNat_eq_ofNat] at kind
      have kindWide : ¬23#16 = port.setWidth 16 := by bv_omega
      iterate 14
        apply Reaches.prepend
        · simp [uxn_state, uxn_step, Stack.push, Stack.pushWord, h190, h191, h192, h193, h194, h195, h196, h197, h198, h19a, h19b, h19c, h19d, h19e, h19f, h1a0, h1a1, h1a2, h1a3, h1a5, h1a6, h1a7, h1a8, h1a9, h1aa, h1ab, h1ac, h1ad, h1ae, input, kind, inputWide, kindWide]
          rfl
      refine ⟨_, .refl _, rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
      · have joined : 0#8 ++ port = port.setWidth 16 := by
          simpa using (join_bytes 0#8 port).symm
        simp [input, kind, joined]
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
