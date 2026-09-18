import ProgramProofs.Uxnmin.DeviceWriteShadow

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- Route a shadowed device write to its host action, cache update, or silent return. -/
theorem device_write_route (ram : Word → Byte) (code : CodeImage ram)
    (port value : Byte) (working returning : Uxn.Stack)
    (workingSpace : working.ptr.toNat ≤ 251) :
    ∃ final, Reaches (machine ram 0x1bc (Stack.push (Stack.push working value) port) returning) final ∧
      final.pc = (if port = 0x0e then 0x1c3 else if port = 0x0f then 0x1cc
        else if port = 0x11 then 0x1d5 else if port = 0x18 then 0x1ea
        else if port = 0x19 then 0x1f3 else 0x1f5) ∧
      final.mem.ram = ram ∧ final.mem.wstk.ptr = working.ptr + 2 ∧
      final.mem.wstk.data working.ptr = value ∧ final.mem.wstk.data (working.ptr + 1) = port ∧
      final.mem.rstk = returning ∧
      (∀ index : Byte, index.toNat < working.ptr.toNat → final.mem.wstk.data index = working.data index) := by
  have h1bc : ram 0x1bc#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1bd : ram 0x1bd#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1be : ram 0x1be#16 = 0x0e#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1bf : ram 0x1bf#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c0 : ram 0x1c0#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c1 : ram 0x1c1#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c2 : ram 0x1c2#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c3 : ram 0x1c3#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c4 : ram 0x1c4#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c5 : ram 0x1c5#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c6 : ram 0x1c6#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c7 : ram 0x1c7#16 = 0x0f#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c8 : ram 0x1c8#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1c9 : ram 0x1c9#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ca : ram 0x1ca#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1cb : ram 0x1cb#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1cc : ram 0x1cc#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1cd : ram 0x1cd#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ce : ram 0x1ce#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1cf : ram 0x1cf#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d0 : ram 0x1d0#16 = 0x11#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d1 : ram 0x1d1#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d2 : ram 0x1d2#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d3 : ram 0x1d3#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d4 : ram 0x1d4#16 = 0x0e#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d5 : ram 0x1d5#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d6 : ram 0x1d6#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d7 : ram 0x1d7#16 = 0x07#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d8 : ram 0x1d8#16 = 0x59#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1d9 : ram 0x1d9#16 = 0xa0#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1da : ram 0x1da#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1db : ram 0x1db#16 = 0x10#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1dc : ram 0x1dc#16 = 0x38#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1dd : ram 0x1dd#16 = 0x14#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1de : ram 0x1de#16 = 0x04#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1df : ram 0x1df#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e0 : ram 0x1e0#16 = 0x93#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e1 : ram 0x1e1#16 = 0x33#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e2 : ram 0x1e2#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e3 : ram 0x1e3#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e4 : ram 0x1e4#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e5 : ram 0x1e5#16 = 0x18#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e6 : ram 0x1e6#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e7 : ram 0x1e7#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e8 : ram 0x1e8#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1e9 : ram 0x1e9#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ea : ram 0x1ea#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1eb : ram 0x1eb#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ec : ram 0x1ec#16 = 0x06#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ed : ram 0x1ed#16 = 0x80#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ee : ram 0x1ee#16 = 0x19#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1ef : ram 0x1ef#16 = 0x09#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1f0 : ram 0x1f0#16 = 0x20#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1f1 : ram 0x1f1#16 = 0x00#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1f2 : ram 0x1f2#16 = 0x02#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1f3 : ram 0x1f3#16 = 0x17#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  have h1f4 : ram 0x1f4#16 = 0x6c#8 := code _ (by decide) (by decide) (by simp [MutableCode])
  by_cases p14 : port = 14#8
  · subst port
    iterate 4
      apply Reaches.prepend
      · simp [uxn_state, uxn_step, h1bc, h1bd, h1be, h1bf, h1c0, h1c1, h1c2, h1c3, h1c4, h1c5, h1c6, h1c7, h1c8, h1c9, h1ca, h1cb, h1cc, h1cd, h1ce, h1cf, h1d0, h1d1, h1d2, h1d3, h1d4, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1ea, h1eb, h1ec, h1ed, h1ee, h1ef, h1f0, h1f1, h1f2, h1f3, h1f4]
        rfl
    refine ⟨_, .refl _, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
    · simp
    · simp
    · simp
    · intro index below
      simp (disch := bv_omega) only [Function.update_of_ne]
  · have wide14 : ¬14#16 = port.setWidth 16 := by bv_omega
    by_cases p15 : port = 15#8
    · subst port
      iterate 8
        apply Reaches.prepend
        · simp [uxn_state, uxn_step, h1bc, h1bd, h1be, h1bf, h1c0, h1c1, h1c2, h1c3, h1c4, h1c5, h1c6, h1c7, h1c8, h1c9, h1ca, h1cb, h1cc, h1cd, h1ce, h1cf, h1d0, h1d1, h1d2, h1d3, h1d4, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1ea, h1eb, h1ec, h1ed, h1ee, h1ef, h1f0, h1f1, h1f2, h1f3, h1f4]
          rfl
      refine ⟨_, .refl _, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
      · simp
      · simp
      · simp
      · intro index below
        simp (disch := bv_omega) only [Function.update_of_ne]
    · have wide15 : ¬15#16 = port.setWidth 16 := by bv_omega
      by_cases p17 : port = 17#8
      · subst port
        iterate 12
          apply Reaches.prepend
          · simp [uxn_state, uxn_step, h1bc, h1bd, h1be, h1bf, h1c0, h1c1, h1c2, h1c3, h1c4, h1c5, h1c6, h1c7, h1c8, h1c9, h1ca, h1cb, h1cc, h1cd, h1ce, h1cf, h1d0, h1d1, h1d2, h1d3, h1d4, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1ea, h1eb, h1ec, h1ed, h1ee, h1ef, h1f0, h1f1, h1f2, h1f3, h1f4]
            rfl
        refine ⟨_, .refl _, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
        · simp
        · simp
        · simp
        · intro index below
          simp (disch := bv_omega) only [Function.update_of_ne]
      · have wide17 : ¬17#16 = port.setWidth 16 := by bv_omega
        by_cases p24 : port = 24#8
        · subst port
          iterate 16
            apply Reaches.prepend
            · simp [uxn_state, uxn_step, h1bc, h1bd, h1be, h1bf, h1c0, h1c1, h1c2, h1c3, h1c4, h1c5, h1c6, h1c7, h1c8, h1c9, h1ca, h1cb, h1cc, h1cd, h1ce, h1cf, h1d0, h1d1, h1d2, h1d3, h1d4, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1ea, h1eb, h1ec, h1ed, h1ee, h1ef, h1f0, h1f1, h1f2, h1f3, h1f4]
              rfl
          refine ⟨_, .refl _, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
          · simp
          · simp
          · simp
          · intro index below
            simp (disch := bv_omega) only [Function.update_of_ne]
        · have wide24 : ¬24#16 = port.setWidth 16 := by bv_omega
          by_cases p25 : port = 25#8
          · subst port
            iterate 20
              apply Reaches.prepend
              · simp [uxn_state, uxn_step, h1bc, h1bd, h1be, h1bf, h1c0, h1c1, h1c2, h1c3, h1c4, h1c5, h1c6, h1c7, h1c8, h1c9, h1ca, h1cb, h1cc, h1cd, h1ce, h1cf, h1d0, h1d1, h1d2, h1d3, h1d4, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1ea, h1eb, h1ec, h1ed, h1ee, h1ef, h1f0, h1f1, h1f2, h1f3, h1f4]
                rfl
            refine ⟨_, .refl _, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
            · simp
            · simp
            · simp
            · intro index below
              simp (disch := bv_omega) only [Function.update_of_ne]
          · have wide25 : ¬25#16 = port.setWidth 16 := by bv_omega
            iterate 20
              apply Reaches.prepend
              · simp [uxn_state, uxn_step, h1bc, h1bd, h1be, h1bf, h1c0, h1c1, h1c2, h1c3, h1c4, h1c5, h1c6, h1c7, h1c8, h1c9, h1ca, h1cb, h1cc, h1cd, h1ce, h1cf, h1d0, h1d1, h1d2, h1d3, h1d4, h1d5, h1d6, h1d7, h1d8, h1d9, h1da, h1db, h1dc, h1dd, h1de, h1df, h1e0, h1e1, h1e2, h1e3, h1e4, h1e5, h1e6, h1e7, h1e8, h1e9, h1ea, h1eb, h1ec, h1ed, h1ee, h1ef, h1f0, h1f1, h1f2, h1f3, h1f4, p14, wide14, p15, wide15, p17, wide17, p24, wide24, p25, wide25]
                rfl
            refine ⟨_, .refl _, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
            · simp [p14, p15, p17, p24, p25]
            · simp
            · simp
            · intro index below
              simp (disch := bv_omega) only [Function.update_of_ne]

end ProgramProofs.Uxnmin
