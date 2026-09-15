import Uxn.Uxn

namespace ProgramProofs.Host
open Uxn

/-- The VM stores a word high byte first. -/
theorem append_split (x : Word) : (x >>> 8).setWidth 8 ++ x.setWidth 8 = x := by
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb,
    BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 16)]
  exact BitVec.extractLsb'_append_extractLsb'

theorem join_bytes (a b : Byte) :
    b.setWidth 16 ||| (a.setWidth 16 <<< 8) = a ++ b := by
  simp only [BitVec.append_def, BitVec.setWidth'_eq, BitVec.shiftLeftZeroExtend_eq,
    BitVec.or_comm]

end ProgramProofs.Host
