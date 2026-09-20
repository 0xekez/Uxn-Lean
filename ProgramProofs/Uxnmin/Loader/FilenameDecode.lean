import ProgramProofs.Uxnmin.Rom
import ProgramProofs.Host.Reduction
import Init.Data.Range.Lemmas

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open private Uxn.Host.fileName from Uxn.Host

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- Reading a terminated, non-NUL byte sequence returns its UTF-8 decoding. -/
theorem fileName_of_bytes (mem : Memory) (bytes : List UInt8)
    (fits : bytes.length < 0x10000) (noNul : 0 ∉ bytes)
    (contents : ∀ i : Fin bytes.length,
      UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 i.val)) = bytes[i.val])
    (terminator : mem.ram (BitVec.ofNat 16 bytes.length) = 0) :
    Uxn.Host.fileName mem 0 = String.fromUTF8? bytes.toByteArray := by
  let step (i : Nat) (state : Option (Option String) × ByteArray) :
      Id (ForInStep (Option (Option String) × ByteArray)) :=
    if UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 i)) == 0 then
      pure (.done (some (String.fromUTF8? state.2), state.2))
    else pure (.yield (none, state.2.push (UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 i)))))
  have scan (bytes : List UInt8) (offset : Nat) (acc : ByteArray)
      (fits : offset + bytes.length < 0x10000) (noNul : 0 ∉ bytes)
      (contents : ∀ i : Fin bytes.length,
        UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 (offset + i.val))) = bytes[i.val])
      (terminator : mem.ram (BitVec.ofNat 16 (offset + bytes.length)) = 0) :
      forIn (List.range' offset (0x10000 - offset)) (none, acc) step =
        (some (String.fromUTF8? (List.toByteArray.loop bytes acc)), List.toByteArray.loop bytes acc) := by
    induction bytes generalizing offset acc with
    | nil =>
      have count : 0x10000 - offset = (0x10000 - (offset + 1)) + 1 := by simp at fits; omega
      rw [count, List.range'_succ, List.forIn_cons]
      simp [step, List.toByteArray.loop, uxn_state, show mem.ram (BitVec.ofNat 16 offset) = 0 by simpa using terminator]
    | cons byte bytes ih =>
      have count : 0x10000 - offset = (0x10000 - (offset + 1)) + 1 := by simp at fits; omega
      have head : UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 offset)) = byte := by
        simpa using contents ⟨0, by simp⟩
      have parts : byte ≠ 0 ∧ 0 ∉ bytes := by simpa [eq_comm] using noNul
      rw [count, List.range'_succ, List.forIn_cons]
      simp only [step, head, parts.1, beq_iff_eq, if_false, uxn_state]
      simpa [List.toByteArray.loop, step, uxn_state] using ih (offset + 1) (acc.push byte)
        (by simp at fits; omega) parts.2
        (fun i => by
          have h := contents ⟨i.val + 1, by simp⟩
          simpa [Nat.add_assoc, Nat.add_comm 1 i.val] using h)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using terminator)
  have result := scan bytes 0 ByteArray.empty (by simpa using fits) noNul
    (by simpa using contents) (by simpa using terminator)
  unfold Uxn.Host.fileName
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  change (forIn (List.range' 0 65536) (none, ByteArray.empty) step).fst.getD none = _
  rw [result]
  rfl

/-- A NUL-terminated copy of a String's bytes decodes back to that String. -/
theorem fileName_string (mem : Memory) (filename : String)
    (fits : filename.utf8ByteSize < 0x10000) (noNul : 0 ∉ filename.toUTF8.data)
    (contents : ∀ (i : Nat) (hi : i < filename.toUTF8.size),
      mem.ram (BitVec.ofNat 16 i) = (filename.toUTF8[i]'hi).toBitVec)
    (terminator : mem.ram (BitVec.ofNat 16 filename.utf8ByteSize) = 0) :
    Uxn.Host.fileName mem 0 = some filename := by
  have bytes_eq : filename.toUTF8.data.toList.toByteArray = filename.toUTF8 := by
    apply ByteArray.ext
    apply Array.ext'
    simp
  have decode : String.fromUTF8? filename.toUTF8 = some filename := by
    cases filename with
    | ofByteArray data valid => simp [String.fromUTF8?, String.toUTF8, String.fromUTF8, valid]
  rw [fileName_of_bytes mem filename.toUTF8.data.toList, bytes_eq, decode]
  · exact fits
  · simpa using noNul
  · intro i
    exact congrArg UInt8.ofBitVec (contents i.val i.isLt)
  · exact terminator

end ProgramProofs.Uxnmin
