import ProgramProofs.Host.Host
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSimpArgs false
set_option maxRecDepth 3000
set_option maxHeartbeats 4000000

namespace ProgramProofs.Sierpinski

open Uxn Uxn.Host ProgramProofs.Host

/-- `examples/binaries/sierpinski.rom`, with its height byte set to `height`.
The supplied example has height 16. -/
def rom (height : Nat) : ByteArray :=
  ⟨#[0xe0, 0x0a, 0x18, 0xe0, 0x20, 0x18, 0xa0, UInt8.ofNat height,
     0x01, 0x19, 0x06, 0x81, 0xd7, 0x80, 0x01, 0x19,
     0x06, 0x20, 0xff, 0xf8, 0x9c, 0x66, 0x20, 0x00,
     0x02, 0x62, 0xfd, 0x57, 0xd7, 0x01, 0x98, 0x80,
     0xe5, 0x12, 0x0b, 0x20, 0xff, 0xee, 0x22, 0x67,
     0x57, 0x80, 0x01, 0x19, 0x81, 0x20, 0xff, 0xda,
     0x02, 0x62, 0x62, 0x00]⟩

def pascalTriangle (height : Nat) : String :=
  String.join ((List.range height).map fun n =>
    String.ofList (List.replicate (height - n) ' ') ++
    String.join ((List.range (n + 1)).map fun j =>
      if n.choose j % 2 = 1 then "* " else "  ") ++ "\n")

example : pascalTriangle 4 =
  "    * \n" ++
  "   * * \n" ++
  "  *   * \n" ++
  " * * * * \n" := by decide

/-- The ROM prints Pascal's triangle. -/
theorem correct (k : Nat) (hk : k < 8) :
    ∃ final,
      Uxn.Host.run (rom (2 ^ k)) =
        (do
          for byte in (pascalTriangle (2 ^ k)).toUTF8.data.toList do
            (← IO.getStdout).write ⟨#[byte]⟩
          pure (0, final)) := by
  have narrow_add (a b : Word) : (a + b).setWidth 8 = a.setWidth 8 + b.setWidth 8 :=
    BitVec.setWidth_add a b (by decide)
  have widen_lt (a b : Byte) : a.setWidth 16 < b.setWidth 16 ↔ a < b := by bv_omega
  have widen_le (a b : Byte) : a.setWidth 16 ≤ b.setWidth 16 ↔ a ≤ b := by bv_omega
  have write_overwrite (host : Uxn.Host.State) (port a b : Byte) :
      (host.write port a).write port b = host.write port b := by
    simp [Uxn.Host.State.write]

  -- At row n, the working-stack row value is height - n - 1. The
  -- return stack keeps the newline/port and space/port pairs throughout.
  let masks (r : Byte → Byte) : Prop := r 0 = 10 ∧ r 1 = 24 ∧ r 2 = 32 ∧ r 3 = 24

  let vm (ram : Word → Byte) (pc : Word) (ptr : Byte) (w r : Byte → Byte) : Uxn.State :=
    machine ram pc ⟨w, ptr⟩ ⟨r, 4⟩

  -- Each loop is equal to its remaining output followed by the next loop.
  let out (s : String) : IO Unit :=
    s.toUTF8.data.toList.forM fun byte => writeStdout byte.toBitVec

  let spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

  let cell (l i : Nat) : String := if (BitVec.ofNat 8 l &&& BitVec.ofNat 8 i) = 0 then "* " else "  "

  let cells (l start count : Nat) : String := String.join ((List.range' start count).map (cell l))

  let line (h n : Nat) : String := spaces (h - n) ++ cells (h - (n + 1)) 0 (n + 1) ++ "\n"

  let rows (h start count : Nat) : String := String.join ((List.range' start count).map (line h))

  have out_append (s t : String) : out (s ++ t) = (do out s; out t) := by
    simp [out, String.toByteArray_append, ByteArray.data_append, List.forM_append]

  have out_spaces_zero : out (spaces 0) = pure () := rfl

  have out_spaces_succ (n : Nat) : out (spaces (n + 1)) = (do writeStdout 32; out (spaces n)) := by
    dsimp only [spaces]
    rw [List.replicate_succ, String.ofList_cons, out_append]
    have h : out (String.singleton ' ') = writeStdout 32 := by
      change (do writeStdout 32; pure ()) = _
      simp
    rw [h]

  have cells_succ (l start count : Nat) : cells l start (count + 1) = cell l start ++ cells l (start + 1) count := by
    simp [cells, List.range'_succ, String.join_cons]

  have out_cell (l i : Nat) : out (cell l i) =
      (do writeStdout (if BitVec.ofNat 8 l &&& BitVec.ofNat 8 i = 0 then 42 else 32); writeStdout 32) := by
    unfold cell
    split
    · change (do writeStdout 42; writeStdout 32; pure ()) = _
      simp only [bind_pure_comp, id_map']
    · change (do writeStdout 32; writeStdout 32; pure ()) = _
      simp only [bind_pure_comp, id_map']

  have cells_zero (l i : Nat) : cells l i 0 = "" := by simp [cells, String.join_nil]

  have rows_succ (h start count : Nat) : rows h start (count + 1) = line h start ++ rows h (start + 1) count := by
    simp [rows, List.range'_succ, String.join_cons]

  have rows_zero (h start : Nat) : rows h start 0 = "" := by simp [rows, String.join_nil]

  have out_newline : out "\n" = writeStdout 10 := by
    change (do writeStdout 10; pure ()) = _
    simp

  -- First establish termination and the exact bitwise triangle for any positive
  -- height that fits in a byte.
  have run_triangle (h : Nat) (hpos : 0 < h) (hfit : h < 256) :
      ∃ final, Uxn.Host.run (rom h) =
        (do out (rows h 0 h); pure (0, final)) := by
    -- Induct on the number of rows left, composing padding, entries, and newline.
    have row_loop (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
        (n count : Nat) (hcount : 0 < count) (hsum : n + count = h) (hfit : h < 256)
        (w r : Byte → Byte) (hr : masks r) (hw : w 0 = BitVec.ofNat 8 (count - 1))
        (host : Uxn.Host.State) (hf : host.fuel = none) :
        ∃ finalVM,
          evalLoop (.next (vm ram 0x10a 1 w r)) host =
            (do out (rows h n count); pure ((), { host.write 24 10 with vm := finalVM })) := by
      have enter_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
          (l : Byte) (w r : Byte → Byte) (hw : w 0 = l)
          (host : Uxn.Host.State) (hf : host.fuel = none) :
          ∃ w',
            evalLoop (.next (vm ram 0x10a 1 w r)) host =
              evalLoop (.next (vm ram 0x10c 3 w' r)) host ∧
            w' 0 = l ∧ w' 1 = l ∧ w' 2 = l + 1 := by
        simp at hw
        refine ⟨?_, ?_, ?_⟩
        rotate_left 1
        · symbolic_steps 2 hf [narrow_add, vm, Code.read hc, rom, hw]
          simp [vm, machine]
          rfl
        · simp [hw]

      -- DEOkr emits a space; SUB/DUP/JCI count down the padding.
      have pad_loop (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
          (l : Byte) (p : Nat) (hp : 0 < p) (hpfit : p < 256)
          (w r : Byte → Byte) (hr : masks r)
          (hw0 : w 0 = l) (hw1 : w 1 = l) (hw2 : w 2 = BitVec.ofNat 8 p)
          (host : Uxn.Host.State) (hf : host.fuel = none) :
          ∃ w',
            evalLoop (.next (vm ram 0x10c 3 w r)) host =
              (do out (spaces p)
                  evalLoop (.next (vm ram 0x114 3 w' r)) (host.write 24 32)) ∧
            w' 0 = l ∧ w' 1 = l ∧ w' 2 = 0 := by
        have pad_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
            (l p : Byte) (w r : Byte → Byte) (hr : masks r)
            (hw0 : w 0 = l) (hw1 : w 1 = l) (hw2 : w 2 = p)
            (host : Uxn.Host.State) (hf : host.fuel = none) :
            ∃ w',
              evalLoop (.next (vm ram 0x10c 3 w r)) host =
                (do writeStdout 32
                    evalLoop
                      (.next (vm ram (if p - 1 = 0 then 0x114 else 0x10c) 3 w' r))
                      (host.write 24 32)) ∧
              w' 0 = l ∧ w' 1 = l ∧ w' 2 = p - 1 := by
          rcases hr with ⟨hr0, hr1, hr2, hr3⟩
          simp at hr0 hr1 hr2 hr3 hw0 hw1 hw2
          refine ⟨Function.update (Function.update (Function.update w 3 1) 2 (p - 1)) 3 (p - 1), ?_, ?_⟩
          · symbolic_steps 5 hf [respond, deo_stdout, narrow_add, vm, Code.read hc, rom, hr0, hr1, hr2, hr3, hw0, hw1,
              hw2]
            simp only [BitVec.sub_eq_add_neg]
            split <;> rename_i hz <;>
              simp [uxn_state, uxn_step, narrow_add, vm, Code.read hc, rom, hz, writeStdout, bind_assoc]
          · simp [hw0, hw1, BitVec.sub_eq_add_neg]

        induction p generalizing w host with
        | zero => omega
        | succ p ih =>
          obtain ⟨w', hs, h0, h1, h2⟩ := pad_step h ram hc l (BitVec.ofNat 8 (p + 1)) w r hr hw0 hw1 hw2 host hf
          have hsub : BitVec.ofNat 8 (p + 1) - 1 = BitVec.ofNat 8 p := by bv_omega
          rw [hsub] at hs h2
          by_cases hz : p = 0
          · subst p
            refine ⟨w', ?_, h0, h1, h2⟩
            simpa [out_spaces_succ, out_spaces_zero] using hs
          · have hbyte : BitVec.ofNat 8 p ≠ 0 := by bv_omega
            rw [if_neg hbyte] at hs
            obtain ⟨w'', hrun, h0', h1', h2'⟩ := ih (by omega) (by omega) w' h0 h1 h2
              (host.write 24 32) hf
            refine ⟨w'', ?_, h0', h1', h2'⟩
            rw [hs, hrun]
            simp only [write_overwrite, out_spaces_succ, bind_assoc, pure_bind]

      -- ANDk selects the entry; INC/ADDk/LDR/LTH advance through the row.
      have fill_loop (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
          (l i count : Nat) (hcount : 0 < count) (hsum : l + i + count = h) (hfit : h < 256)
          (w r : Byte → Byte) (hr : masks r)
          (hw0 : w 0 = BitVec.ofNat 8 l) (hw1 : w 1 = BitVec.ofNat 8 l)
          (hw2 : w 2 = BitVec.ofNat 8 i)
          (host : Uxn.Host.State) (hf : host.fuel = none) :
          ∃ w' r',
            evalLoop (.next (vm ram 0x114 3 w r)) host =
              (do out (cells l i count)
                  evalLoop (.next (vm ram 0x126 3 w' r')) (host.write 24 32)) ∧
            (w' 0 = BitVec.ofNat 8 l ∧ w' 1 = BitVec.ofNat 8 l ∧ w' 2 = BitVec.ofNat 8 (i + count)) ∧
            masks r' := by
        have emit_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
            (l i : Byte) (w r : Byte → Byte) (hr : masks r)
            (hw0 : w 0 = l) (hw1 : w 1 = l) (hw2 : w 2 = i)
            (host : Uxn.Host.State) (hf : host.fuel = none) :
            ∃ w' r',
              evalLoop (.next (vm ram 0x114 3 w r)) host =
                (do writeStdout (if l &&& i = 0 then 42 else 32)
                    writeStdout 32
                    evalLoop (.next (vm ram 0x11d 3 w' r')) (host.write 24 32)) ∧
              (w' 0 = l ∧ w' 1 = l ∧ w' 2 = i) ∧ masks r' := by
          rcases hr with ⟨hr0, hr1, hr2, hr3⟩
          simp at hr0 hr1 hr2 hr3 hw0 hw1 hw2
          by_cases hz : l &&& i = 0
          · simp at hz
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            rotate_left 2
            · symbolic_steps 7 hf [respond, deo_stdout, narrow_add, vm, Code.read hc, rom, hr0, hr1, hr2, hr3, hw0, hw1,
                hw2, BitVec.and_comm, hz]
              simp [vm, machine, hz, write_overwrite, writeStdout, bind_assoc]
              rfl
            · simp [hw0, hw1, hw2]
            · simp [masks, hr0, hr1, hr2, hr3]
          · simp at hz
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            rotate_left 2
            · symbolic_steps 5 hf [respond, deo_stdout, narrow_add, vm, Code.read hc, rom, hr0, hr1, hr2, hr3, hw0, hw1,
                hw2, BitVec.and_comm, hz]
              simp [vm, machine, hz, write_overwrite, writeStdout, bind_assoc]
              rfl
            · simp [hw0, hw1, hw2]
            · simp [masks, hr0, hr1, hr2, hr3]

        have advance_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
            (l i : Byte) (w r : Byte → Byte)
            (hw0 : w 0 = l) (hw1 : w 1 = l) (hw2 : w 2 = i)
            (host : Uxn.Host.State) (hf : host.fuel = none) :
            ∃ w',
              evalLoop (.next (vm ram 0x11d 3 w r)) host =
                evalLoop
                  (.next (vm ram (if l + (i + 1) < BitVec.ofNat 8 h then 0x114 else 0x126) 3 w' r))
                  host ∧
              w' 0 = l ∧ w' 1 = l ∧ w' 2 = i + 1 := by
          simp at hw0 hw1 hw2
          by_cases hc' : l + (i + 1#8) < BitVec.ofNat 8 h
          all_goals
            refine ⟨?_, ?_, ?_⟩
            rotate_left 1
            · symbolic_steps 6 hf [narrow_add, vm, Code.read hc, rom, hw0, hw1, hw2, widen_lt,
                widen_le, UInt8.toBitVec_ofNat', BitVec.add_comm, hc']
              simp [vm, machine, BitVec.add_assoc, BitVec.add_comm, hc']
              rfl
            · simp [hw0, hw1, hw2]

        induction count generalizing i w r host with
        | zero => omega
        | succ count ih =>
          obtain ⟨we, re, he, ⟨he0, he1, he2⟩, her⟩ :=
            emit_step h ram hc (BitVec.ofNat 8 l) (BitVec.ofNat 8 i) w r hr hw0 hw1 hw2 host hf
          obtain ⟨wa, ha, ha0, ha1, ha2⟩ := advance_step h ram hc (BitVec.ofNat 8 l) (BitVec.ofNat 8 i)
            we re he0 he1 he2 (host.write 24 32) hf
          have hi' : BitVec.ofNat 8 i + 1 = BitVec.ofNat 8 (i + 1) := by rw [BitVec.ofNat_add]; rfl
          rw [hi'] at ha2
          by_cases hz : count = 0
          · rcases hz with rfl
            have hcmp : ¬ BitVec.ofNat 8 l + (BitVec.ofNat 8 i + 1) < BitVec.ofNat 8 h := by bv_omega
            rw [if_neg hcmp] at ha
            refine ⟨wa, re, ?_, ⟨ha0, ha1, ha2⟩, her⟩
            rw [he, ha]
            simp only [cells_succ, cells_zero, String.append_empty, out_cell, bind_assoc]
          · have hcmp : BitVec.ofNat 8 l + (BitVec.ofNat 8 i + 1) < BitVec.ofNat 8 h := by bv_omega
            rw [if_pos hcmp] at ha
            obtain ⟨w', r', hrun, hw', hr'⟩ := ih (i + 1) (by omega) (by omega) wa re her ha0 ha1 ha2
              (host.write 24 32) hf
            refine ⟨w', r', ?_, ?_, hr'⟩
            · rw [he, ha, hrun]
              simp only [write_overwrite, cells_succ, out_append, out_cell, bind_assoc, pure_bind]
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw'

      have newline_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
          (w r : Byte → Byte) (hr : masks r)
          (host : Uxn.Host.State) (hf : host.fuel = none) :
          ∃ r',
            evalLoop (.next (vm ram 0x126 3 w r)) host =
              (do writeStdout 10
                  evalLoop (.next (vm ram 0x129 1 w r')) (host.write 24 10)) ∧ masks r' := by
        rcases hr with ⟨hr0, hr1, hr2, hr3⟩
        simp at hr0 hr1 hr2 hr3
        refine ⟨?_, ?_, ?_⟩
        rotate_left 1
        · symbolic_steps 3 hf [respond, deo_stdout, narrow_add, vm, Code.read hc, rom, hr0, hr1, hr2, hr3]
          simp [vm, machine, writeStdout, bind_assoc]
          rfl
        · simp [masks, hr0, hr1, hr2, hr3]

      have next_row_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
          (l : Byte) (w r : Byte → Byte) (hw : w 0 = l)
          (host : Uxn.Host.State) (hf : host.fuel = none) :
          ∃ w',
            evalLoop (.next (vm ram 0x129 1 w r)) host =
              evalLoop
                (.next (vm ram (if l = 0 then 0x130 else 0x10a) 1 w' r)) host ∧
            w' 0 = l - 1 := by
        simp at hw
        by_cases hz : l = 0#8
        all_goals
          refine ⟨?_, ?_, ?_⟩
          rotate_left 1
          · symbolic_steps 4 hf [narrow_add, vm, Code.read hc, rom, hw, hz]
            simp [vm, machine, hz]
            rfl
          · simp [hw, hz, BitVec.sub_eq_add_neg]

      have stop_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
          (w r : Byte → Byte) (host : Uxn.Host.State)
          (hf : host.fuel = none) :
          evalLoop (.next (vm ram 0x130 1 w r)) host =
            pure ((), { host with vm := machine ram 0x134 ⟨w, 0⟩ ⟨r, 0⟩ }) := by
        symbolic_steps 4 hf [narrow_add, vm, Code.read hc, rom]
        rw [evalLoop.eq_def]
        rfl

      induction count generalizing n w r host with
      | zero => omega
      | succ count ih =>
        obtain ⟨we, he, he0, he1, he2⟩ := enter_step h ram hc (BitVec.ofNat 8 count) w r hw host hf
        have hinc : BitVec.ofNat 8 count + 1 = BitVec.ofNat 8 (count + 1) := by rw [BitVec.ofNat_add]; rfl
        rw [hinc] at he2
        obtain ⟨wp, hp, hp0, hp1, hp2⟩ := pad_loop h ram hc (BitVec.ofNat 8 count) (count + 1)
          (by omega) (by omega) we r hr he0 he1 he2 host hf
        obtain ⟨wf, rf, hfill, ⟨hf0, hf1, hf2⟩, hfr⟩ := fill_loop h ram hc count 0 (h - count)
          (by omega) (by omega) hfit wp r hr hp0 hp1 hp2
          (host.write 24 32) hf
        obtain ⟨rn, hn, hnr⟩ := newline_step h ram hc wf rf hfr
          ((host.write 24 32).write 24 32) hf
        obtain ⟨wn, ha, hwa⟩ := next_row_step h ram hc (BitVec.ofNat 8 count) wf rn hf0
          (((host.write 24 32).write 24 32).write 24 10) hf
        have hspace : h - n = count + 1 := by omega
        have hlength : h - (n + 1) = count := by omega
        have hwidth : h - count = n + 1 := by omega
        by_cases hz : count = 0
        · rcases hz with rfl
          rw [if_pos (show (0#8) = (0 : Byte) from rfl)] at ha
          refine ⟨machine ram 0x134 ⟨wn, 0⟩ ⟨rn, 0⟩, ?_⟩
          rw [he, hp, hfill, hn, ha, stop_step h ram hc wn rn
            (((host.write 24 32).write 24 32).write 24 10) hf]
          simp only [write_overwrite, rows_succ, rows_zero, String.append_empty, line,
            hspace, hlength, hwidth, out_append, out_newline, bind_assoc]
        · have hbyte : BitVec.ofNat 8 count ≠ 0 := by bv_omega
          rw [if_neg hbyte] at ha
          have hsub : BitVec.ofNat 8 count - 1 = BitVec.ofNat 8 (count - 1) := by bv_omega
          rw [hsub] at hwa
          obtain ⟨finalVM, hrun⟩ := ih (n + 1) (by omega) (by omega) wn rn hnr hwa
            (((host.write 24 32).write 24 32).write 24 10) hf
          refine ⟨finalVM, ?_⟩
          rw [he, hp, hfill, hn, ha, hrun]
          simp only [write_overwrite, rows_succ, line, hspace, hlength, hwidth,
            out_append, out_newline, bind_assoc, pure_bind]

    have boot_step (h : Nat) (ram : Word → Byte) (hc : Code (rom h) 52 ram)
        (host : Uxn.Host.State) (hf : host.fuel = none) :
        ∃ w r,
          evalLoop (.next (machine ram 0x100 Stack.empty Stack.empty)) host =
            evalLoop (.next (vm ram 0x10a 1 w r)) host ∧
          w 0 = BitVec.ofNat 8 h - 1 ∧ masks r := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      rotate_left 2
      · symbolic_steps 4 hf [narrow_add, vm, Code.read hc, rom, UInt8.toBitVec_ofNat']
        simp [vm, machine]
        rfl
      · simp [BitVec.sub_eq_add_neg]
      · simp [masks]

    let ram := (initialState (rom h)).vm.mem.ram
    have hc : Code (rom h) 52 ram := Code.initial (rom h) 52 (by change 52 ≤ (rom h).data.size; simp [rom]) (by decide)
    let host : Uxn.Host.State := { vm := machine ram 0 Stack.empty Stack.empty }
    obtain ⟨w, r, hboot, hw, hr⟩ := boot_step h ram hc host rfl
    have hsub : BitVec.ofNat 8 h - 1 = BitVec.ofNat 8 (h - 1) := by bv_omega
    rw [hsub] at hw
    obtain ⟨finalVM, hrun⟩ := row_loop h ram hc 0 h hpos (by omega) hfit w r hr hw host rfl
    let final : Uxn.Host.State := { host.write 24 10 with vm := finalVM }
    have hboot' :
        evalLoop (.next (machine ram 0x100 Stack.empty Stack.empty)) host =
          (do out (rows h 0 h); pure ((), final)) := by
      rw [hboot, hrun]
    have hv : final.consoleVector = 0#16 := rfl
    have hh : final.read 0x0f#8 = 0#8 := by
      simp [final, host, Uxn.Host.State.read, Uxn.Host.State.write,
        Vector.get, Fin.cast, Array.getElem_set]
    refine ⟨final, ?_⟩
    apply run_of_evalLoop (rom h) final _ ?_ hv hh
    rw [← initial_shape (rom h)]
    exact hboot'

  -- Lucas's theorem: n.choose j is odd exactly when every set bit of j is set in n.
  -- Below 2 ^ k, height - n - 1 is n's k-bit complement, exactly the ROM's mask.
  have rows_pascal (k : Nat) (hk : k < 8) : rows (2 ^ k) 0 (2 ^ k) = pascalTriangle (2 ^ k) := by
    have choose_odd_complement (k n j : Nat) (hn : n < 2 ^ k) (hj : j < 2 ^ k) :
        n.choose j % 2 = 1 ↔ (2 ^ k - (n + 1)) &&& j = 0 := by
      have choose_odd_iff (n j : Nat) : n.choose j % 2 = 1 ↔ n &&& j = j := by
        induction n using Nat.strong_induction_on generalizing j with
        | h n ih =>
          by_cases hn : n = 0
          · subst n
            cases j <;> simp
          have ih := ih (n / 2) (by omega) (j / 2)
          have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := n) (k := j)
          change n.choose j % 2 = _ at lucas
          have hd := Nat.and_div_two (a := n) (b := j)
          have hm := Nat.and_mod_two_pow (a := n) (b := j) (n := 1)
          change (n &&& j) % 2 = (n % 2) &&& (j % 2) at hm
          have heq : n &&& j = j ↔ (n % 2) &&& (j % 2) = j % 2 ∧
              n / 2 &&& j / 2 = j / 2 := by omega
          rw [lucas, heq, ← ih, Nat.mul_mod]
          have hn2 : n % 2 < 2 := Nat.mod_lt _ (by decide)
          have hj2 : j % 2 < 2 := Nat.mod_lt _ (by decide)
          interval_cases hn' : n % 2 <;> interval_cases hj' : j % 2 <;> simp

      rw [choose_odd_iff, Nat.eq_iff_testBit_eq, Nat.eq_iff_testBit_eq]
      apply forall_congr'
      intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_succ hn, Nat.testBit_zero]
      by_cases hi : i < k
      · cases n.testBit i <;> cases j.testBit i <;> simp [hi]
      · have hj' : j.testBit i = false := Nat.testBit_eq_false_of_lt
            (hj.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hi, hj']

    have hfit : 2 ^ k < 256 := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) (show k ≤ 7 by omega)
      omega
    unfold rows pascalTriangle
    rw [← List.range_eq_range']
    apply congrArg String.join
    apply List.map_congr_left
    intro n hn
    simp only [List.mem_range] at hn
    change spaces (2 ^ k - n) ++ cells (2 ^ k - (n + 1)) 0 (n + 1) ++ "\n" = _
    apply congrArg (fun s => spaces (2 ^ k - n) ++ s ++ "\n")
    unfold cells
    rw [← List.range_eq_range']
    apply congrArg String.join
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    have hl : 2 ^ k - (n + 1) < 256 := by omega
    have hjfit : j < 256 := by omega
    have hb : (BitVec.ofNat 8 (2 ^ k - (n + 1)) &&& BitVec.ofNat 8 j = 0) ↔
        (2 ^ k - (n + 1)) &&& j = 0 := by
      rw [← BitVec.toNat_inj]
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl,
        Nat.mod_eq_of_lt hjfit, BitVec.toNat_zero]
      rfl
    unfold cell
    exact if_congr (hb.trans (choose_odd_complement k n j hn (by omega)).symm) rfl rfl

  have hfit : 2 ^ k < 256 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k ≤ 7 by omega)
    omega
  have forM_eq_loop {α : Type} (xs : List α) (f : α → IO Unit) :
      forM xs f = (do for x in xs do f x) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.forM_cons, ih]
  obtain ⟨final, hrun⟩ := run_triangle (2 ^ k) (Nat.two_pow_pos k) hfit
  refine ⟨final, ?_⟩
  rw [hrun, rows_pascal k hk]
  dsimp only [out]
  rw [List.forM_eq_forM, forM_eq_loop]
  simp only [bind_assoc, pure_bind]
  rfl

run_cmd do
  unless (← IO.FS.readBinFile
      ((System.FilePath.mk (← Lean.getFileName)).parent.get! /
        ".." / "examples" / "binaries" / "sierpinski.rom")) == rom 16 do
    throwError "Sierpiński ROM differs from ProgramProofs.Sierpinski.rom 16"

end ProgramProofs.Sierpinski
