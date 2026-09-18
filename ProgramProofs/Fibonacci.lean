-- The recursive Fibonacci ROM, proved by induction over finite executions.
import ProgramProofs.Fibonacci.Blocks
import ProgramProofs.Fibonacci.Tactics
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ClearExcept

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Fibonacci
open Uxn Uxn.Host ProgramProofs.Host ProgramProofs.Host.Stack Stack

/-- The bytes of `examples/binaries/fibonacci.rom`. -/
def rom : ByteArray :=
  ⟨#[0xa0, 0x01, 0x07, 0x80, 0x10, 0x37, 0x00, 0x80,
     0x17, 0x16, 0x80, 0x01, 0x09, 0x20, 0x00, 0x0e,
     0x80, 0x12, 0x16, 0x80, 0x00, 0x04, 0x60, 0x00,
     0x06, 0x80, 0x80, 0x80, 0x0f, 0x17, 0x00, 0xa0,
     0x00, 0x01, 0xaa, 0x20, 0x00, 0x02, 0x22, 0x6c,
     0xb9, 0x60, 0xff, 0xf3, 0x2f, 0x21, 0x39, 0x60,
     0xff, 0xed, 0x6f, 0x38, 0x6c, 0x00]⟩

run_cmd do
  unless (← IO.FS.readBinFile
      ((System.FilePath.mk (← Lean.getFileName)).parent.get! /
        ".." / "examples" / "binaries" / "fibonacci.rom")) == rom do
    throwError "Fibonacci ROM differs from ProgramProofs.Fibonacci.rom"

/-- Given a byte-value, n, between 0 and 24, the rom returns the nth
    Fibonacci number. Different values of n cause a stack overflow or
    other unspecified behavior. -/
theorem correct :
    ∃ final : Fin 25 → Uxn.Host.State,
    ∃ eof : Uxn.Host.State,
    ∃ onInvalid : Byte → IO (UInt32 × Uxn.Host.State),
      Uxn.Host.run rom =
        (do
          match (← (← IO.getStdin).read 1)[0]? with
          | none => pure (0, eof)
          | some b =>
            if h : b.toNat < 25 then pure (0, final ⟨b.toNat, h⟩)
            else onInvalid b.toBitVec) ∧
      eof.vm.mem.wstk.ptr = 0 ∧ eof.vm.mem.rstk.ptr = 0 ∧
      ∀ n : Fin 25,
        (final n).vm.mem.wstk.ptr = 2 ∧ (final n).vm.mem.rstk.ptr = 0 ∧
        ((final n).vm.mem.wstk.data 0 ++
          (final n).vm.mem.wstk.data 1).toNat = Nat.fib n.val := by
  -- Prove the recursive subroutine contract before assembling the host run.
  have fib_call (ram : Word → Byte) (hc : Code rom 54 ram)
      (n : Nat) (hn : n ≤ 24) (w r : List Byte) (address : Word)
      (hw : w.length + 4 * n + 8 < 256) (hr : r.length + 4 * n + 8 < 256) :
      Block ram 0x11f (w ++ bytes (BitVec.ofNat 16 n)) (r ++ bytes address)
        address (w ++ bytes (BitVec.ofNat 16 (Nat.fib n))) r := by
    have enter (ram : Word → Byte) (hc : Code rom 54 ram)
        (w r : List Byte) (x : Word) (hspace : w.length + 5 < 256) :
        Block ram 0x11f (w ++ bytes x) r
          (if (1 : Word) < x then 0x128 else 0x126) (w ++ bytes x ++ bytes 1) r := by
      have h := (Block.lit16 ram 0x11f (w ++ bytes x) r 1
        (hc ⟨31, by decide⟩) (hc ⟨32, by decide⟩) (hc ⟨33, by decide⟩)
        (by simpa [bytes] using (show w.length + 4 < 256 by omega))).trans
        ((Block.gth16k ram 0x122 w r x 1 (hc ⟨34, by decide⟩) hspace).trans
          (Block.jci ram 0x123 (w ++ bytes x ++ bytes 1) r
            (if (1 : Word) < x then 1 else 0) 2
            (hc ⟨35, by decide⟩) (hc ⟨36, by decide⟩) (hc ⟨37, by decide⟩)))
      split <;> rename_i hcmp
      · simp only [hcmp, if_true, show (1 : Byte) ≠ 0 by decide, if_false] at h
        simpa using h
      · simp only [hcmp, if_false, if_true] at h
        simpa using h

    have first_call (ram : Word → Byte) (hc : Code rom 54 ram)
        (w r : List Byte) (x : Word)
        (hw : w.length + 6 < 256) (hr : r.length + 2 < 256) :
        Block ram 0x128 (w ++ bytes x ++ bytes 1) r 0x11f
          (w ++ bytes x ++ bytes 1 ++ bytes (x - 1)) (r ++ bytes 0x12c) := by
      exact (Block.sub16k ram 0x128 w r x 1 (hc ⟨40, by decide⟩) hw).trans
        (Block.jsi ram 0x129 (w ++ bytes x ++ bytes 1 ++ bytes (x - 1)) r 0xfff3
          (hc ⟨41, by decide⟩) (hc ⟨42, by decide⟩) (hc ⟨43, by decide⟩) hr)

    have second_call (ram : Word → Byte) (hc : Code rom 54 ram)
        (w r : List Byte) (x a : Word)
        (hr : r.length + 4 < 256) :
        Block ram 0x12c (w ++ bytes x ++ bytes 1 ++ bytes a) r 0x11f
          (w ++ bytes (x - 2)) (r ++ bytes a ++ bytes 0x132) := by
      exact (Block.sth16 ram 0x12c (w ++ bytes x ++ bytes 1) r a
        (hc ⟨44, by decide⟩) (by omega)).trans
        ((Block.inc16 ram 0x12d (w ++ bytes x) (r ++ bytes a) 1
          (hc ⟨45, by decide⟩)).trans
          ((Block.sub16 ram 0x12e w (r ++ bytes a) x 2 (hc ⟨46, by decide⟩)).trans
            (Block.jsi ram 0x12f (w ++ bytes (x - 2)) (r ++ bytes a) 0xffed
              (hc ⟨47, by decide⟩) (hc ⟨48, by decide⟩) (hc ⟨49, by decide⟩)
              (by simpa [bytes] using hr))))

    have finish (ram : Word → Byte) (hc : Code rom 54 ram)
        (w r : List Byte) (a b address : Word) (hw : w.length + 4 < 256) :
        Block ram 0x132 (w ++ bytes b) (r ++ bytes address ++ bytes a)
          address (w ++ bytes (b + a)) r := by
      exact (Block.sth16r ram 0x132 (w ++ bytes b) (r ++ bytes address) a
        (hc ⟨50, by decide⟩) (by simpa [bytes] using hw)).trans
        ((Block.add16 ram 0x133 w (r ++ bytes address) b a (hc ⟨51, by decide⟩)).trans
          (Block.jmp16r ram 0x134 (w ++ bytes (b + a)) r address (hc ⟨52, by decide⟩)))

    induction n using Nat.strong_induction_on generalizing w r address with
    | h n ih =>
      have entry := enter ram hc w (r ++ bytes address) (BitVec.ofNat 16 n) (by omega)
      by_cases hb : n ≤ 1
      · have hcmp : ¬ (1 : Word) < BitVec.ofNat 16 n := by
          change ¬ 1 < n % 65536
          omega
        simp only [hcmp, if_false] at entry
        have hf : Nat.fib n = n := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp
        simpa only [hcmp, if_false, hf] using entry.trans
          ((Block.pop16 ram 0x126 (w ++ bytes (BitVec.ofNat 16 n)) (r ++ bytes address)
            1 (hc ⟨38, by decide⟩)).trans
            (Block.jmp16r ram 0x127 (w ++ bytes (BitVec.ofNat 16 n)) r address
              (hc ⟨39, by decide⟩)))
      · have hcmp : (1 : Word) < BitVec.ofNat 16 n := by
          change 1 < n % 65536
          omega
        simp only [hcmp, if_true] at entry
        have hsub1 : BitVec.ofNat 16 n - 1 = BitVec.ofNat 16 (n - 1) := by bv_omega
        have hsub2 : BitVec.ofNat 16 n - 2 = BitVec.ofNat 16 (n - 2) := by bv_omega
        have hsum : BitVec.ofNat 16 (Nat.fib (n - 2)) + BitVec.ofNat 16 (Nat.fib (n - 1)) =
            BitVec.ofNat 16 (Nat.fib n) := by
          rw [← BitVec.ofNat_add]
          congr 1
          have h := Nat.fib_add_two (n := n - 2)
          rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at h
          exact h.symm
        have first := ih (n - 1) (by omega) (by omega)
          (w ++ bytes (BitVec.ofNat 16 n) ++ bytes 1) (r ++ bytes address) 0x12c
          (by simp [bytes]; omega) (by simp [bytes]; omega)
        have second := ih (n - 2) (by omega) (by omega)
          w (r ++ bytes address ++ bytes (BitVec.ofNat 16 (Nat.fib (n - 1)))) 0x132
          (by omega) (by simp [bytes]; omega)
        have prepareFirst := first_call ram hc w (r ++ bytes address) (BitVec.ofNat 16 n)
          (by omega) (by simp [bytes]; omega)
        rw [hsub1] at prepareFirst
        have prepareSecond := second_call ram hc w (r ++ bytes address) (BitVec.ofNat 16 n)
          (BitVec.ofNat 16 (Nat.fib (n - 1))) (by simp [bytes]; omega)
        rw [hsub2] at prepareSecond
        have last := finish ram hc w r (BitVec.ofNat 16 (Nat.fib (n - 1)))
          (BitVec.ofNat 16 (Nat.fib (n - 2))) address (by omega)
        rw [hsum] at last
        simpa only [hcmp, if_true] using
          entry.trans (prepareFirst.trans (first.trans (prepareSecond.trans (second.trans last))))

  -- Install the input callback while preserving empty stacks.
  have boot (ram : Word → Byte) (hc : Code rom 54 ram) :
      ∃ final : Uxn.Host.State,
        evalLoop (.next (machine ram 0x100 Stack.empty Stack.empty))
          { vm := machine ram 0x100 Stack.empty Stack.empty } = pure ((), final) ∧
        final.consoleVector = 0x107 ∧ final.fuel = none ∧ final.read 0x0f = 0 ∧
        final.vm.mem.ram = ram ∧ Holds final.vm.mem.wstk [] ∧ Holds final.vm.mem.rstk [] := by
    clear * - ram hc
    dsimp [Stack.empty]
    iterate 5 host_step [Code.read hc, rom]
    refine ⟨_, rfl, ?_⟩
    simp only [and_true, true_and]
    refine ⟨?_, Holds.empty _ rfl, Holds.empty _ rfl⟩
    simp [Vector.get, Fin.cast, Array.getElem_set]

  -- An input event loads the argument and calls the recursive subroutine.
  have input_prefix (ram : Word → Byte) (hc : Code rom 54 ram)
      (n : Nat) (hn : n ≤ 24) (w r : Byte → Byte) (saved : Uxn.State)
      (ports : Vector Byte 256) (file : Uxn.Host.File) :
      ∃ sw sr,
        evalLoop (.next (machine ram 0x107 ⟨w, 0⟩ ⟨r, 0⟩))
          { vm := saved, ports := (ports.set 0x12 (BitVec.ofNat 8 n)).set 0x17 1,
            consoleVector := 0x107, file } =
        evalLoop (.next (machine ram 0x11f sw sr))
          { vm := saved, ports := (ports.set 0x12 (BitVec.ofNat 8 n)).set 0x17 1,
            consoleVector := 0x107, file } ∧
        Holds sw (bytes (BitVec.ofNat 16 n)) ∧ Holds sr (bytes 0x119) := by
    clear * - ram hc n hn w r saved ports file
    iterate 10 host_step [Code.read hc, rom]
    refine ⟨_, _, rfl, ?_, ?_⟩
    · constructor
      · simp [bytes]
      · simp [bytes]
      · intro i hi
        simp only [bytes, List.length_cons, List.length_nil] at hi
        interval_cases i <;> simp [bytes, Function.update_apply]
        all_goals apply BitVec.eq_of_toNat_eq
        all_goals simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        all_goals omega
    · constructor
      · simp [bytes]
      · simp [bytes]
      · intro i hi
        simp only [bytes, List.length_cons, List.length_nil] at hi
        interval_cases i <;> simp [bytes, Function.update_apply]

  let Finished (ram : Word → Byte) (x : Word) (s : Uxn.Host.State) : Prop :=
    s.vm.mem.ram = ram ∧ Holds s.vm.mem.wstk (bytes x) ∧ Holds s.vm.mem.rstk [] ∧
    s.consoleVector = 0x107 ∧ s.fuel = none ∧ s.read 0x0f = 0x80

  have halt (ram : Word → Byte) (hc : Code rom 54 ram)
      (x : Word) (w r : Byte → Byte) (hw : Holds ⟨w, 2⟩ (bytes x))
      (saved : Uxn.State) (ports : Vector Byte 256) (file : Uxn.Host.File) :
      ∃ final : Uxn.Host.State,
        evalLoop (.next (machine ram 0x119 ⟨w, 2⟩ ⟨r, 0⟩))
          { vm := saved, ports, consoleVector := 0x107, file } = pure ((), final) ∧
        Finished ram x final := by
    clear * - Finished ram hc x w r hw saved ports file
    iterate 5 host_step [Code.read hc, rom]
    refine ⟨_, rfl, rfl, ?_, Holds.empty _ rfl, rfl, rfl, ?_⟩
    · simpa [Stack.push, Stack.pop] using
        ((hw.push 0x80 (by simp [bytes])).push 0x0f (by simp [bytes])).pop.pop
    · simp [Uxn.Host.State.read, Vector.get, Fin.cast, Array.getElem_set]

  have end_event (ram : Word → Byte) (hc : Code rom 54 ram) (x : Word)
      (s : Uxn.Host.State) (hs : Finished ram x s) :
      ∃ final : Uxn.Host.State,
        run.consoleInput 10 4 s = pure ((), final) ∧ Finished ram x final := by
    clear * - Finished ram hc x s hs
    rcases s with ⟨⟨pc, ⟨ram', ⟨w, wp⟩, ⟨r, rp⟩⟩⟩, ports, vector, fuel, file⟩
    rcases hs with ⟨hram, hw, hr, hvector, hfuel, hhalt⟩
    dsimp at hram hvector hfuel
    subst ram' vector fuel
    have hpw : wp = 2 := hw.ptr_eq
    have hpr : rp = 0 := hr.ptr_eq
    subst wp rp
    simp only [run.consoleInput, eval]
    state_reduce
    dsimp [Uxn.Host.State.write]
    state_reduce
    iterate 7 host_step [Code.read hc, rom]
    refine ⟨_, rfl, rfl, ?_, Holds.empty _ rfl, rfl, rfl, ?_⟩
    · constructor
      · simp [bytes]
      · simp [bytes]
      · intro i hi
        have hi2 : i < 2 := by simpa [bytes] using hi
        interval_cases i <;> simpa [Function.update_apply] using hw.data_eq _ (by simp [bytes])
    · simpa [Uxn.Host.State.read, Vector.get, Fin.cast, Array.getElem_set] using hhalt

  have input_event (ram : Word → Byte) (hc : Code rom 54 ram) (n : Nat) (hn : n ≤ 24)
      (s : Uxn.Host.State) (hram : s.vm.mem.ram = ram)
      (hw : Holds s.vm.mem.wstk []) (hr : Holds s.vm.mem.rstk [])
      (hvector : s.consoleVector = 0x107) (hfuel : s.fuel = none) :
      ∃ final : Uxn.Host.State,
        run.consoleInput (BitVec.ofNat 8 n) 1 s = pure ((), final) ∧
        Finished ram (BitVec.ofNat 16 (Nat.fib n)) final := by
    rcases s with ⟨⟨pc, ⟨ram', ⟨w, wp⟩, ⟨r, rp⟩⟩⟩, ports, vector, fuel, file⟩
    dsimp at hram hvector hfuel
    subst ram' vector fuel
    have hpw : wp = 0 := hw.ptr_eq
    have hpr : rp = 0 := hr.ptr_eq
    subst wp rp
    obtain ⟨sw, sr, hprefix, hsw, hsr⟩ := input_prefix ram hc n hn w r
      (machine ram pc ⟨w, 0⟩ ⟨r, 0⟩) ports file
    obtain ⟨tw, tr, hsteps, htw, htr⟩ := fib_call ram hc n hn [] [] 0x119
      (by simp; omega) (by simp; omega) sw sr (by simpa using hsw) (by simpa using hsr)
    have heval := hsteps.evalLoop
      { vm := machine ram pc ⟨w, 0⟩ ⟨r, 0⟩,
        ports := (ports.set 0x12 (BitVec.ofNat 8 n)).set 0x17 1, consoleVector := 0x107, file } rfl
    simp only [run.consoleInput, eval]
    state_reduce
    dsimp [Uxn.Host.State.write]
    simp [machine] at hprefix heval
    state_reduce
    rw [hprefix, heval]
    rcases tw with ⟨tw, wp⟩
    rcases tr with ⟨tr, rp⟩
    have hpw : wp = 2 := htw.ptr_eq
    have hpr : rp = 0 := htr.ptr_eq
    subst wp rp
    exact halt ram hc (BitVec.ofNat 16 (Nat.fib n)) tw tr htw
      (machine ram pc ⟨w, 0⟩ ⟨r, 0⟩) ((ports.set 0x12 (BitVec.ofNat 8 n)).set 0x17 1) file

  have eof_event (ram : Word → Byte) (hc : Code rom 54 ram)
      (s : Uxn.Host.State) (hram : s.vm.mem.ram = ram)
      (hw : Holds s.vm.mem.wstk []) (hr : Holds s.vm.mem.rstk [])
      (hvector : s.consoleVector = 0x107) (hfuel : s.fuel = none)
      (hhalt : s.read 0x0f = 0) :
      ∃ final : Uxn.Host.State,
        run.consoleInput 10 4 s = pure ((), final) ∧
        final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 ∧
        final.read 0x0f = 0 := by
    clear * - ram hc s hram hw hr hvector hfuel hhalt
    rcases s with ⟨⟨pc, ⟨ram', ⟨w, wp⟩, ⟨r, rp⟩⟩⟩, ports, vector, fuel, file⟩
    dsimp at hram hvector hfuel
    subst ram' vector fuel
    have hpw : wp = 0 := hw.ptr_eq
    have hpr : rp = 0 := hr.ptr_eq
    subst wp rp
    simp only [run.consoleInput, eval]
    state_reduce
    dsimp [Uxn.Host.State.write]
    state_reduce
    iterate 7 host_step [Code.read hc, rom]
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    simpa [Uxn.Host.State.read, Vector.get, Fin.cast, Array.getElem_set] using hhalt

  let input : IO (Option UInt8) := do return (← (← IO.getStdin).read 1)[0]?
  have execution :
      ∃ afterRead : Option UInt8 → IO (UInt32 × Uxn.Host.State),
        Uxn.Host.run rom = (input >>= afterRead) ∧
        (∃ final : Uxn.Host.State, afterRead none = pure (0, final) ∧
          final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0) ∧
        ∀ (n : Nat) (_hn : n ≤ 24), ∃ final : Uxn.Host.State,
          afterRead (some (UInt8.ofNat n)) = pure (0, final) ∧
          final.vm.mem.wstk.ptr = 2 ∧ final.vm.mem.rstk.ptr = 0 ∧
          (final.vm.mem.wstk.data 0 ++ final.vm.mem.wstk.data 1).toNat = Nat.fib n := by
    let ram := (initialState rom).vm.mem.ram
    have hc : Code rom 54 ram := Code.initial rom 54 (by decide) (by decide)
    obtain ⟨started, hboot, hv, hf, hz, hram, hw, hr⟩ := boot ram hc
    simp at hf hv hz
    let finish : StateT Uxn.Host.State IO UInt32 := do
      run.consoleInput 10 4
      return ((← get).read 0x0f &&& 0x7f).toNat.toUInt32
    let afterRead (value : Option UInt8) : IO (UInt32 × Uxn.Host.State) :=
      (do
        match value with
        | none => pure ()
        | some b =>
          run.consoleInput b.toBitVec 1
          run.readConsole
        finish) started
    refine ⟨afterRead, ?_, ?_, ?_⟩
    · unfold run
      state_reduce
      simp only [Uxn.Host.State.write, Vector.set_replicate_self]
      rw [← initial_shape rom]
      dsimp [ram] at hboot
      simp only [Uxn.Host.State.write, Vector.set_replicate_self]
      simp [machine] at hboot ⊢
      rw [hboot]
      state_reduce
      simp only [hf, hv]
      dsimp
      simp only [run.consoleArgs]
      state_reduce
      rw [run.readConsole.eq_def]
      state_reduce
      simp only [hf, hz]
      dsimp
      simp only [uxn_state, bind_assoc, pure_bind]
      simp only [input, bind_assoc, pure_bind]
      apply congrArg (fun f => IO.getStdin.toEIO >>= f)
      funext stream
      apply congrArg (fun f => stream.read 1 >>= f)
      funext data
      cases data[0]? <;> dsimp [afterRead, finish] <;> state_reduce
    · obtain ⟨final, hend, hw, hr, hh⟩ := eof_event ram hc started hram hw hr hv hf hz
      refine ⟨final, ?_, hw, hr⟩
      dsimp [afterRead, finish]
      state_reduce
      simp at hend
      rw [hend]
      state_reduce
      simp at hh
      rw [hh]
      rfl
    · intro n hn
      obtain ⟨stopped, hinput, hs⟩ := input_event ram hc n hn started hram hw hr hv hf
      obtain ⟨final, hend, hfinal⟩ := end_event ram hc (BitVec.ofNat 16 (Nat.fib n)) stopped hs
      have ⟨_, hworking, hreturned, _, _, hh⟩ := hfinal
      refine ⟨final, ?_, hworking.ptr_eq, hreturned.ptr_eq, ?_⟩
      · dsimp [afterRead]
        state_reduce
        simp at hinput
        rw [show (UInt8.ofNat n).toBitVec = BitVec.ofNat 8 n by rfl, hinput]
        state_reduce
        rw [run.readConsole.eq_def]
        state_reduce
        have hsf := hs.2.2.2.2.1
        have hsh := hs.2.2.2.2.2
        simp at hsf hsh
        simp only [hsf, hsh]
        simp
        state_reduce
        dsimp [finish]
        state_reduce
        simp at hend
        rw [hend]
        state_reduce
        simp at hh
        rw [hh]
        rfl
      · have fib_fits : Nat.fib n < 65536 := by
          have h := Nat.fib_mono hn
          have h24 : Nat.fib 24 = 46368 := by norm_num [Nat.fib_add_two]
          omega
        have h0 := hworking.data_eq 0 (by simp [bytes])
        have h1 := hworking.data_eq 1 (by simp [bytes])
        simp only [bytes, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        simp [h0, h1, append_split, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fib_fits]
        rw [← BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 16) (Nat.fib n), append_split]
        exact Nat.mod_eq_of_lt fib_fits
  classical
  obtain ⟨afterRead, hrun, ⟨eof, heof, heofw, heofr⟩, hvalid⟩ := execution
  choose final hfinal using fun (n : Fin 25) => hvalid n.val (by omega)
  refine ⟨final, eof, fun b => afterRead (some (UInt8.ofBitVec b)), ?_,
    heofw, heofr, fun n => (hfinal n).2⟩
  rw [hrun]
  calc
    (input >>= afterRead) = (input >>= fun value =>
      match value with
      | none => pure (0, eof)
      | some b => if h : b.toNat < 25 then pure (0, final ⟨b.toNat, h⟩)
        else afterRead (some b)) := by
      apply congrArg (fun f => input >>= f)
      funext value
      cases value with
      | none => exact heof
      | some b =>
        dsimp
        split
        · rename_i h
          simpa using (hfinal ⟨b.toNat, h⟩).1
        · rfl
    _ = _ := by simp [input, bind_assoc]

end ProgramProofs.Fibonacci
