-- Live-stack contracts used by the recursive Fibonacci proof.
import ProgramProofs.Host.Execution

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ProgramProofs.Fibonacci
open Uxn Uxn.Host ProgramProofs.Host

namespace Stack
open ProgramProofs.Host.Stack

def pop (s : Uxn.Stack) : Uxn.Stack := { s with ptr := s.ptr - 1 }

def peek (s : Uxn.Stack) : Byte := s.data (s.ptr - 1)

def bytes (x : Word) : List Byte := [(x >>> 8).setWidth 8, x.setWidth 8]

def popWord (s : Uxn.Stack) : Uxn.Stack := pop (pop s)

def peekWord (s : Uxn.Stack) : Word := peek (pop s) ++ peek s

/-- Only the live bottom-to-top bytes are specified; popped cells are unrestricted. -/
structure Holds (s : Uxn.Stack) (xs : List Byte) : Prop where
  length_lt : xs.length < 256
  ptr_eq : s.ptr = BitVec.ofNat 8 xs.length
  data_eq : ∀ i (hi : i < xs.length), s.data (BitVec.ofNat 8 i) = xs[i]

theorem Holds.empty (s : Uxn.Stack) (h : s.ptr = 0) : Holds s [] :=
  ⟨by simp, h, by simp⟩

theorem Holds.push {s : Uxn.Stack} {xs : List Byte} (h : Holds s xs)
    (b : Byte) (hb : xs.length + 1 < 256) : Holds (push s b) (xs ++ [b]) := by
  constructor
  · simpa using hb
  · simp [ProgramProofs.Host.Stack.push, h.ptr_eq, BitVec.ofNat_add]
  · intro i hi
    by_cases he : i = xs.length
    · subst i
      simp [ProgramProofs.Host.Stack.push, h.ptr_eq]
    · have hil : i < xs.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      have hne : BitVec.ofNat 8 i ≠ BitVec.ofNat 8 xs.length := by
        intro heq
        have := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [ProgramProofs.Host.Stack.push, h.ptr_eq, Function.update_of_ne hne, h.data_eq i hil,
        List.getElem_append_left hil]

theorem Holds.peek {s : Uxn.Stack} {xs : List Byte} {b : Byte}
    (h : Holds s (xs ++ [b])) : peek s = b := by
  have hp : s.ptr - 1 = BitVec.ofNat 8 xs.length := by
    rw [h.ptr_eq]
    simp [BitVec.ofNat_add, BitVec.add_sub_cancel]
  change s.data (s.ptr - 1) = b
  rw [hp]
  simpa using h.data_eq xs.length (by simp)

theorem Holds.pop {s : Uxn.Stack} {xs : List Byte} {b : Byte}
    (h : Holds s (xs ++ [b])) : Holds (pop s) xs := by
  constructor
  · have := h.length_lt; simp only [List.length_append, List.length_singleton] at this; omega
  · simp [ProgramProofs.Fibonacci.Stack.pop, h.ptr_eq, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · intro i hi
    exact (h.data_eq i (by simp; omega)).trans (List.getElem_append_left hi)

theorem Holds.pushWord {s : Uxn.Stack} {xs : List Byte} (h : Holds s xs)
    (x : Word) (hx : xs.length + 2 < 256) : Holds (pushWord s x) (xs ++ bytes x) := by
  simpa [ProgramProofs.Host.Stack.pushWord, bytes, List.append_assoc] using
    (h.push ((x >>> 8).setWidth 8) (by omega)).push (x.setWidth 8) (by simp; omega)

theorem Holds.popWord {s : Uxn.Stack} {xs : List Byte} {x : Word}
    (h : Holds s (xs ++ bytes x)) : Holds (popWord s) xs := by
  unfold bytes at h
  have h' : Holds s ((xs ++ [(x >>> 8).setWidth 8]) ++ [x.setWidth 8]) := by
    simpa [List.append_assoc] using h
  exact h'.pop.pop

theorem Holds.peekWord {s : Uxn.Stack} {xs : List Byte} {x : Word}
    (h : Holds s (xs ++ bytes x)) : peekWord s = x := by
  have h' : Holds s ((xs ++ [(x >>> 8).setWidth 8]) ++ [x.setWidth 8]) := by
    simpa [bytes, List.append_assoc] using h
  rw [ProgramProofs.Fibonacci.Stack.peekWord, h'.peek, h'.pop.peek, append_split]

end Stack

attribute [local uxn_step] Stack.pop Stack.peek Stack.popWord Stack.peekWord

/-- Reduce a VM instruction using its byte hypotheses and the shared execution rules. -/
local macro "reduce_step" : tactic => `(tactic| (
  all_goals try simp only [Stack.peekWord, Stack.popWord, Stack.pop, Stack.peek] at *
  all_goals simp [uxn_state, uxn_step, *]
  all_goals simp_all [uxn_state, uxn_step]
  all_goals try simp [← BitVec.add_assoc]))

/-- A finite block contract, with live stacks listed bottom to top. -/
def Block (ram : Word → Byte) (pc : Word) (w r : List Byte)
    (pc' : Word) (w' r' : List Byte) : Prop :=
  ∀ sw sr, Stack.Holds sw w → Stack.Holds sr r →
    ∃ tw tr, Reaches (machine ram pc sw sr) (machine ram pc' tw tr) ∧
      Stack.Holds tw w' ∧ Stack.Holds tr r'

theorem Block.trans {ram : Word → Byte} {pc pc' pc'' : Word}
    {w r w' r' w'' r'' : List Byte}
    (h : Block ram pc w r pc' w' r') (k : Block ram pc' w' r' pc'' w'' r'') :
    Block ram pc w r pc'' w'' r'' := by
  intro sw sr hw hr
  obtain ⟨tw, tr, hsteps, hw', hr'⟩ := h sw sr hw hr
  obtain ⟨uw, ur, ksteps, hw'', hr''⟩ := k tw tr hw' hr'
  exact ⟨uw, ur, hsteps.trans ksteps, hw'', hr''⟩

namespace Block
open Uxn Stack ProgramProofs.Host.Stack

variable (ram : Word → Byte) (pc : Word) (w r : List Byte)

theorem lit16 (x : Word) (h0 : ram pc = 0xa0)
    (h1 : ram (pc + 1) = (x >>> 8).setWidth 8) (h2 : ram (pc + 2) = x.setWidth 8)
    (hspace : w.length + 2 < 256) :
    Block ram pc w r (pc + 3) (w ++ bytes x) r := by
  intro sw sr hw hr
  exact ⟨pushWord sw x, sr, .next (by reduce_step) (.refl _),
    hw.pushWord x hspace, hr⟩

theorem pop16 (x : Word) (h0 : ram pc = 0x22) :
    Block ram pc (w ++ bytes x) r (pc + 1) w r := by
  intro sw sr hw hr
  exact ⟨popWord sw, sr, .next (by reduce_step) (.refl _), hw.popWord, hr⟩

theorem add16 (a b : Word) (h0 : ram pc = 0x38) :
    Block ram pc (w ++ bytes a ++ bytes b) r (pc + 1) (w ++ bytes (a + b)) r := by
  intro sw sr hw hr
  refine ⟨pushWord (popWord (popWord sw)) (a + b), sr, .next ?_ (.refl _),
    hw.popWord.popWord.pushWord _ ?_, hr⟩
  · have ha := hw.popWord.peekWord
    have hb := hw.peekWord
    reduce_step
    simp [BitVec.add_comm]
  · have := hw.length_lt
    simp only [List.length_append, bytes, List.length_cons, List.length_nil] at this
    omega

theorem sub16 (a b : Word) (h0 : ram pc = 0x39) :
    Block ram pc (w ++ bytes a ++ bytes b) r (pc + 1) (w ++ bytes (a - b)) r := by
  intro sw sr hw hr
  refine ⟨pushWord (popWord (popWord sw)) (a - b), sr, .next ?_ (.refl _),
    hw.popWord.popWord.pushWord _ ?_, hr⟩
  · have ha := hw.popWord.peekWord
    have hb := hw.peekWord
    reduce_step
  · have := hw.length_lt
    simp only [List.length_append, bytes, List.length_cons, List.length_nil] at this
    omega

theorem sub16k (a b : Word) (h0 : ram pc = 0xb9) (hspace : w.length + 6 < 256) :
    Block ram pc (w ++ bytes a ++ bytes b) r (pc + 1)
      (w ++ bytes a ++ bytes b ++ bytes (a - b)) r := by
  intro sw sr hw hr
  refine ⟨pushWord sw (a - b), sr, .next ?_ (.refl _), hw.pushWord _ ?_, hr⟩
  · have ha := hw.popWord.peekWord
    have hb := hw.peekWord
    reduce_step
  · simpa [bytes] using hspace

theorem inc16 (a : Word) (h0 : ram pc = 0x21) :
    Block ram pc (w ++ bytes a) r (pc + 1) (w ++ bytes (a + 1)) r := by
  intro sw sr hw hr
  refine ⟨pushWord (popWord sw) (a + 1), sr, .next ?_ (.refl _), hw.popWord.pushWord _ ?_, hr⟩
  · have hx := hw.peekWord
    reduce_step
  · simpa [bytes] using hw.length_lt

theorem gth16k (a b : Word) (h0 : ram pc = 0xaa) (hspace : w.length + 5 < 256) :
    Block ram pc (w ++ bytes a ++ bytes b) r (pc + 1)
      ((w ++ bytes a ++ bytes b) ++ [if b < a then 1 else 0]) r := by
  intro sw sr hw hr
  refine ⟨push sw (if b < a then 1 else 0), sr, .next ?_ (.refl _), hw.push _ ?_, hr⟩
  · have ha := hw.popWord.peekWord
    have hb := hw.peekWord
    reduce_step
  · simpa [bytes] using hspace

theorem sth16 (a : Word) (h0 : ram pc = 0x2f) (hspace : r.length + 2 < 256) :
    Block ram pc (w ++ bytes a) r (pc + 1) w (r ++ bytes a) := by
  intro sw sr hw hr
  refine ⟨popWord sw, pushWord sr a, .next ?_ (.refl _), hw.popWord, hr.pushWord a hspace⟩
  have hx := hw.peekWord
  reduce_step

theorem sth16r (a : Word) (h0 : ram pc = 0x6f) (hspace : w.length + 2 < 256) :
    Block ram pc w (r ++ bytes a) (pc + 1) (w ++ bytes a) r := by
  intro sw sr hw hr
  refine ⟨pushWord sw a, popWord sr, .next ?_ (.refl _), hw.pushWord a hspace, hr.popWord⟩
  have hx := hr.peekWord
  reduce_step

theorem jmp16r (address : Word) (h0 : ram pc = 0x6c) :
    Block ram pc w (r ++ bytes address) address w r := by
  intro sw sr hw hr
  refine ⟨sw, popWord sr, .next ?_ (.refl _), hw, hr.popWord⟩
  have hx := hr.peekWord
  reduce_step

theorem jsi (offset : Word) (h0 : ram pc = 0x60)
    (h1 : ram (pc + 1) = (offset >>> 8).setWidth 8) (h2 : ram (pc + 2) = offset.setWidth 8)
    (hspace : r.length + 2 < 256) :
    Block ram pc w r (pc + 3 + offset) w (r ++ bytes (pc + 3)) := by
  intro sw sr hw hr
  exact ⟨sw, pushWord sr (pc + 3), .next (by reduce_step) (.refl _),
    hw, hr.pushWord _ hspace⟩

theorem jci (b : Byte) (offset : Word) (h0 : ram pc = 0x20)
    (h1 : ram (pc + 1) = (offset >>> 8).setWidth 8) (h2 : ram (pc + 2) = offset.setWidth 8) :
    Block ram pc (w ++ [b]) r (if b = 0 then pc + 3 else pc + 3 + offset) w r := by
  intro sw sr hw hr
  refine ⟨pop sw, sr, .next ?_ (.refl _), hw.pop, hr⟩
  have hb := hw.peek
  by_cases hz : b = 0 <;> reduce_step

end Block
end ProgramProofs.Fibonacci
