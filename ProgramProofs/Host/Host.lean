import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO
import Mathlib.Tactic.Conv

namespace ProgramProofs.Host
open Uxn Uxn.Host

/-- Resume the host after an evaluation returns. -/
def finish (after : ReturnTo) (host : Uxn.Host.State) : IO Uxn.Host.State :=
  { host with control := .console (match after with
    | .arguments args => if host.consoleVector == 0 then .done else .arguments args
    | .console work => work) }.run

/-- Run an evaluation with its actual host continuation. -/
def evaluate (after : ReturnTo) (vm : Uxn.State) (host : Uxn.Host.State) : IO Uxn.Host.State :=
  { host with vm, control := .evaluating after }.run

@[uxn_state] theorem deo_stdout (mem : Memory) (byte : Byte) (host : Uxn.Host.State) :
    deo mem 0x18#8 byte host = (do writeStdout byte; pure ({}, host.write 0x18 byte)) := by
  change ((do
    modify (·.write 0x18 byte)
    (← IO.getStdout).write ⟨#[UInt8.ofBitVec byte]⟩
    return {}) : StateT Uxn.Host.State IO Patch) host = _
  simp [uxn_state, writeStdout]

/-- Unfold unbounded execution by one actual host transition. -/
theorem run_next (host : Uxn.Host.State) :
    host.run = match host.next with
      | none => pure {host with fuel := none}
      | some action => action >>= fun state => state.run := by
  rw [Uxn.Host.State.run.eq_def]
  cases host.control <;> rfl

/-- Symbolically execute `count` VM instructions in the actual unbounded host
run, keeping its continuation and all external IO actions intact. -/
macro "symbolic_steps" count:num "[" facts:term,* "]" : tactic => `(tactic|
  set_option backward.isDefEq.respectTransparency false in
  iterate $count
    conv_lhs =>
      simp only [evaluate, Uxn.Host.State.write]
      rw [run_next]
      simp only [Uxn.Host.State.next, Uxn.Host.step, Option.map_none,
        Bool.false_eq_true, if_false]
      conv =>
        pattern Uxn.step _
        simp [uxn_state, uxn_step, $[$facts:term],*]
      simp [uxn_state, $[$facts:term],*, Patch.apply, Uxn.Host.State.write, bind_assoc])

/-- A completed startup with no input callback returns without reading stdin. -/
theorem run_of_evaluate (rom : ByteArray) (final : Uxn.Host.State)
    (output : IO Unit)
    (hrun : evaluate (.arguments []) (initialState rom).vm (initialState rom) =
      (do output; finish (.arguments []) final))
    (hv : final.consoleVector = 0) (hh : final.read 0x0f = 0) :
    (initialState rom).run = (do output; pure {final with control := .console .done, fuel := none}) ∧
    final.exitCode = 0 := by
  constructor
  · change evaluate (.arguments []) (initialState rom).vm (initialState rom) = _
    rw [hrun]
    simp only [finish, hv, beq_self_eq_true, if_true]
    rw [Uxn.Host.State.run.eq_def]
    rfl
  · change (final.read 0x0f &&& 0x7f).toNat.toUInt32 = 0
    rw [hh]
    rfl

end ProgramProofs.Host
