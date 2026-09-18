import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO
import Mathlib.Tactic.Conv

namespace ProgramProofs.Host
open Uxn Uxn.Host

/-- Writing stdout preserves VM memory and returns an empty patch. -/
@[uxn_state] theorem deo_stdout (mem : Memory) (byte : Byte) (host : Uxn.Host.State) :
    deo mem 0x18#8 byte host = (do writeStdout byte; pure ({}, host.write 0x18 byte)) := by
  change ((do
    modify (·.write 0x18 byte)
    (← IO.getStdout).write ⟨#[UInt8.ofBitVec byte]⟩
    return {}) : StateT Uxn.Host.State IO Patch) host = _
  simp [uxn_state, writeStdout]

/-- Unfold one unbounded host iteration, leaving recursive calls opaque. -/
theorem evalLoop_next (vm : Uxn.State) (host : Uxn.Host.State)
    (hfuel : host.fuel = none) :
    evalLoop (.next vm) host =
      (match Uxn.step vm with
      | .done outcome => evalLoop outcome
      | .request request vm resume => do
        evalLoop (resume (← respond vm.mem request))) host := by
  rcases host with ⟨hostVM, ports, vector, fuel, file⟩
  cases hfuel
  rw [evalLoop.eq_def]
  simp only [uxn_state]
  cases h : Uxn.step vm <;> simp [Uxn.Host.step, h, uxn_state]

/-- Symbolically execute exactly `count` host instructions on the left of an
execution equation. Code and invariant facts are supplied by the caller; each
iteration unfolds the host loop once, so recursive calls stay opaque.
The scoped elaborator option lets rewriting unfold the dependent `Request.Result`
type while simplifying a device request; the resulting proof is kernel checked. -/
macro "symbolic_steps" count:num fuel:term:max "[" facts:term,* "]" : tactic => `(tactic|
  set_option backward.isDefEq.respectTransparency false in
  iterate $count
    conv_lhs =>
      rw [evalLoop_next _ _ (by exact $fuel)]
      conv =>
        pattern Uxn.step _
        simp [uxn_state, uxn_step, $[$facts:term],*]
      simp [uxn_state, $[$facts:term],*, Patch.apply])

/-- A completed startup with no input callback determines the direct IO run. -/
theorem run_of_evalLoop (rom : ByteArray) (final : Uxn.Host.State)
    (output : IO Unit)
    (hrun : evalLoop (.next { (initialState rom).vm with pc := 0x100 }) (initialState rom) =
      (do output; pure ((), final)))
    (hv : final.consoleVector = 0) (hh : final.read 0x0f = 0) :
    Uxn.Host.run rom = (do output; pure (0, final)) := by
  unfold Uxn.Host.run
  rw [← initial_shape rom] at hrun ⊢
  simp [uxn_state, machine] at hrun
  simp at hv hh
  simp [machine, uxn_state, Uxn.Host.State.write, hrun, hv, hh, Port.System.state]

end ProgramProofs.Host
