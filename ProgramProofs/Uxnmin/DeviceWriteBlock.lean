import ProgramProofs.Uxnmin.DeviceWriteSimulation
import ProgramProofs.Uxnmin.DeviceWriteCompatible

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host ProgramProofs.Host

/-- Supported DEO instructions form complete simulation blocks, including IO errors. -/
theorem device_write_block {start : Configuration} (compatible : CompatibleDevices start)
    {guest outer : Uxn.State} (guestHost outerHost : Uxn.Host.State) (world : Void IO.RealWorld)
    (reachable : Reachable start (.ok (.next guest, guestHost) world))
    (core : EvaluationBoundary guest outer) (devices : DeviceImage guestHost outer)
    (pointer : outer.mem.rstk.ptr = 4)
    (loaderFrame : outer.mem.rstk.data 0 ++ outer.mem.rstk.data 1 = 0x139#16)
    (runFrame : outer.mem.rstk.data 2 ++ outer.mem.rstk.data 3 = 0x154#16)
    (confined : guest.pc.toNat < ramSize) (opcode : guest.mem.ram guest.pc &&& 0x1f = 0x17) :
    ∃ last,
      Relation.ReflTransGen
        (fun x y => next x = some y ∧ label (.ok (.next guest, guestHost) world) = label x)
        (.ok (.next outer, outerHost) world) last ∧
      label (.ok (.next guest, guestHost) world) = label last ∧
      Option.Rel (fun d' c' => ∃ finish,
        Relation.ReflTransGen (fun x y => next x = some y ∧ label d' = label x) c' finish ∧
        Boundary start d' finish)
        (next (.ok (.next guest, guestHost) world)) (next last) := by
  obtain ⟨input, kind, outputInput, outputKind, supported⟩ :=
    device_write_compatible compatible guest guestHost world reachable opcode
  obtain ⟨stage, resume, final, finalHost, direct, before, action, after, finalCore, finalDevices, finalPointer, finalFrame⟩ :=
    device_write_simulation guestHost outerHost core devices confined opcode input kind outputInput outputKind supported
  let ret := (guest.mem.ram guest.pc).getLsbD 6
  let short := (guest.mem.ram guest.pc).getLsbD 5
  let kept := (guest.mem.ram guest.pc).getLsbD 7
  let stack := guestStack guest ret
  let output : IO Unit := deviceOutput (stack.data (stack.ptr - 1) + (if short then 1 else 0))
    (stack.data (stack.ptr - 2))
  let guest' := deviceWriteNext guest ret short kept
  let guestHost' := deviceWriteHost guest guestHost ret short
  have performed {α : Type} (result : α) : (do output; pure result) world =
      match output world with
      | .ok _ later => .ok result later
      | .error error later => .error error later := by
    change EST.bind output (fun _ => EST.pure result) world = _
    exact (EST.bind.eq_def _ _ _).trans (by cases output world <;> rfl)
  have directStep : Uxn.Host.step guest guestHost world =
      match output world with
      | .ok _ after => .ok (.next guest', guestHost') after
      | .error error after => .error error after := (congrFun direct world).trans (performed _)
  have nativeStep : Uxn.Host.step stage outerHost world =
      match output world with
      | .ok _ after => .ok (.next resume, finalHost) after
      | .error error after => .error error after := (congrFun action world).trans (performed _)
  refine ⟨.ok (.next stage, outerHost) world, reaches_chunk before outerHost world, rfl, ?_⟩
  simp only [next, directStep, nativeStep]
  cases effect : output world with
  | ok result later =>
    simp only [effect]
    apply Option.Rel.some
    refine ⟨.ok (.next final, finalHost) later, reaches_chunk after finalHost later,
      .evaluating ?_ finalCore finalDevices (finalPointer.trans pointer) ?_ ?_⟩
    · apply reachable.tail
      simp only [next, directStep, effect]
    · rw [finalFrame 0 (by rw [pointer]; decide), finalFrame 1 (by rw [pointer]; decide)]
      exact loaderFrame
    · rw [finalFrame 2 (by rw [pointer]; decide), finalFrame 3 (by rw [pointer]; decide)]
      exact runFrame
  | error error later =>
    simp only [effect]
    exact .some ⟨.error error later, .refl, .stopped rfl rfl rfl⟩

end ProgramProofs.Uxnmin
