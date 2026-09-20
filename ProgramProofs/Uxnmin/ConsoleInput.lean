import ProgramProofs.Uxnmin.Chunks

set_option backward.isDefEq.respectTransparency false
namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Input reading and final-event selection depend only on the common system port. -/
def consoleEvent (state : Byte) : IO (Byte × Byte × Bool) := do
  if state == 0 then
    if let some byte := (← (← IO.getStdin).read 1)[0]? then
      return (byte.toBitVec, 1, false)
  return (10, 4, true)

theorem next_input (state : Uxn.Host.State) (control : state.control = .console .input) :
    state.next = some (do
      let (value, kind, last) ← consoleEvent (state.read Port.System.state)
      pure {state with control := .delivering value kind (remaining last)}) := by
  simp only [Uxn.Host.State.next, control, consoleEvent]
  split
  · congr 1
    simp only [bind_assoc]
    congr 1
    funext stream
    congr 1
    funext bytes
    cases bytes[0]? <;> rfl
  · rfl

theorem input_block {filename : String} {initialWorld : Void IO.RealWorld}
    {guest outer : Uxn.Host.State} (world : Void IO.RealWorld)
    (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
    (image : ConsoleImage guest outer)
    (guestControl : guest.control = .console .input)
    (outerControl : outer.control = .console .input) :
    Block (Boundary filename initialWorld) (.running guest world) (.running outer world) := by
  have next (host : Uxn.Host.State) (control : host.control = .console .input) :
      Configuration.next (.running host world) = some (match consoleEvent (host.read Port.System.state) world with
        | .ok (value, kind, last) later =>
            .running {host with control := .delivering value kind (remaining last)} later
        | .error error later => .failed error later) := by
    rw [Configuration.next, next_input host control]
    change some (Configuration.ofResult (EST.bind _ _ world)) = _
    rw [EST.bind.eq_def]
    cases consoleEvent (host.read Port.System.state) world with
    | ok event later => rcases event with ⟨value, kind, last⟩; rfl
    | error => rfl
  refine ⟨.running outer world, .refl, ?_, ?_⟩
  · simp only [label, next_input guest guestControl, next_input outer outerControl,
      Option.isNone_some, Bool.false_eq_true, if_false]
  · rw [next guest guestControl, next outer outerControl, image.system]
    cases effect : consoleEvent (guest.read Port.System.state) world with
    | ok event later =>
      rcases event with ⟨value, kind, last⟩
      refine .some ⟨_, .refl, .delivering value kind last ?_ ?_ rfl rfl⟩
      · exact reachable.tail (by simpa only [effect] using next guest guestControl)
      · exact ⟨image.core, image.ports, image.vector, image.system, image.working, image.returning, image.outerVector⟩
    | error error later => exact .some ⟨_, .refl, .stopped rfl rfl rfl⟩

end ProgramProofs.Uxnmin.Model
