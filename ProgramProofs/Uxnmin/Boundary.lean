import ProgramProofs.Uxnmin.Simulation
import ProgramProofs.Uxnmin.Representation

namespace ProgramProofs.Uxnmin
open Semantics
open Uxn Uxn.Host

/-- The interpreter's shadow device bytes and its two special input literals. -/
structure DeviceImage (guest : Uxn.Host.State) (outer : Uxn.State) : Prop where
  ports : ∀ port : Byte, outer.mem.ram (0x759 + port.setWidth 16) = guest.read port
  consoleRead : outer.mem.ram 0x199 = guest.read Port.Console.read
  consoleType : outer.mem.ram 0x1a4 = guest.read Port.Console.type

/-- A dispatch state during reset, or two equally labelled finished states. -/
inductive Boundary (start : Configuration) : Configuration → Configuration → Prop where
  | evaluating {guest outer : Uxn.State} {guestHost outerHost : Uxn.Host.State}
      {world : Void IO.RealWorld}
      (reachable : Reachable start (.ok (.next guest, guestHost) world))
      (core : EvaluationBoundary guest outer)
      (devices : DeviceImage guestHost outer)
      (pointer : outer.mem.rstk.ptr = 4)
      (loaderFrame : outer.mem.rstk.data 0 ++ outer.mem.rstk.data 1 = 0x139#16)
      (runFrame : outer.mem.rstk.data 2 ++ outer.mem.rstk.data 3 = 0x154#16) :
      Boundary start (.ok (.next guest, guestHost) world) (.ok (.next outer, outerHost) world)
  | stopped {d c : Configuration}
      (direct : next d = none) (concrete : next c = none) (agree : label d = label c) :
      Boundary start d c

/-- A pure guest step and a represented native endpoint preserve the boundary
when the native block retains device bytes and active return frames. -/
theorem Boundary.of_next {start : Configuration} {guest guest' outer final : Uxn.State}
    {guestHost outerHost : Uxn.Host.State} {world : Void IO.RealWorld}
    (boundary : Boundary start (.ok (.next guest, guestHost) world) (.ok (.next outer, outerHost) world))
    (direct : next (.ok (.next guest, guestHost) world) = some (.ok (.next guest', guestHost) world))
    (core : EvaluationBoundary guest' final)
    (memory : ∀ address, address = 0x199 ∨ address = 0x1a4 ∨
      (0x759 ≤ address.toNat ∧ address.toNat < 0x859) → final.mem.ram address = outer.mem.ram address)
    (pointer : final.mem.rstk.ptr = outer.mem.rstk.ptr)
    (frame : ∀ index : Byte, index.toNat < outer.mem.rstk.ptr.toNat →
      final.mem.rstk.data index = outer.mem.rstk.data index) :
    Boundary start (.ok (.next guest', guestHost) world) (.ok (.next final, outerHost) world) := by
  cases boundary with
  | evaluating reachable _ devices outerPointer loaderFrame runFrame =>
    refine .evaluating ?_ core ?_ (pointer.trans outerPointer) ?_ ?_
    · exact reachable.tail direct
    · constructor
      · intro port
        rw [memory _ (.inr (.inr (by constructor <;> bv_omega)))]
        exact devices.ports port
      · rw [memory _ (.inl rfl)]
        exact devices.consoleRead
      · rw [memory _ (.inr (.inl rfl))]
        exact devices.consoleType
    · rw [frame 0 (by rw [outerPointer]; decide), frame 1 (by rw [outerPointer]; decide)]
      exact loaderFrame
    · rw [frame 2 (by rw [outerPointer]; decide), frame 3 (by rw [outerPointer]; decide)]
      exact runFrame
  | stopped direct _ _ => simp [next] at direct

end ProgramProofs.Uxnmin
