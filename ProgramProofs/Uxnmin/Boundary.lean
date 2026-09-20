import ProgramProofs.Uxnmin.Confinement
import ProgramProofs.Uxnmin.DeviceRepresentation

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host ProgramProofs.Host

/-- Reset and input callbacks use different native return frames. -/
inductive Invocation where
  | reset
  | callback (last : Bool)

def remaining (last : Bool) : Console := if last then .done else .input

def Invocation.directReturn : Invocation → ReturnTo
  | .reset => .arguments []
  | .callback last => .console (remaining last)

def Invocation.outerReturn : Invocation → ReturnTo
  | .reset => .console .input
  | .callback last => .console (remaining last)

def Invocation.pointer : Invocation → Byte
  | .reset => 4
  | .callback _ => 2

def Invocation.firstReturn : Invocation → Word
  | .reset => 0x139
  | .callback _ => 0x18f

def Invocation.outerVector : Invocation → Word
  | .reset => 0
  | .callback _ => 0x174

/-- The complete invariant while the interpreter is evaluating guest code. -/
structure Evaluation (invocation : Invocation) (guest outer : Uxn.Host.State) : Prop where
  core : EvaluationBoundary guest.vm outer.vm
  devices : DeviceImage guest outer.vm
  system : outer.read Port.System.state = guest.read Port.System.state
  guestControl : guest.control = .evaluating invocation.directReturn
  outerControl : outer.control = .evaluating invocation.outerReturn
  outerVector : outer.consoleVector = invocation.outerVector
  pointer : outer.vm.mem.rstk.ptr = invocation.pointer
  firstReturn : outer.vm.mem.rstk.data 0 ++ outer.vm.mem.rstk.data 1 = invocation.firstReturn
  resetReturn : invocation = .reset → outer.vm.mem.rstk.data 2 ++ outer.vm.mem.rstk.data 3 = 0x154#16

/-- At console boundaries, input literals need not match when the guest has
cleared its vector. They are refreshed before every nonzero-vector callback. -/
structure ConsoleImage (guest outer : Uxn.Host.State) : Prop where
  core : Represents guest.vm outer.vm
  ports : ∀ port : Byte, port ≠ Port.Console.read → port ≠ Port.Console.type →
    outer.vm.mem.ram (0x759 + port.setWidth 16) = guest.read port
  vector : outer.vm.mem.ram 0x175 ++ outer.vm.mem.ram 0x176 = guest.consoleVector
  system : outer.read Port.System.state = guest.read Port.System.state
  working : outer.vm.mem.wstk.ptr = 0
  returning : outer.vm.mem.rstk.ptr = 0
  outerVector : outer.consoleVector = 0x174

/-- Native addresses carrying device state between guest instructions. -/
def DeviceAddress (address : Word) : Prop :=
  address ∈ [0x175, 0x176, 0x199, 0x1a4] ∨ 0x759 ≤ address.toNat ∧ address.toNat < 0x859

/-- Preserve host bookkeeping while moving both VMs to a new evaluation boundary. -/
theorem Evaluation.of_pure {invocation : Invocation} {guest outer : Uxn.Host.State}
    (image : Evaluation invocation guest outer) {guestVM outerVM : Uxn.State}
    (core : EvaluationBoundary guestVM outerVM)
    (memory : ∀ address, DeviceAddress address → outerVM.mem.ram address = outer.vm.mem.ram address)
    (pointer : outerVM.mem.rstk.ptr = outer.vm.mem.rstk.ptr)
    (frame : ∀ index : Byte, index.toNat < outer.vm.mem.rstk.ptr.toNat →
      outerVM.mem.rstk.data index = outer.vm.mem.rstk.data index) :
    Evaluation invocation {guest with vm := guestVM} {outer with vm := outerVM} := by
  have active (index : Byte) (bound : index.toNat < invocation.pointer.toNat) :
      outerVM.mem.rstk.data index = outer.vm.mem.rstk.data index :=
    frame index (image.pointer ▸ bound)
  refine ⟨core, ?_, image.system, image.guestControl, image.outerControl,
    image.outerVector, pointer.trans image.pointer, ?_, ?_⟩
  · constructor
    · intro port input kind
      rw [memory _ (.inr (by constructor <;> bv_omega))]
      exact image.devices.ports port input kind
    · rw [memory _ (.inl (by simp))]
      exact image.devices.consoleRead
    · rw [memory _ (.inl (by simp))]
      exact image.devices.consoleType
    · rw [memory _ (.inl (by simp)), memory _ (.inl (by simp))]
      exact image.devices.vector
  · rw [active 0 (by cases invocation <;> simp [Invocation.pointer]), active 1 (by cases invocation <;> simp [Invocation.pointer])]
    exact image.firstReturn
  · intro reset
    subst invocation
    rw [active 2 (by decide), active 3 (by decide)]
    exact image.resetReturn rfl

/-- Boundaries span initialization, evaluation, console routing, and completion. -/
inductive Boundary (filename : String) (initialWorld : Void IO.RealWorld) :
    Configuration → Configuration → Prop where
  | loading : Boundary filename initialWorld (.starting (Uxn.Host.file filename) initialWorld)
      (.running (initialState rom [filename]) initialWorld)
  | evaluating {guest outer : Uxn.Host.State} {world : Void IO.RealWorld}
      (invocation : Invocation)
      (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
      (image : Evaluation invocation guest outer) :
      Boundary filename initialWorld (.running guest world) (.running outer world)
  | input {guest outer : Uxn.Host.State} {world : Void IO.RealWorld}
      (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
      (image : ConsoleImage guest outer)
      (guestControl : guest.control = .console .input)
      (outerControl : outer.control = .console .input) :
      Boundary filename initialWorld (.running guest world) (.running outer world)
  | delivering {guest outer : Uxn.Host.State} {world : Void IO.RealWorld}
      (value kind : Byte) (last : Bool)
      (reachable : Reachable (.starting (Uxn.Host.file filename) initialWorld) (.running guest world))
      (image : ConsoleImage guest outer)
      (guestControl : guest.control = .delivering value kind (remaining last))
      (outerControl : outer.control = .delivering value kind (remaining last)) :
      Boundary filename initialWorld (.running guest world) (.running outer world)
  | stopped {direct nested : Configuration}
      (directStopped : direct.next = none) (nestedStopped : nested.next = none)
      (agree : label direct = label nested) : Boundary filename initialWorld direct nested

end ProgramProofs.Uxnmin.Model
