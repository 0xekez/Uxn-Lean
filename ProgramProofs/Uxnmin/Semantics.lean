import Uxn.Host
import ProgramProofs.Uxnmin.Rom
import Mathlib.Logic.Relation

/-! Internal definitions used by the block proofs. `Correctness.lean` presents
the same contract together with the public refinement theorem. -/

namespace ProgramProofs.Uxnmin.Model
open Uxn Uxn.Host

/-- A configuration is a machine state and an IO state. -/
inductive Configuration where
  | starting (boot : IO Uxn.Host.State) (world : Void IO.RealWorld)
  | running (state : Uxn.Host.State) (world : Void IO.RealWorld)
  | failed (error : IO.Error) (world : Void IO.RealWorld)

def Configuration.ofResult : EST.Out IO.Error IO.RealWorld Uxn.Host.State → Configuration
  | .ok state world => .running state world
  | .error error world => .failed error world

/-- Apply an actual initialization action or `State.next` to its IO world. -/
def Configuration.next : Configuration → Option Configuration
  | .starting boot world => some (.ofResult (boot world))
  | .running state world => state.next.map (fun action => .ofResult (action world))
  | .failed _ _ => none

/-- The IO world and exit status are observable from the refinement POV. -/
def label : Configuration → EST.Out IO.Error IO.RealWorld (Option UInt32)
  | .starting _ world => .ok none world
  | .running state world => .ok (if state.next.isNone then some state.exitCode else none) world
  | .failed error world => .error error world

def Reachable (start finish : Configuration) : Prop :=
  Relation.ReflTransGen (fun a b => a.next = some b) start finish

/-- Change only RAM outside the range represented by the interpreter. -/
def replaceOutside (ram : Word → Byte) : Configuration → Configuration
  | .running state world => .running
      { state with vm.mem.ram := fun address =>
          if address.toNat < ramSize then state.vm.mem.ram address else ram address } world
  | config => config

/-- At every reachable loaded state, changing outside RAM before a host step
has the same effect as changing it afterward, thus outside RAM neither affects
execution nor is modified. -/
def Confined (start : Configuration) : Prop :=
  ∀ state world,
    let current := Configuration.running state world
    Reachable start current → ∀ ram,
      (replaceOutside ram current).next = current.next.map (replaceOutside ram)

/-- Every reachable guest instruction uses device operations supported
by uxnmin.tal. -/
def CompatibleDevices (start : Configuration) : Prop :=
  ∀ state world after, Reachable start (.running state world) →
    state.control = .evaluating after →
    match Uxn.step state.vm with
    | .done _ => True
    | .request (.read8 port) _ _ => port ∉ Port.File.ports
    | .request (.read16 port) _ _ =>
        (∀ p ∈ [port, port + 1], p ∉ Port.File.ports) ∧
        port + 1 ∉ [Port.Console.read, Port.Console.type]
    | .request (.write8 port _) _ _ =>
        port ∉ Port.File.ports ∧ port ∉ [Port.Console.read, Port.Console.type]
    | .request (.write16 port _ _) _ _ =>
        port ≠ Port.System.state ∧
        (∀ p ∈ [port, port + 1],
          p ∉ Port.File.ports ∧ p ∉ [Port.Console.read, Port.Console.type])

/-- Both guest-loading paths succeed, initialize the same program, and leave
the same IO world. The bounded File-device read must fit the interpreter's ROM
capacity. -/
def Loadable (filename : String) (world : Void IO.RealWorld) : Prop :=
  match (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) world with
  | .ok program after => program.size ≤ ramSize - 0x100 ∧
      Uxn.Host.file filename [] world = .ok (initialState program) after
  | .error _ _ => False

end ProgramProofs.Uxnmin.Model
