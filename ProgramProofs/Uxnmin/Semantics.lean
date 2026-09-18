import Uxn.Host
import ProgramProofs.Uxnmin.Rom
import Mathlib.Logic.Relation

namespace ProgramProofs.Uxnmin.Semantics
open Uxn Uxn.Host

abbrev Configuration := EST.Out IO.Error IO.RealWorld (Outcome × Uxn.Host.State)

-- For simulation purposes, our label is the state of the IO world.
def label : Configuration → EST.Out IO.Error IO.RealWorld Unit
  | .ok _ world => .ok () world
  | .error error world => .error error world

def next : Configuration → Option Configuration
  | .ok (.next vm, host) world => some (Uxn.Host.step vm host world)
  | .ok (.brk _, _) _ | .error _ _ => none

-- Reachability by finitely many steps.
def Reachable (start state : Configuration) : Prop :=
  Relation.ReflTransGen (fun a b => next a = some b) start state

-- Replace a Configuration's VM's RAM at addresses ≥ cutoff.
def replaceOutside (cutoff : Nat) (replacement : Word → Byte) : Configuration → Configuration
  | .ok (.next vm, host) world => .ok (.next (replace vm), host) world
  | .ok (.brk vm, host) world => .ok (.brk (replace vm), host) world
  | .error error world => .error error world
where
  replace (vm : Uxn.State) : Uxn.State :=
    { vm with mem.ram := fun address =>
        if address.toNat < cutoff then vm.mem.ram address else replacement address }

-- At every reachable state, replacing outside RAM before an
-- instruction is the same as replacing it afterward. Hence outside RAM
-- neither effects execution nor is modified.
def Confined (start : Configuration) : Prop :=
  ∀ state, Reachable start state → ∀ ram,
    next (replaceOutside ramSize ram state) = (next state).map (replaceOutside ramSize ram)

-- The reachable guest instructions use the device operations
-- supported by uxnmin.  File ports are excluded. Console input/type
-- cannot be written or read as the second byte of DEI2, and DEO2
-- cannot write its high byte to System/state.
def CompatibleDevices (start : Configuration) : Prop :=
  ∀ vm host world, Reachable start (.ok (.next vm, host) world) →
    match Uxn.step vm with
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

end ProgramProofs.Uxnmin.Semantics
