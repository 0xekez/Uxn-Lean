-- The self-hosted Uxn VM is a well-founded stuttering simulation of
-- the Uxn VM.
import Uxn.Host
import ProgramProofs.Uxnmin.Rom
import ProgramProofs.RankedSimulation
import ProgramProofs.Uxnmin.Proof

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host

abbrev Configuration := EST.Out IO.Error IO.RealWorld (Outcome × Uxn.Host.State)

-- Our label is the state of the IO world.
def label : Configuration → EST.Out IO.Error IO.RealWorld Unit
  | .ok _ world => .ok () world
  | .error error world => .error error world

def next : Configuration → Option Configuration
  | .ok (.next vm, host) world => some (Uxn.Host.step vm host world)
  | .ok (.brk _, _) _ | .error _ _ => none

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

-- uxnmin provides 0xf7a7 bytes of guest RAM (ramSize), relocated
-- above its own code and state. If, at every reachable state,
-- replacing outside RAM before an instruction is the same as
-- replacing it afterward, then outside RAM neither affects execution
-- nor is modified.
def Confined (start : Configuration) : Prop :=
  ∀ state, Reachable start state → ∀ ram,
    next (replaceOutside ramSize ram state) = (next state).map (replaceOutside ramSize ram)

-- The reachable guest instructions use the device operations
-- supported by uxnmin.
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

-- If the self-hosted VM can load filename, and filename's contents
-- correspond to program, then the self-hosted VM takes some number of
-- steps to initialize itself, and from then on is a simulation
-- refinement of Uxn.Host.
theorem correct (filename : String) (program : ByteArray)
    (before after : Void IO.RealWorld)
    (filenameFits : filename.utf8ByteSize < 0x40)
    (filenameNoNul : 0 ∉ filename.toUTF8.data)
    (programFits : program.size ≤ ramSize - 0x0100)
    (read : (do
      (← File.Handle.open filename).read (ramSize - 0x0100).toUSize) before = .ok program after) :
    let initial := Uxn.Host.initialState program
    let start : Configuration := .ok (.next initial.vm, initial) after
    Confined start → CompatibleDevices start →
    ∃ steps host, ∃ R : Configuration → Configuration → Prop,
      Uxn.Host.run rom [filename] (some steps) before = .ok (0, host) after ∧
      host.fuel = some 0 ∧
      R start (.ok (.next host.vm, host) after) ∧
      RankedSimulation next next label label R := by
  exact Proof.correct filename program before after filenameFits filenameNoNul programFits read

end ProgramProofs.Uxnmin
