import ProgramProofs.Uxnmin.Blocks

/-!
uxnmin.tal is a well-founded stuttering simulation of uxn.
-/

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host

/-- A host state and IO world state. -/
abbrev Configuration := Model.Configuration

abbrev Configuration.starting (boot : IO Uxn.Host.State) (world : Void IO.RealWorld) :
    Configuration := Model.Configuration.starting boot world

abbrev Configuration.running (state : Uxn.Host.State) (world : Void IO.RealWorld) :
    Configuration := Model.Configuration.running state world

abbrev Configuration.failed (error : IO.Error) (world : Void IO.RealWorld) :
    Configuration := Model.Configuration.failed error world

def Configuration.ofResult : EST.Out IO.Error IO.RealWorld Uxn.Host.State → Configuration
  | .ok state world => .running state world
  | .error error world => .failed error world

def Configuration.next : Configuration → Option Configuration
  | .starting boot world => some (.ofResult (boot world))
  | .running state world => state.next.map (fun action => .ofResult (action world))
  | .failed _ _ => none

/-- Our refinement's labels are the IO world and Host exit code. -/
def label : Configuration → EST.Out IO.Error IO.RealWorld (Option UInt32)
  | .starting _ world => .ok none world
  | .running state world => .ok (if state.next.isNone then some state.exitCode else none) world
  | .failed error world => .error error world

def Reachable (start finish : Configuration) : Prop :=
  Relation.ReflTransGen (fun a b => a.next = some b) start finish

/-- Change RAM outside the range uxnmin.tal allows guest programs to access. -/
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

def Loadable (filename : String) (world : Void IO.RealWorld) : Prop :=
  match (do (← File.Handle.open filename).read (ramSize - 0x100).toUSize) world with
  | .ok program after => program.size ≤ ramSize - 0x100 ∧
      Uxn.Host.file filename [] world = .ok (initialState program) after
  | .error _ _ => False

/-- A well-founded stuttering simulation where every step of the
specification corresponds to ≥1 step of the implementation, i.e. the
specification never stutters wrt the guest. -/
def RankedSimulation (R : Configuration → Configuration → Prop) : Prop :=
  (∀ direct nested, R direct nested → label direct = label nested) ∧
  ∃ rank : Configuration → Configuration → Nat,
    ∀ direct nested, R direct nested →
      Option.Rel R direct.next nested.next ∨
        ∃ nested', nested.next = some nested' ∧ R direct nested' ∧
          rank direct nested' < rank direct nested

theorem correct (filename : String) (world : Void IO.RealWorld)
    (filenameFits : filename.utf8ByteSize < 0x40)
    (filenameNoNul : 0 ∉ filename.toUTF8.data)
    (loadable : Loadable filename world) :
    let direct := Configuration.starting (Uxn.Host.file filename) world
    Confined direct → CompatibleDevices direct →
    ∃ R, R direct (.running (initialState rom [filename]) world) ∧
      RankedSimulation R := by
  intro direct confined compatible
  obtain ⟨R, includes, simulation⟩ := ProgramProofs.RankedSimulation.of_silent_blocks
    (Model.Boundary filename world)
    (Model.boundary_blocks filename world filenameFits filenameNoNul loadable confined compatible)
  exact ⟨R, includes _ _ .loading, simulation⟩

theorem correct_file (interpreter filename : String) (before world : Void IO.RealWorld)
    (interpreterLoaded : Uxn.Host.file interpreter [filename] before =
      .ok (initialState rom [filename]) world)
    (filenameFits : filename.utf8ByteSize < 0x40)
    (filenameNoNul : 0 ∉ filename.toUTF8.data)
    (loadable : Loadable filename world) :
    let direct := Configuration.starting (Uxn.Host.file filename) world
    Confined direct → CompatibleDevices direct →
    ∃ R, R direct (.ofResult (Uxn.Host.file interpreter [filename] before)) ∧
      RankedSimulation R := by
  simpa only [interpreterLoaded, Configuration.ofResult] using
    correct filename world filenameFits filenameNoNul loadable

end ProgramProofs.Uxnmin
