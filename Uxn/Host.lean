-- A Uxn host supporting a subset of the Varvara spec https://wiki.xxiivv.com/site/varvara.html.
import Uxn.Host.File
import Uxn.Host.Ports

namespace Uxn.Host

structure File where
  name : Option Word := none
  length : Word := 0
  handle : Option File.Handle := none

structure State where
  vm : Uxn.State
  ports : Vector Byte 0x100 := .replicate _ 0
  -- uxn2 updates Console/vector only when the low-byte of its
  -- port is written to. hence, we can't derive its value from the
  -- ports' state alone.
  consoleVector : Word := 0
  fuel : Option Nat := none
  -- like Console/vector, File/name and File/length cannot be derived
  -- from port state.
  file : File := {}

def State.read (s : State) (port : Byte) : Byte :=
  s.ports.get port.toFin

def State.write (s : State) (port value : Byte) : State :=
  { s with ports := s.ports.set port.toNat value port.isLt }

def State.readWord (s : State) (port : Byte) : Word :=
  s.read port ++ s.read (port + 1)

def State.writeWord (s : State) (port : Byte) (value : Word) : State :=
  (s.write port ((value >>> 8).setWidth 8)).write (port + 1) (value.setWidth 8)

def initialState (rom : ByteArray) : State :=
  let (memSize, romStart) := (0x10000, 0x100)
  let ram := rom.copySlice 0 ⟨Array.replicate memSize 0⟩ romStart (memSize - romStart)
  { vm :=
      { pc := 0
        mem :=
          { ram := fun address => ram[address.toNat]!.toBitVec
            wstk := { data := fun _ => 0, ptr := 0 }
            rstk := { data := fun _ => 0, ptr := 0 } } } }

private def fileName (mem : Memory) (address : Word) : Option String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [address.toNat:0x10000] do
    let byte := UInt8.ofBitVec (mem.ram (BitVec.ofNat 16 i))
    if byte == 0 then return String.fromUTF8? bytes
    bytes := bytes.push byte
  return none

private def readFile (mem : Memory) : StateT State IO Patch := do
  modify (·.writeWord Port.File.success 0)
  let file := (← get).file
  let some name := file.name | return {}
  try
    let handle ← match file.handle with
      | some handle => pure handle
      | none =>
        match fileName mem name with
        | none => throw (IO.userError "invalid file name")
        | some name => File.Handle.open name
    modify fun s => { s with file := { file with handle := some handle } }
    let address := (← get).readWord Port.File.read
    let bytes ← handle.read (min file.length.toNat (0x10000 - address.toNat)).toUSize
    modify (·.writeWord Port.File.success (BitVec.ofNat 16 bytes.size))
    return { ramWrites := bytes.data.toList.zipIdx |>.map fun (byte, i) =>
      (address + BitVec.ofNat 16 i, byte.toBitVec) }
  catch _ => return {}

def deo (mem : Memory) (port value : Byte) : StateT State IO Patch := do
  modify (·.write port value)
  match port with
  | Port.Console.vectorLow => modify fun s => { s with consoleVector := s.read Port.Console.vector ++ value }
  | Port.Console.write => (← IO.getStdout).write ⟨#[UInt8.ofBitVec value]⟩
  | Port.Console.error => (← IO.getStderr).write ⟨#[UInt8.ofBitVec value]⟩
  | Port.File.nameLow => modify fun s => { s.writeWord Port.File.success 0 with
      file := { s.file with name := some (s.readWord Port.File.name), handle := none } }
  | Port.File.lengthLow => modify fun s => { s with file.length := s.readWord Port.File.length }
  | Port.File.readLow => return ← readFile mem
  | _ => pure ()
  return {}

def respond (mem : Memory) (request : Request) : StateT State IO (Reply request) :=
  match request with
  | .read8 port => do return { reply := (← get).read port, patch := {} }
  | .read16 port => do return { reply := (← get).readWord port, patch := {} }
  | .write8 port value => do return { reply := (), patch := ← deo mem port value }
  | .write16 port low high => do
    modify (·.write port high)
    return { reply := (), patch := ← deo mem (port + 1) low }

def evalLoop : Outcome → StateT State IO Unit
  | .brk vm => modify fun s => { s with vm }
  | .next vm => do
    if (← get).fuel == some 0 then
      modify fun s => { s with vm }
    else
      modify fun s => { s with fuel := s.fuel.map Nat.pred }
      match Uxn.step vm with
      | .done outcome => evalLoop outcome
      | .request request vm resume =>
        evalLoop (resume (← respond vm.mem request))
partial_fixpoint

def eval (pc : Word) : StateT State IO Unit := do
  evalLoop (.next { (← get).vm with pc })

def run.consoleInput (value kind : Byte) : StateT State IO Unit := do
  if (← get).fuel == some 0 then return
  modify fun s => (s.write Port.Console.read value).write Port.Console.type kind
  if (← get).consoleVector != 0 then
    eval (← get).consoleVector

def run.consoleArgs (args : List String) : StateT State IO Unit :=
  match args with
  | [] => pure ()
  | arg :: args => do
    if (← get).fuel == some 0 then return
    for byte in arg.toUTF8 do
      if (← get).fuel == some 0 || (← get).read Port.System.state != 0 || byte == 0 then break
      run.consoleInput byte.toBitVec 2
    -- reference delivers even when the preceding callback set the halt flag.
    run.consoleInput 10 (if args.isEmpty then 4 else 3)
    run.consoleArgs args

def run.readConsole : StateT State IO Unit := do
  if (← get).fuel == some 0 || (← get).read Port.System.state != 0 then return
  match (← (← IO.getStdin).read 1)[0]? with
  | none => pure ()
  | some byte =>
    run.consoleInput byte.toBitVec 1
    run.readConsole
partial_fixpoint

/-- Run a ROM from its initial state, with no arguments and unlimited fuel by default. -/
def run (rom : ByteArray) (args : List String := [])
    (fuel : Option Nat := none) : IO (UInt32 × State) :=
  StateT.run (s := initialState rom) do
    modify fun s => { s.write Port.Console.type (if args.isEmpty then 0 else 1) with fuel }
    eval 0x100
    if (← get).fuel != some 0 && (← get).consoleVector != 0 then
      run.consoleArgs args
      run.readConsole
      run.consoleInput 10 4
    return ((← get).read Port.System.state &&& 0x7f).toNat.toUInt32

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    report (← IO.getStdout) s!"usage: {← IO.appPath} file.rom [args..]\n"
  | file :: args =>
    match ← (IO.FS.Handle.mk file .read).toBaseIO with
    | .error _ =>
      report (← IO.getStderr) s!"{← IO.appPath}: {file} not found.\n"
    | .ok handle =>
      return (← run (← handle.read 0xff00) args).1
where
  report (stream : IO.FS.Stream) (message : String) : IO UInt32 := do
    stream.putStr message
    return message.utf8ByteSize.toUInt32

end Uxn.Host
