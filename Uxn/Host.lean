import Uxn.Host.File
import Uxn.Host.Ports

/-! A UXN host implementing a subset of the Varvara spec [1].

The implementation is a state machine which State.next drives. This
simplifies refinement proofs about host implementations.

[1]: https://wiki.xxiivv.com/site/varvara.html  -/

namespace Uxn.Host

structure File where
  name : Option Word := none
  length : Word := 0
  handle : Option File.Handle := none

/-- The VM host runs a program in three phases. Arguments are fed in,
then standard input is. The program is notified when input is done. -/
inductive Console where
  | argument (bytes : List UInt8) (remaining : List String)
  | input
  | done

/-- Does completion of an event result in argument processing or
console work? -/
inductive ReturnTo where
  | arguments (args : List String)
  | console (work : Console)

inductive Control where
  | evaluating (after : ReturnTo)
  | delivering (value kind : Byte) (after : Console)
  | console (work : Console)

structure State where
  vm : Uxn.State
  control : Control := .evaluating (.arguments [])
  ports : Vector Byte 0x100 := .replicate _ 0
  -- uxn2 updates Console/vector only when the low-byte of its
  -- port is written to. hence, we can't derive its value from the
  -- ports' state alone.
  consoleVector : Word := 0
  -- Remaining instruction budget when State.run returns; next does not consult it.
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

def State.exitCode (s : State) : UInt32 :=
  (s.read Port.System.state &&& 0x7f).toNat.toUInt32

/-- Load a ROM and prepare its reset entry and console arguments. -/
def initialState (rom : ByteArray) (args : List String := []) : State :=
  let (memSize, romStart) := (0x10000, 0x100)
  let ram := rom.copySlice 0 ⟨Array.replicate memSize 0⟩ romStart (memSize - romStart)
  ({ vm :=
       { pc := BitVec.ofNat 16 romStart
         mem :=
           { ram := fun address => ram[address.toNat]!.toBitVec
             wstk := { data := fun _ => 0, ptr := 0 }
             rstk := { data := fun _ => 0, ptr := 0 } } }
     control := .evaluating (.arguments args) } : State).write
       Port.Console.type (if args.isEmpty then 0 else 1)

def load (handle : IO.FS.Handle) (args : List String := [])
    (limit : Nat := 0xff00) : IO State := do
  return initialState (← handle.read limit.toUSize) args

/-- Load a ROM by filename, using the same open/read operations as `main`. -/
def file (filename : String) (args : List String := []) : IO State := do
  load (← IO.FS.Handle.mk filename .read) args

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
    -- Like uxn2, release the handle on a positive-length EOF read so the next read reopens it.
    if file.length != 0 && bytes.isEmpty then
      modify fun s => { s with file.handle := none }
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

def step (vm : Uxn.State) : StateT State IO Outcome :=
  match Uxn.step vm with
  | .done outcome => pure outcome
  | .request request vm resume => resume <$> respond vm.mem request

/-- Select the next argument, or stdin when there are no arguments left. -/
def Console.arguments : List String → Console
  | [] => .input
  | arg :: args => .argument arg.toUTF8.data.toList args

/-- One host transition: a VM instruction, an input read, or console delivery
and routing. -/
def State.next (s : State) : Option (IO State) :=
  match s.control with
  | .evaluating after => some do
      match ← step s.vm s with
      | (.next vm, s) => return { s with vm }
      | (.brk vm, s) => return { s with vm, control := .console (match after with
          | .arguments args => if s.consoleVector == 0 then .done else .arguments args
          | .console work => work) }
  | .delivering value kind after => some do
      let s := (s.write Port.Console.read value).write Port.Console.type kind
      -- Once the console loop has started, clearing the vector skips
      -- callbacks but does not stop input consumption.
      if s.consoleVector == 0 then
        return { s with control := .console after }
      else
        return { s with vm.pc := s.consoleVector, control := .evaluating (.console after) }
  | .console (.argument bytes args) => some do
      if let byte :: bytes := bytes then
        if s.read Port.System.state == 0 && byte != 0 then
          return { s with control := .delivering byte.toBitVec 2 (.argument bytes args) }
      -- The separator is delivered even if the preceding callback set the halt flag.
      return { s with control := .delivering 10 (if args.isEmpty then 4 else 3) (.arguments args) }
  | .console .input => some do
      if s.read Port.System.state == 0 then
        -- An empty read is EOF; a NUL byte is still a console event.
        if let some byte := (← (← IO.getStdin).read 1)[0]? then
          return { s with control := .delivering byte.toBitVec 1 .input }
      -- EOF and host halt both deliver the final console event before returning.
      return { s with control := .delivering 10 4 .done }
  | .console .done => none

/-- Execute until completion or budget exhaustion of fuel. -/
def State.run (state : State) (fuel : Option Nat := none) : IO State := do
  if fuel == some 0 then return { state with fuel }
  match state.next with
  | none => return { state with fuel }
  | some action =>
      (← action).run (match state.control with
        | .evaluating _ => fuel.map Nat.pred
        | _ => fuel)
partial_fixpoint

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    report (← IO.getStdout) s!"usage: {← IO.appPath} file.rom [args..]\n"
  | file :: args =>
    match ← (IO.FS.Handle.mk file .read).toBaseIO with
    | .error _ =>
      report (← IO.getStderr) s!"{← IO.appPath}: {file} not found.\n"
    | .ok handle =>
      return (← (← load handle args).run).exitCode
where
  report (stream : IO.FS.Stream) (message : String) : IO UInt32 := do
    stream.putStr message
    return message.utf8ByteSize.toUInt32

end Uxn.Host
