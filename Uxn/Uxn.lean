-- The Uxn virtual machine.
import Mathlib.Logic.Function.Basic
import Lean.Elab.Tactic.Omega

namespace Uxn

abbrev Byte := BitVec 8
abbrev Word := BitVec 16

structure Stack where
  data : Byte → Byte
  ptr  : Byte

structure Memory where
  ram  : Word → Byte
  wstk : Stack
  rstk : Stack

structure State where
  pc : Word
  mem : Memory

-- The VM can read and write from opaque ports. The host determines
-- the mapping between ports and functions.

inductive Request where
  | read8   (port : Byte)
  | read16  (port : Byte)
  | write8  (port value : Byte)
  | write16 (port low high : Byte)

def Request.Result : Request → Type
  | .read8 _       => Byte
  | .read16 _      => Word
  | .write8 _ _    => Unit
  | .write16 _ _ _ => Unit

structure Patch where
  ramWrites : List (Word × Byte) := []
  wstPtr : Option Byte := none
  rstPtr : Option Byte := none

def Patch.apply (patch : Patch) (s : State) : State :=
  { s with
    mem.ram := patch.ramWrites.foldl
      (fun ram (address, value) => Function.update ram address value) s.mem.ram
    mem.wstk.ptr := patch.wstPtr.getD s.mem.wstk.ptr
    mem.rstk.ptr := patch.rstPtr.getD s.mem.rstk.ptr }

structure Reply (request : Request) where
  reply : request.Result
  patch : Patch

-- A single step returns the VM state, either ready to continue or stopped by BRK.

inductive Outcome where
  | next : State → Outcome
  | brk  : State → Outcome

inductive Step where
  | done : Outcome → Step
  | request (r : Request) (s : State) (k : Reply r → Outcome) : Step

structure Mode where
  short : Bool
  keep  : Bool
  ret   : Bool

-- Instructions and their decoding.

inductive Op where
  | inc | pop | nip | swp | rot | dup | ovr
  | equ | neq | gth | lth
  | jmp | jcn | jsr | sth
  | ldz | stz | ldr | str | lda | sta
  | dei | deo
  | add | sub | mul | div | and | ora | eor | sft

inductive Instruction where
  | brk
  | jci  | jmi  | jsi
  | lit (short ret : Bool)
  | normal : Op → Mode → Instruction

def Instruction.ofByte (b : Byte) : Instruction :=
  let op := b.setWidth 5
  let mode : Mode :=
    { short := b.getLsbD 5, ret := b.getLsbD 6, keep := b.getLsbD 7 }
  let normal : Op → Instruction := (.normal · mode)
  match h : op.toNat with
  | 0 =>
    if mode.keep then .lit mode.short mode.ret
    else
      match mode.ret, mode.short with
      | false, false => .brk
      | false, true  => .jci
      | true,  false => .jmi
      | true,  true  => .jsi
  | 0x01 => normal .inc | 0x02 => normal .pop
  | 0x03 => normal .nip | 0x04 => normal .swp
  | 0x05 => normal .rot | 0x06 => normal .dup
  | 0x07 => normal .ovr | 0x08 => normal .equ
  | 0x09 => normal .neq | 0x0a => normal .gth
  | 0x0b => normal .lth | 0x0c => normal .jmp
  | 0x0d => normal .jcn | 0x0e => normal .jsr
  | 0x0f => normal .sth | 0x10 => normal .ldz
  | 0x11 => normal .stz | 0x12 => normal .ldr
  | 0x13 => normal .str | 0x14 => normal .lda
  | 0x15 => normal .sta | 0x16 => normal .dei
  | 0x17 => normal .deo | 0x18 => normal .add
  | 0x19 => normal .sub | 0x1a => normal .mul
  | 0x1b => normal .div | 0x1c => normal .and
  | 0x1d => normal .ora | 0x1e => normal .eor
  | 0x1f => normal .sft
  | _ + 32 => by
      have := op.isLt
      omega


--- A single step of the virtual machine.

def fetchByte : StateM State Byte :=
  modifyGet fun s => (s.mem.ram s.pc, { s with pc := s.pc + 1 })

def fetchInstruction : StateM State Instruction := do
  return Instruction.ofByte (← fetchByte)

def Stack.inc (value : Byte) : StateM Stack Unit :=
  modify fun s =>
    { s with data := Function.update s.data s.ptr value, ptr := s.ptr + 1 }

def Stack.dec : StateM Stack Byte :=
  modifyGet fun s => (s.data (s.ptr - 1), { s with ptr := s.ptr - 1 })

def withStack (ret : Bool) (action : StateM Stack α) : StateM State α :=
  modifyGet fun s =>
    let (value, stack) := action.run (if ret then s.mem.rstk else s.mem.wstk)
    (value, if ret then { s with mem.rstk := stack } else { s with mem.wstk := stack })

-- in keep mode, decrementing uses a cursor but doesn't change the
-- stack pointer. hence, M being an argument.
structure StackOps (m : Type → Type) where
  inc : Word → StateM State Unit
  dec : m Word
  inc8 : Byte → StateM State Unit
  dec8 : m Byte
  inc16 : Word → StateM State Unit
  dec16 : m Word

def StackOps.ofBytes [Monad m] (short : Bool)
    (inc8 : Byte → StateM State Unit) (dec8 : m Byte) : StackOps m :=
  let inc16 (value : Word) : StateM State Unit := do
    inc8 ((value >>> 8).setWidth 8)
    inc8 (value.setWidth 8)
  let dec16 : m Word := do
    return (← dec8).setWidth 16 ||| ((← dec8).setWidth 16 <<< 8)
  { inc := if short then inc16 else fun value => inc8 (value.setWidth 8)
    dec := if short then dec16 else do return (← dec8).setWidth 16
    inc8, dec8, inc16, dec16 }

def stackOps (ret short : Bool) : StackOps (StateM State) :=
  .ofBytes short (fun value => withStack ret (Stack.inc value)) (withStack ret Stack.dec)

structure ModeOps (m : Type → Type) extends StackOps m where
  secondary : StackOps (StateM State)
  jump : Word → StateM State Unit
  load : {n : Nat} → BitVec n → StateM State Word
  store : {n : Nat} → BitVec n → Word → StateM State Unit
  read : Byte → (request : Request) × (request.Result → Word)
  write : Byte → Word → Request

-- In keep mode, pops move a private cursor, leaving the stack pointer
-- unchanged.
def withMode (mode : Mode)
    (fn : {m : Type → Type} → [Monad m] → [MonadStateOf State m] →
      [MonadLiftT (StateM State) m] → ModeOps m → m Step) : StateM State Step := do
  let stack := stackOps mode.ret mode.short
  (fn (m := StateT Byte (StateM State))
    { toStackOps := .ofBytes mode.short stack.inc8
        (if mode.keep then do
          let source ← withStack mode.ret get
          modifyGet fun cursor =>
            let (value, popped) := Stack.dec.run { source with ptr := cursor }
            (value, popped.ptr)
         else stack.dec8)
      secondary := stackOps (!mode.ret) mode.short
      jump := fun offset => modify fun s =>
        { s with pc := if mode.short then offset
                       else s.pc + (offset.setWidth 8).signExtend 16 }
      load := fun address => do
        if mode.short then
          return (← get).mem.ram (address.setWidth 16) ++
            (← get).mem.ram ((address + 1).setWidth 16)
        else
          return ((← get).mem.ram (address.setWidth 16)).setWidth 16
      store := fun address value => modify fun s =>
        let ram := Function.update s.mem.ram (address.setWidth 16)
          ((if mode.short then value >>> 8 else value).setWidth 8)
        { s with mem.ram := if mode.short then
            Function.update ram ((address + 1).setWidth 16) (value.setWidth 8)
          else ram }
      read := fun port => if mode.short then ⟨.read16 port, fun value => value⟩
        else ⟨.read8 port, fun value => value.setWidth 16⟩
      write := fun port value => if mode.short then
          .write16 port (value.setWidth 8) ((value >>> 8).setWidth 8)
        else .write8 port (value.setWidth 8) }).run' (← withStack mode.ret get).ptr

def stepM : StateM State Step := do
  let imm : StateM State Word := do
    return (← fetchByte) ++ (← fetchByte)
  let jump (offset : Word) : StateM State Unit :=
    modify fun s => { s with pc := s.pc + offset }

  match ← fetchInstruction with
  | .brk => return .done (.brk (← get))
  | .jci =>
    if (← (stackOps false false).dec8) != 0 then
      jump (← imm)
    else
      jump 2
  | .jmi => jump (← imm)
  | .jsi =>
    let offset ← imm
    (stackOps true true).inc16 (← get).pc
    jump offset
  | .lit short ret =>
    if short then (stackOps ret false).inc8 (← fetchByte)
    (stackOps ret false).inc8 (← fetchByte)
  | .normal op mode =>
    return ← withMode mode fun ops => do
      match op with
      | .inc => ops.inc ((← ops.dec) + 1)
      | .pop => discard ops.dec
      | .nip =>
        let value ← ops.dec
        discard ops.dec
        ops.inc value
      | .swp =>
        let a ← ops.dec
        let b ← ops.dec
        ops.inc a
        ops.inc b
      | .rot =>
        let a ← ops.dec
        let b ← ops.dec
        let c ← ops.dec
        ops.inc b
        ops.inc a
        ops.inc c
      | .dup =>
        let value ← ops.dec
        ops.inc value
        ops.inc value
      | .ovr =>
        let a ← ops.dec
        let b ← ops.dec
        ops.inc b
        ops.inc a
        ops.inc b
      | .equ => ops.inc8 (if (← ops.dec) == (← ops.dec) then 1 else 0)
      | .neq => ops.inc8 (if (← ops.dec) != (← ops.dec) then 1 else 0)
      | .gth => ops.inc8 (if (← ops.dec) < (← ops.dec) then 1 else 0)
      | .lth => ops.inc8 (if (← ops.dec) > (← ops.dec) then 1 else 0)
      | .jmp => ops.jump (← ops.dec)
      | .jcn =>
        let offset ← ops.dec
        if (← ops.dec8) != 0 then ops.jump offset
      | .jsr =>
        let offset ← ops.dec
        ops.secondary.inc16 (← get).pc
        ops.jump offset
      | .sth => ops.secondary.inc (← ops.dec)
      | .ldz => ops.inc (← ops.load (← ops.dec8))
      | .stz =>
        let address ← ops.dec8
        ops.store address (← ops.dec)
      | .ldr =>
        ops.inc (← ops.load ((← get).pc + (← ops.dec8).signExtend 16))
      | .str =>
        let offset ← ops.dec8
        ops.store ((← get).pc + offset.signExtend 16) (← ops.dec)
      | .lda => ops.inc (← ops.load (← ops.dec16))
      | .sta =>
        let address ← ops.dec16
        ops.store address (← ops.dec)
      | .dei =>
        let ⟨request, value⟩ := ops.read (← ops.dec8)
        let s ← get
        return .request request s fun reply =>
          .next ((ops.inc (value reply.reply)).run (reply.patch.apply s)).2
      | .deo =>
        let port ← ops.dec8
        let request := ops.write port (← ops.dec)
        let s ← get
        return .request request s fun reply => .next (reply.patch.apply s)
      | .add => ops.inc ((← ops.dec) + (← ops.dec))
      | .sub =>
        let a ← ops.dec
        ops.inc ((← ops.dec) - a)
      | .mul => ops.inc ((← ops.dec) * (← ops.dec))
      | .div =>
        let divisor ← ops.dec
        -- BitVec division returns zero for a zero divisor.
        ops.inc ((← ops.dec) / divisor)
      | .and => ops.inc ((← ops.dec) &&& (← ops.dec))
      | .ora => ops.inc ((← ops.dec) ||| (← ops.dec))
      | .eor => ops.inc ((← ops.dec) ^^^ (← ops.dec))
      | .sft =>
        let shift ← ops.dec8
        ops.inc ((← ops.dec) >>> (shift &&& 0x0f).toNat <<< (shift >>> 4).toNat)
      return .done (.next (← get))

  return .done (.next (← get))

def step (s : State) : Step := (stepM.run s).1

end Uxn
