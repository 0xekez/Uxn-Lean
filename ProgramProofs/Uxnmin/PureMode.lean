import ProgramProofs.Uxnmin.GuestStack

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ProgramProofs.Uxnmin
open Uxn ProgramProofs.Host

/-- The stack-only part of a mode, permitting a returned operand value. -/
def pureMode {α : Type} (mode : Mode)
    (fn : {m : Type → Type} → [Monad m] → [MonadStateOf Uxn.State m] →
      [MonadLiftT (StateM Uxn.State) m] → StackOps m → m α) : StateM Uxn.State α := do
  let stack := stackOps mode.ret mode.short
  (fn (m := StateT Byte (StateM Uxn.State))
    (.ofBytes mode.short stack.inc8
      (if mode.keep then do
        let source ← withStack mode.ret get
        modifyGet fun cursor =>
          let (value, popped) := Uxn.Stack.dec.run { source with ptr := cursor }
          (value, popped.ptr)
      else stack.dec8))).run' (← withStack mode.ret get).ptr

theorem pureMode_bind {α β : Type} (mode : Mode)
    (fn : {m : Type → Type} → [Monad m] → [MonadStateOf Uxn.State m] →
      [MonadLiftT (StateM Uxn.State) m] → StackOps m → m α)
    (finish : α → StateM Uxn.State β) :
    pureMode mode (fun ops => do let value ← fn ops; finish value) =
      (do let value ← pureMode mode fn; finish value) := by
  funext guest
  rfl

def takeThree (mode : Mode) : StateM Uxn.State (Word × Word × Word) :=
  pureMode mode fun ops => do
    let first ← ops.dec
    let second ← ops.dec
    let third ← ops.dec
    return (first, second, third)

theorem stack_inc (ret short : Bool) (value : Word) (guest : Uxn.State) :
    (stackOps ret short).inc value guest = ((), pushStack guest ret short value) := by
  cases ret <;> cases short <;> rfl

end ProgramProofs.Uxnmin
