import ProgramProofs.Host.State
import Uxn.Host

namespace ProgramProofs.Host
open Uxn

@[uxn_state] theorem state_bind_apply {m : Type → Type} [Monad m]
    {σ α β : Type} (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f) s = (do let (a, s') ← x s; f a s') := rfl

@[uxn_state] theorem state_pure_apply {m : Type → Type} [Monad m]
    {σ α : Type} (a : α) (s : σ) :
    (pure a : StateT σ m α) s = pure (a, s) := rfl

@[uxn_state] theorem state_get_apply {m : Type → Type} [Monad m]
    {σ : Type} (s : σ) : (get : StateT σ m σ) s = pure (s, s) := rfl

@[uxn_state] theorem state_modify_apply {m : Type → Type} [Monad m]
    {σ : Type} (f : σ → σ) (s : σ) :
    (modify f : StateT σ m PUnit) s = pure (PUnit.unit, f s) := rfl

@[uxn_state] theorem state_modifyGet_apply {m : Type → Type} [Monad m]
    {σ α : Type} (f : σ → α × σ) (s : σ) :
    (modifyGet f : StateT σ m α) s = pure (f s) := rfl

@[uxn_state] theorem state_lift_apply {m : Type → Type} [Monad m]
    {σ α : Type} (x : m α) (s : σ) :
    (liftM x : StateT σ m α) s = (do let a ← x; pure (a, s)) := rfl

@[uxn_state] theorem state_map_apply {m : Type → Type} [Monad m]
    {σ α β : Type} (f : α → β) (x : StateT σ m α) (s : σ) :
    (f <$> x) s = (do let (a, s') ← x s; pure (f a, s')) := rfl

attribute [uxn_state] StateT.run StateT.run' Id.run
  StateT.bind StateT.pure StateT.get StateT.modifyGet StateT.map
  get getThe modify modifyGet MonadStateOf.get MonadStateOf.modifyGet
  liftM monadLift MonadLift.monadLift StateT.lift

@[uxn_state] theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl
@[uxn_state] theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
@[uxn_state] theorem id_map {α β : Type} (f : α → β) (x : Id α) : (f <$> x) = f x := rfl

attribute [uxn_step]
  machine Stack.empty Stack.push Stack.pushWord
  Uxn.step stepM fetchInstruction fetchByte Uxn.Instruction.ofByte
  withMode stackOps StackOps.ofBytes withStack Uxn.Stack.inc Uxn.Stack.dec
  discard Functor.mapConst Function.const join_bytes append_split
  BitVec.sub_eq_add_neg BitVec.add_assoc

attribute [uxn_state]
  Host.Port.System.state
  Host.Port.Console.vector Host.Port.Console.vectorLow
  Host.Port.Console.read Host.Port.Console.type
  Host.Port.Console.write Host.Port.Console.error

end ProgramProofs.Host
