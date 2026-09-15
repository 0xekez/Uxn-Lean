Proofs of IO action equalities for ROMs from `../examples`.

From `uxn-lean/`, run:

```sh
lake build ProgramProofs
```

For example, `../examples/binaries/fibonacci.rom` is a recursive
Fibonacci program. It reads a byte from standard input and leaves
the result on the working stack. In `Fibonacci.lean`, we prove that
for inputs from 0 through 24 this result agrees with `Nat.fib`:

```lean
theorem correct :
    ∃ final : Fin 25 → Uxn.Host.State,
    ∃ eof : Uxn.Host.State,
    ∃ onInvalid : Byte → IO (UInt32 × Uxn.Host.State),
      Uxn.Host.run rom =
        (do
          match (← (← IO.getStdin).read 1)[0]? with
          | none => pure (0, eof)
          | some b =>
            if h : b.toNat < 25 then pure (0, final ⟨b.toNat, h⟩)
            else onInvalid b.toBitVec) ∧
      eof.vm.mem.wstk.ptr = 0 ∧ eof.vm.mem.rstk.ptr = 0 ∧
      ∀ n : Fin 25,
        (final n).vm.mem.wstk.ptr = 2 ∧ (final n).vm.mem.rstk.ptr = 0 ∧
        ((final n).vm.mem.wstk.data 0 ++
          (final n).vm.mem.wstk.data 1).toNat = Nat.fib n.val
```

`Fin 25` is the type of natural numbers less than 25, so `final`
assigns a VM state to each supported input. For these inputs, the
first part states that running the ROM is equivalent to reading a byte
in Lean and returning zero and the corresponding state. The last three
lines check this returned state contains the correct number and leave
the working and return stacks in a good state.

The theorem leaves behavior for larger inputs and EOF largely
unspecified (`eof` and `onInvalid`).
