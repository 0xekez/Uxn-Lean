A Lean implementation of the [Uxn VM](https://wiki.xxiivv.com/site/uxn.html).

```sh
lake build
lake exe uxn examples/binaries/hello_world.rom
lake exe uxn examples/binaries/tictactoe.rom
```

Because it is implemented in Lean, one can prove properties of Uxn
programs running in the VM. For example,
`ProgramProofs/Sierpinski.lean` contains a function for printing a
triangle,

```lean
example : pascalTriangle 4 =
  "    * \n" ++
  "   * * \n" ++
  "  *   * \n" ++
  " * * * * \n" := by decide
```

and one can prove that running `examples/binaries/sierpinski.rom` in
the VM is equivalent to printing the triangle's bytes out.

```lean
theorem correct (k : Nat) (hk : k < 8) :
    ∃ final,
      Uxn.Host.run (rom (2 ^ k)) =
        (do
          for byte in (pascalTriangle (2 ^ k)).toUTF8.data.toList do
            (← IO.getStdout).write ⟨#[byte]⟩
          pure (0, final))
```

This states, there exists a return code (`0`) and `final` VM state
such that running the `.rom` file is equivalent to printing the
triangle and returning those values.

**Correctness.** These proofs are trustworthy if you trust the Lean
kernel and the [implementation's](Uxn/) faithfullness to the Uxn
specification. I have written some tests to compare behavior with
[`uxnmin.c`](https://wiki.xxiivv.com/etc/uxnmin.c.txt) and
[`uxnmin.tal`](https://wiki.xxiivv.com/etc/uxnmin.tal.txt) which you
may find convincing.

```python
# Check that IO and final VM state exactly matches uxnmin.c across 52
# example Uxn ROMs (including the canon opcode test).
python3 tests/run.py

# Run the above checks on nine example programs running inside
# self-hosted Uxn VM (uxnmin.tal) running inside the Lean VM versus
# uxnmin.c running uxnmin.tal running the programs.
python3 tests/run.py --extended

# Run the above checks on 1000 randomly generated Uxn programs using
# eight parallel workers.
python3 tests/run.py 1000 --jobs 8 --seed 0
```

`ProgramProofs/` also contains a correctness proof for a Fibonacci and
HelloWorld program.
