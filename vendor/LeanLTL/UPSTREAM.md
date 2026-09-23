# LeanLTL Core

Source: https://github.com/UCSCFormalMethods/LeanLTL
Revision: `d5473f06ab9d0ea652a51b2e78b11089731c4b6c`
Authors: Eric Vin, Kyle A. Miller, and Daniel J. Fremont.

This directory vendors the LTL core as a local Lake package for Lean/mathlib
4.33.1. The parent repository versions both the source snapshot and its
compatibility changes; no external fork or submodule checkout is required.

The `Var`, `Trace`, `Formula`, `sat`, and derived-connective definitions in
`LeanLTL/Logics/LTL/Core.lean` are unchanged text from upstream
`LeanLTL/Logics/LTL.lean`. The TraceSet translation and its supporting library
are not included. This is a port of the required core, not the full library.

Compatibility changes:

- Keep `LeanLTL/Init.lean` unchanged.
- In `ForMathlib.lean`, remove `ENat.one_lt_top` (now in mathlib) and replace
  the deprecated `ENat.coe_ne_top` with `ENat.natCast_ne_top`.
- In `Trace/Defs.lean`, rename `Option.isSome_map'` to `Option.isSome_map`
  and mark `Trace.inhabited` as `instance_reducible`.
- Split out the LTL definitions into `Logics/LTL/Core.lean`, with the three
  infinite-trace lemmas needed to elaborate their existing proofs. These
  correspond to upstream `Trace/Basic.lean` lemmas with current proofs.
- Set the package's Lean/mathlib versions to 4.33.1 and its root import to the core.

All compatibility lemmas are kernel-checked. There are no admitted proofs or
native-evaluation proofs. The recorded upstream revision has no license file;
this snapshot does not introduce a license on the upstream code.
