Example programs for differential testing.

To recompile and verify examples as part of the test suite,

```sh
python3 tests/run.py
```

These examples are kindly provided by Devine Lu Linvega under the MIT
license (`LICENSE.upstream`).

`fibonacci` adapts the upstream routine to read one raw byte from stdin and
leave its 16-bit result on the working stack, with no console output.
