# Build and audit Erdős #902

Run the following commands from this directory. Elan selects the exact compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`. The canonical Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
./verify.sh
```

`./verify.sh` builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge`, then checks that every
exported endpoint depends only on `propext`, `Classical.choice`, and `Quot.sound`. It does not run
Comparator.

To run Comparator under its built-in `bwrap` sandbox, which is the trustworthy mode, with NanoDa
and Lean's default kernel:

```sh
lake env lake comparator --config comparator.json
```

The sandbox needs a host that permits unprivileged mount namespaces. On a host that forbids them,
Comparator reports `bwrap: Can't mount proc` and stops. `./verify.sh --no-sandbox` passes
`--inadvisably-no-sandbox` for local diagnosis; its output is not a trustworthy Comparator result
and should not be treated as verification evidence.
