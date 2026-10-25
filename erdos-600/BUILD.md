# Build and audit Erdős #600

Run the following commands from this directory. Elan selects the exact compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`. The canonical Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
./verify.sh
```

`./verify.sh` builds `Statement`, `Solution`, `AxiomAudit` and `Challenge`, then checks that every exported endpoint depends only on `propext`, `Classical.choice` and `Quot.sound`.

To additionally recheck the exported theorems in the NanoDa and con-ron kernels and in Lean's default kernel:

```sh
./verify.sh --no-sandbox
```

The `--no-sandbox` flag is required because the kernel sandbox needs unprivileged user namespaces, which are unavailable in this environment. It runs the same three kernel checks without that sandbox.
