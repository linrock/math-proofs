# Build and audit Erdős #939

Run the following commands from this directory. Elan selects the exact compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`. The canonical Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
./verify.sh
```

To also run `comparator` locally with both NanoDa and Lean's default kernel:

```sh
./verify.sh --no-sandbox
```
