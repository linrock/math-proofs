# Build Instructions

The package is pinned to Lean `4.35.0-rc2` (`leanprover/lean4:v4.35.0-rc2`) and to Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; `lean-toolchain` and `lake-manifest.json` record both
pins.

To build and verify everything in the package:

```bash
./verify.sh
```

The script checks that each Lean module starts with a `module` header and stays within the size
limit, builds `Solution`, `AxiomAudit`, and `Challenge`, replays the axiom audit for the exported
theorem, and then runs the Comparator with its sandbox enabled. To run the same steps while letting
the Comparator start without its sandbox on a machine where the sandbox cannot be created, use the
command below. That mode reports a sandbox-disabled warning, and its Comparator output is a local
diagnostic rather than a trustworthy verification:

```bash
./verify.sh --no-sandbox
```

The individual Lake targets can also be built directly:

```bash
lake build Solution AxiomAudit Challenge
```
