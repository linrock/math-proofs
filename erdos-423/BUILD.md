# Building and Verifying `erdos-423`

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`

## Build and Audit Commands

```bash
lake exe cache get
lake build Challenge Solution AxiomAudit Statement
./verify.sh
```

`./verify.sh` checks module headers and line limits, rebuilds `Statement`, `Solution`,
`AxiomAudit`, and `Challenge`, replays the axiom audit for all 24 exported theorems, and confirms
that each reports only `propext`, `Classical.choice`, and `Quot.sound`. Pass `--no-sandbox` to
additionally run the Comparator without its sandbox.
