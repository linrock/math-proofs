# Building and Verifying `erdos-726`

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`

## Build and Audit Commands

```bash
lake build Challenge Solution AxiomAudit Statement
./verify.sh
```
