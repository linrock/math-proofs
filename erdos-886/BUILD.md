# Building and Verifying `erdos-886`

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`

## Build and Audit Commands

```bash
lake build Statement Solution AxiomAudit Challenge
./verify.sh
```

`Challenge.lean` states the 24 target declarations with `sorry`; `Solution.lean` imports the proof modules under `Proofs/` and proves the identical declarations. `AxiomAudit.lean` runs `#print axioms` on every declaration in `comparator.json` and checks that only `propext`, `Classical.choice`, and `Quot.sound` appear.
