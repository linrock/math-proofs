# Build instructions

The package targets Lean `4.35.0-rc2` (`leanprover/lean4:v4.35.0-rc2`) with
Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`, both pinned in
`lean-toolchain` and `lakefile.toml`.

From this directory:

```bash
./verify.sh
```

This checks the module headers, builds `Statement`, `Solution`, `AxiomAudit` and
`Challenge`, and confirms that `#print axioms` reports one theorem depending only
on `propext`, `Classical.choice` and `Quot.sound`. Adding `--no-sandbox` also runs
Comparator.

For the full gate, including `FCCompare` against the precompiled Formal
Conjectures module and the Statement duplicate, run from the repository root:

`Solution.lean` proves the target; `Challenge.lean` restates it with `sorry` and
is deliberately not imported by the solution.
