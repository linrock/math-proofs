# Build and verify

The package is pinned to Lean 4.35.0-rc2 and Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Lake links to the shared pinned package cache when it is available.

A fast hygiene and manifest check omits `--verify`. The full check builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge`, performs the challenge/solution environment comparison, and audits the exported theorem's transitive axioms.
