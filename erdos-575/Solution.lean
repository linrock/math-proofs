module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 OpenAI.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures and OpenAI definitions and statement forms, and
the MIT License for the local proof development.

Adaptation notice: Linmiao Xu adapted the Erdős 575 statements and proved all
public endpoints in Lean 4.35.0-rc2 in 2026. This module does not import or
reference `Challenge`.
-/

public import Erdos575
public import ForestCounterexample575


@[expose] public section

/-!
# Proved endpoints for Erdős Problem 575

This module exports all nine proved targets declared in `Challenge.lean`:
- `Erdos575.erdos_575` and `Erdos575.erdos_575_unrestricted`: the elaborated
  `False ↔` Formal Conjectures statements for the cycle-containing and
  unrestricted formulations (from `Erdos575`),
- `Erdos575.not_erdos_575_corrected`, `Erdos575.not_erdos_575`, and
  `Erdos575.not_erdos_575_all_bipartite`: direct disproofs of the
  cycle-containing, unrestricted, and all-bipartite cyclic compactness
  statements (from `Erdos575`),
- `Erdos575.correctedCounterexample` and `Erdos575.quantitativeCounterexample`:
  qualitative and quantitative (`ex(n; H) ≥ c n^(4/3)` vs.
  `ex(n; F)^16 ≤ C n^21`, exponent gap `1 / 48`) connected, bipartite, cyclic
  counterexample theorems (from `Erdos575` and `CompactnessAndDegeneracy`), and
- `Erdos575.ForestCounterexample.forestFamily_not_isBipartiteCompact` and
  `Erdos575.ForestCounterexample.forestCounterexample`: the self-contained
  pure-Mathlib bipartite forest counterexample `F_0 = {K_{1,2}, 2K_2}` with
  `ex(n; F_0) ≤ 1`, `ex(n; K_{1,2}) ≥ ⌊n / 2⌋`, and `ex(n; 2K_2) ≥ n - 1`
  (from `ForestCounterexample575`).
-/
