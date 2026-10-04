module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions and statement forms, and the MIT
License for the local proof development.

Adaptation notice: Linmiao Xu adapted the Erdős 546 statements and proved all
public endpoints in Lean 4.35.0-rc2 in 2026. This module does not import or
reference `Challenge`.
-/

public import Sudakov546
public import OriginalStatement546
public import SparseCut546
public import LowDensityRounded546
public import Amplification546


@[expose] public section

/-!
# Proved endpoints for Erdős Problem 546

This module exports all seven proved targets declared in `Challenge.lean`:
- `erdos_546_original_statement` from `OriginalStatement546`,
- `Erdos546.erdos_546`, `Erdos546.sudakov_sparse_bound`, and
  `Erdos546.sparse_graph_ramsey_witness` from `Sudakov546`,
- `Erdos546.boundedDegree_sparse_cut` from `SparseCut546`,
- `Erdos546.exists_monoPair_of_low_edgeDensity` from `LowDensityRounded546`, and
- `Erdos546.quantitative_monoPair_amplification` from `Amplification546`.
-/
