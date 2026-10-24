# Third-party notices

- **Mathlib4**, revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`: Apache
  License 2.0. The package imports Mathlib for finite sets, real logarithms,
  filters, and the elementary inequalities used in the proof.
- **Formal Conjectures**, files
  `FormalConjecturesForMathlib/Combinatorics/Additive/RestrictedSumset.lean`
  and `FormalConjectures/ErdosProblems/787.lean` at commit
  `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`: Copyright 2026 The Formal
  Conjectures Authors, Apache License 2.0. `Finset.restrictedSumset` comes from
  `FormalConjecturesForMathlib/Combinatorics/Additive/RestrictedSumset.lean`;
  the definition of `g`, the helper lemmas `disjoint_restrictedSumset_iff` and
  `le_g`, and the target statement `erdos_787.variants.klarner` follow
  `FormalConjectures/ErdosProblems/787.lean`, all at that pinned commit. The
  package states the definitions locally rather than importing the upstream
  modules.

The helper lemmas `disjoint_restrictedSumset_iff` and `le_g` in
`Proofs/Erdos787Proofs.lean` are adapted from
`FormalConjectures/ErdosProblems/787.lean` (Copyright 2026 The Formal
Conjectures Authors, Apache License 2.0). The conflict-peeling argument itself
is package-local. The mathematical result and its attribution come from the
published literature cited in `formalization.yaml`:

- P. Erdős, "Extremal problems in number theory," Proceedings of Symposia in
  Pure Mathematics, Vol. VIII (1965), 181–189, especially p. 187.
- S. L. G. Choi, "On a combinatorial problem in number theory," Proceedings of
  the London Mathematical Society (3) 23 (1971), 629–642, especially p. 630.
- I. Z. Ruzsa, "Sum-avoiding subsets," The Ramanujan Journal 9 (2005), 77–82,
  DOI 10.1007/s11139-005-0826-4.
- Tom Sanders, "The Erdős-Moser sum-free set problem," Canadian Journal of
  Mathematics 73 (2021), 63–107.
- A. Beker, "The Erdős-Moser sum-free set problem via improved bounds for
  k-configurations," arXiv:2501.10203 (2025).

Bibliographic facts only are used from these papers. No text, table, or figure
is copied. The package is released under the Apache License 2.0; see `LICENSE`.
