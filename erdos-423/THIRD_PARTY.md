# Third-Party Notices

## Mathlib4

This package imports Mathlib, the community library for Lean 4 at
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4), licensed under
Apache-2.0 and copyright its contributors. The pinned revision is
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Formal Conjectures

The problem statement and the definitions `IsConsecutiveBlockSum` and `IsHofstadterSeq` come from
[Google DeepMind's Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/423.lean),
licensed under Apache-2.0 with the notice `Copyright 2026 The Formal Conjectures Authors`; the
package adapts these definitions and the inline small-term checks `erdos_423.test.a3` and
`erdos_423.test.a4` locally and introduces `IsGlobalConsecutiveBlockSum`. The five
structural API lemmas in the upstream file (`strictMono`, `le_apply`, `lt_iff_lt`,
`infinite_compl_of_unbounded`, `unbounded_of_infinite_compl`) were proved inline there by
contributor liudongdong in pull request 6055; this package reproves them locally and imports no
upstream module.

## lean-fc-proofs

[`anatoliiohorodnyk/lean-fc-proofs`](https://github.com/anatoliiohorodnyk/lean-fc-proofs),
Apache-2.0, written by Anatolii Ohorodnyk, contains an independent Lean proof of the
nondecreasing-excess variant of Erdős Problem 423. The corresponding theorem here is a re-proof of
an already registered result and is not presented as new. No file from that repository is copied or
imported.

## Mathematical sources

The mathematical arguments are due to Michael Bolan, *Hofstader-Ulam sequence* (expository note),
and Quanyu Tang, *The Hofstadter consecutive-sum sequence omits infinitely many positive
integers* ([arXiv:2603.09939](https://arxiv.org/abs/2603.09939)). The convex-sumset exponent
688/413 is quoted from A. Cushman, *A note on the sum-product problem and the convex sumset
problem* ([arXiv:2512.13849](https://arxiv.org/abs/2512.13849)); it is not reproved here. The term
sequence is OEIS [A005243](https://oeis.org/A005243).

## License of this package

The Lean sources in this package carry `Copyright 2025-2026 The Formal Conjectures Authors` and
`Copyright 2026 Linmiao Xu`, under Apache-2.0.
