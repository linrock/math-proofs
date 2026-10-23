# Provenance and licenses for Erdős #306

The `erdos_306` and `erdos_306.variants.integer_three_primes` statements are
adapted from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/306.lean)
and appear in `Challenge.lean`, `Statement.lean`, `Solution.lean`, and the
`Representation` and Formal Conjectures bridge sections of
`Proofs/Erdos306Unified435.lean`. They retain the Formal Conjectures
Apache-2.0 notice. The license text is in
`third_party/FORMAL-CONJECTURES-LICENSE.txt`. No Formal Conjectures source
module is imported.

The sections titled "Li (2026)" in `Proofs/Erdos306Unified435.lean` adapt
Shisheng Li's Lean development accompanying
[arXiv:2609.32140v1](https://arxiv.org/abs/2609.32140v1)
([daizisheng/erdos-306](https://github.com/daizisheng/erdos-306), commit
`1314c9a8bcedaaf986f61fb6cd7129a834116abb`), released under the
[Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/).
The changes are a port from Lean 4.29.0-rc6 to Lean 4.35.0-rc2 with updated
Mathlib names, the merge of its thirteen modules into one file, and added
finite-set and three-prime corollaries. Li's framework adapts Yuren Tang's
earlier Lean proof ([doi:10.5281/zenodo.20767390](https://doi.org/10.5281/zenodo.20767390));
no code from Tang's repository is included.

The three-prime integer theorem was first proved by Butler, Erdős, and
Graham (Integers 15 (2015), A51). Its formal proof here is an independent
derivation from Li's construction.

Mathlib (`leanprover-community/mathlib4` at
`065356127b1dc0016f66b7283ce0ce2c4055aa55`) and its dependencies retain their
own Apache-2.0 licenses and commit pins.

The remaining locally authored material is Copyright 2026 Linmiao Xu and
released under the Apache-2.0 license in `LICENSE`, matching
`formalization.yaml`. This grant does not claim authorship of prior
mathematics or change the licenses of third-party sources.
