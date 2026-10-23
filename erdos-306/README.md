# Erdős #306: unit fractions with semiprime denominators

This standalone Lean 4.35.0-rc2 project gives a complete formal proof of the
affirmative answer to [Erdős problem 306](https://www.erdosproblems.com/306).
The question asks whether every positive rational `a/b` with `b` squarefree
can be written as `1/n₁ + ⋯ + 1/nₖ` with `1 < n₁ < ⋯ < nₖ`, where each `nᵢ`
is the product of two distinct primes. The answer is **yes**.

The formal proof follows Shisheng Li's elementary argument,
[*Unit fractions with semiprime denominators: an elementary proof of Erdős
Problem #306*](https://arxiv.org/abs/2609.32140v1) (September 2026), and ports
its [companion Lean development](https://github.com/daizisheng/erdos-306) to
Lean 4.35.0-rc2. The contribution here is a packaged, machine-checked proof of
known mathematics together with several finite results about representations
of `1`. No novelty is claimed for the main theorem.

[Solution.lean](Solution.lean) exports 19 theorems in `Erdos306` and
`Erdos306.variants`. [Challenge.lean](Challenge.lean) states the same 19 targets using only Mathlib
and contains intentional statement placeholders. Solution does not import
Challenge. [Statement.lean](Statement.lean) checks that the exported statements
match the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/306.lean),
and [AxiomAudit.lean](AxiomAudit.lean) prints the axioms of every endpoint.
Every endpoint depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Main results

| Theorem in `Solution.lean` | Statement |
| --- | --- |
| `erdos_306`, `variants.finset_omega_Omega` | The original question in the current upstream plain-proposition form, and a finite-set form. |
| `variants.integer_three_primes`, `variants.integer_three_primes_finset` | Every positive integer is a sum of reciprocals of distinct products of three distinct primes. |
| `variants.incidence_ten_iff` | `1` has a representation in which every prime divides at most `d` denominators if and only if `d ≥ 10`. |
| `variants.semiprime_card_ge_*`, `variants.prime_edges_card_ge_*` | When every prime divides at most ten denominators, a representation of `1` has at least 61 terms, and at least 63 if the number of terms is odd. |
| `variants.sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two` and its two corollaries | For any representation of `1`, with `q` ranging over the primes paired with `2`, `Σ q + 2·(number of terms) ≡ 2 (mod 4)`. |
| `variants.witness_{71,72,73}_cell_111` | Explicit 71-, 72-, and 73-term representations of `1` on primes up to 61, each prime dividing at most ten denominators. |

The main theorem is `Erdos306.erdos_306`; every other public result is in
`Erdos306.variants`.

## Attribution and scope

The question is from Erdős and Graham's 1980 monograph *Old and new problems
and results in combinatorial number theory*. Butler, Erdős, and Graham proved
the three-prime integer case in [Integers 15 (2015), A51](https://math.colgate.edu/~integers/p51/p51.pdf).
The formal proof here reaches that case differently: it dilutes Li's
two-prime construction by the prime `3`.

Yuren Tang gave the first Lean proof of the two-prime theorem
([doi:10.5281/zenodo.20767390](https://doi.org/10.5281/zenodo.20767390),
[repository](https://github.com/Yuren-Tang/erdos-306)), assuming two
Rosser–Schoenfeld (1962) prime estimates as axioms. Li adapts Tang's finite
Fourier framework, replaces its anchor synchronisation with a no-wrap Chinese
remainder lemma, and needs only Chebyshev-type bounds. Li's companion
development proves the large-`x` lower bound from Erdős's central binomial
argument instead of citing Ramanujan's inequality. No code from Tang's
repository is included, and neither paper is assumed as an axiom.

The incidence threshold, the term-count lower bounds, the mod-4 identity, and
the explicit witnesses are local finite results. They do not determine the
exact minimum number of terms in an incidence-10 representation of `1`. The
smallest verified example has 68 terms.

## Proof outline

1. [Erdos306Unified435](Proofs/Erdos306Unified435.lean) contains the port of
   Li's proof as one section per paper module: prime bounds (§2), reduction by
   prime dilution (§3), the bipartite construction and tuning lemma (§4),
   Fourier counting (§5), the row and column table (§6), major arcs (§7),
   single-column lemmas (§8), minor arcs (§9), and the Formal Conjectures
   bridge. The same file proves the incidence-nine mass bound, prime-row
   admissibility, row-potential duality, and the 68-term witnesses.
2. [HeadPrimeRowAdmissibilityDefectsAndMultiTailWitnesses306](Proofs/HeadPrimeRowAdmissibilityDefectsAndMultiTailWitnesses306.lean)
   proves the head-prime defect bounds and the 58-term lower bound.
3. [Blueprint306](Proofs/Blueprint306.lean) proves the 59-, 60-, and 61-term
   bounds, the mod-4 identity at `2`, the odd 63-term bound, the 71-, 72-,
   and 73-term witnesses, and the three-prime dilution.

Linmiao Xu is recorded as the human author and responsible maintainer of this
formalization. The local build and endpoint axiom audit do not constitute human
specialist review. See [BUILD.md](BUILD.md) for build commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for provenance and licenses.
