# Erdős #973: power sums cannot all be exponentially small

This standalone Lean 4.35.0-rc2 project gives a complete formal proof of the
negative answer to Erdős problem 973. The question asks whether, for every
`n ≥ 2`, one can choose `n` complex numbers on or outside the unit circle,
with `z₁ = 1`, so that all their power sums of orders `2` through `n+1` have
magnitude below `C^(-n)` for a single fixed `C > 1`. The answer is **no**.

The project also proves a stronger statement than this negative answer:
for each fixed `C > 1`, once `n` is large enough, every choice of `n` such
numbers has some `2 ≤ k ≤ n+1` with `|∑_i z_i^k| > C^(-n)`. The threshold
depends only on `C`. Repeated points and points on the unit circle are
allowed, and `z₁ = 1` is not required.

The contribution is a complete machine-checked proof of known mathematics:
the negative answer and this uniform bound were already proved by
[Luo, Yang, and Zhu](https://arxiv.org/abs/2607.22017v1). The formalization
follows the residual-polynomial method of
[Tan, Wang, Huang, and Chen](https://arxiv.org/abs/2608.02043v3).

[Solution.lean](Solution.lean) proves
`Erdos973.Palomar.not_erdos_973` and
`Erdos973.Palomar.eventually_exterior_power_sum_strict_lower_bound`.
The prefix `not_` means that the first theorem proves `¬ OriginalStatement`:
the proposed constant does not exist. The second theorem states the uniform
lower bound above. These fully qualified Lean names are the identifiers used
by Palomar's verification tools.
[Challenge.lean](Challenge.lean) independently states the same two targets
using only Mathlib and contains intentional statement placeholders.
Solution does not import Challenge. The 11 [Proofs](Proofs) modules provide the
mathematical argument. [AxiomAudit.lean](AxiomAudit.lean) checks the two
selected endpoints.

## Attribution and scope

The [Erdős #973 problem record](https://www.erdosproblems.com/973) traces this
exterior question to [Erdős's 1965 paper, p. 213](https://www.renyi.hu/~p_erdos/1965-17.pdf).
The interior construction discussed there has a different condition on the
points and is outside this theorem.

[Luo, Yang, and Zhu](https://arxiv.org/abs/2607.22017v1) presented the
qualitative negative answer. This formalization follows the residual
polynomial method of [Tan, Wang, Huang, and Chen](https://arxiv.org/abs/2608.02043v3),
using a fixed test degree for the qualitative conclusion. Their stronger
square-root logarithmic residual estimate is outside this package. Neither
paper is assumed as an axiom.

## Proof outline

1. [NewtonBridge973](Proofs/NewtonBridge973.lean),
   [Normalization973](Proofs/Normalization973.lean), and
   [TaylorResidual973](Proofs/TaylorResidual973.lean) turn small original
   power sums into a small differential residual for a normalized
   reciprocal-root polynomial.
2. [ZeroSeparation973](Proofs/ZeroSeparation973.lean) separates its zeros
   from the boundary point. [TransformedRoots973](Proofs/TransformedRoots973.lean)
   then gives bounded points with real part at least `1/2`.
3. [HigherMoments973](Proofs/HigherMoments973.lean) makes a fixed window of
   those points' normalized moments small. A fixed test polynomial in
   [MomentObstruction973](Proofs/MomentObstruction973.lean) forces one of
   those moments to be large. [ExteriorPowerSums973](Proofs/ExteriorPowerSums973.lean)
   derives the eventual contradiction and the original negative answer.

The project gives no explicit threshold `N(C)` and no optimized residual rate.

## Earlier Lean work and production

The pinned [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/5d65ac9b140a00051fe2827fb10911beb2201b3b/FormalConjectures/ErdosProblems/973.lean)
is reproduced in an independent Mathlib-only Challenge. Its declaration is
not a proof. A [proposed Formal Conjectures update](https://github.com/google-deepmind/formal-conjectures/pull/4862)
records the negative paper answer and adds a uniform eventual-bound variant.
Both proposed declarations still end in `sorry`. The
[public Lean project accompanying Luo–Yang–Zhu](https://github.com/miracleqihe/Erdos-973_solution_check-by-Lean)
checks several components but explicitly leaves the full theorem outside Lean.
No proof source from either project is imported here.

Linmiao Xu is recorded as the human author and responsible maintainer of this
formalization. The local build and endpoint axiom audit do not constitute human
specialist review.

The independently reproduced Formal Conjectures statement retains its
Apache-2.0 notice in `Challenge.lean`, `Solution.lean`, and
`Proofs/Statement973.lean`, with the accompanying
[license text](third_party/FORMAL-CONJECTURES-LICENSE.txt). The exact statement
revision is recorded in Challenge. Local proof-file hashes are recorded in
[source-manifest.json](source-manifest.json). Its research paths record
provenance and are not build dependencies. See [THIRD_PARTY.md](THIRD_PARTY.md)
for the remaining attribution boundary.

## Reproduce and submission status

[BUILD.md](BUILD.md) gives the pinned toolchain, dependency, build, and axiom
checks. [comparator.json](comparator.json) names both theorem endpoints.
Palomar enables NanoDa through its protected verification configuration.
[formalization.yaml](formalization.yaml) records Linmiao Xu as author and
maintainer and the [MIT license](../LICENSE) for locally authored material.
This remains a prepared candidate and has not been submitted to or registered
with Palomar.
