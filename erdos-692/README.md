# Erdős #692: a valley in the divisor-interval density

Let \(\delta_1(n,m)\) be the natural density of the integers having exactly one
divisor in the open interval \((n,m)\). Erdős asked whether, for each fixed
\(n\), the sequence \(m \mapsto \delta_1(n,m)\) is unimodal on \(m > n+1\).
Cambie answered no in *Resolution of Erdős' problems about unimodularity*
(Journal of Number Theory 280, 2026, 271–277; arXiv:2501.10333), and this
package gives a complete Lean 4 proof of his \(n = 3\) counterexample.

The relevant densities are exact rational numbers,
\[
\delta_1(3,6) = \frac{7}{20}, \qquad
\delta_1(3,7) = \frac{1}{3}, \qquad
\delta_1(3,8) = \frac{38}{105},
\]
so the sequence drops at \(m = 7\) and rises again at \(m = 8\). Since
\(\tfrac13 < \tfrac{7}{20} < \tfrac{38}{105}\), \(m = 7\) is a strict valley and
the sequence is not unimodal.

## Statement and proof

[Challenge.lean](Challenge.lean) states the target with Mathlib alone. The
statement is
`Erdos692.erdos_692_variants_cambie_three`, the declaration
`erdos_692.variants.cambie_three` in the pinned
[Formal Conjectures entry](https://github.com/google-deepmind/formal-conjectures/blob/0214b275653a2aa8fe5e44f01a0954723516801f/FormalConjectures/ErdosProblems/692.lean),
which quantifies over *every* function \(\delta : \mathbb{N} \to \mathbb{N} \to \mathbb{R}\)
whose values are densities of the corresponding divisor sets:

```lean
∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
  δ 3 7 < δ 3 6 ∧ δ 3 7 < δ 3 8
```

[Solution.lean](Solution.lean) proves it as
`Erdos692.erdos_692_variants_cambie_three`; the work is in
[DivisorIntervalDensityAndExtrema692.lean](Proofs/DivisorIntervalDensityAndExtrema692.lean).

The proof has two ingredients. The counting argument in
[PlbyErdos692.lean](Proofs/PlbyErdos692.lean) observes that "having exactly one
divisor in \((n,m)\)" is periodic modulo \(L = \operatorname{lcm}(n+1,\dots,m-1)\),
so each density is a ratio of two explicit finite counts; for \((3,6)\), \((3,7)\)
and \((3,8)\) the proportions are \(7/20\), \(20/60\) and \(152/420\).

That computation concerns one particular density function. The bridge
`isDelta1_delta1` proves that the periodic residue proportion really is the
natural density in the sense of the Formal Conjectures definition
(`Set.HasDensity` of `Set.partialDensity`), for every pair \((n,m)\). Uniqueness
of limits (`isDelta1_unique`) then forces every admissible \(\delta\) to agree
with the explicit values, which turns the rational comparison into the stated
inequality.

## Scope

This is exactly the upstream declaration: `FCCompare` matches
`Erdos692.erdos_692.variants.cambie_three` against the solution in `exact` mode,
and `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.

At the pinned commit the declaration is still `sorry` with no `formal_proof`
link, so the package supplies a proof that did not previously exist. The
companion results are auxiliary and are not exported:

- `erdos_692_parts_i` proves Part (i) in the `False ↔ …` form. That declaration
  already carries an external `formal_proof` link upstream, so this reproof is
  a duplicate.
- `cambie_two_lt` and `not_unimodularOn_delta_two` record Cambie's \(n = 2\)
  valley, for which there is no separate upstream declaration.
- `erdos_692_parts_ii_zero`, `erdos_692_parts_ii_one_three` and
  `erdos_692_parts_ii_one_four` settle the \(n = 0\) and \(n = 1\) endpoint
  cases of Part (ii), the open question about where the maximum is attained.
  The general case is untouched.

Part (ii), `erdos_upper_bound` and `cambie_local_maxima` remain open or are not
addressed here, so nothing in this package resolves the original problem.

## Provenance

Cambie's paper supplies the counterexample. The explicit periodic counts and
their evaluation are adapted from Pietro Monticone's Apache-2.0 Lean gist, which
is retained as `Proofs/PlbyErdos692.lean` with its original copyright notice.
The density bridge, the uniqueness argument and the small-\(n\) endpoint results
are developed here. See [THIRD_PARTY.md](THIRD_PARTY.md) and
[formalization.yaml](formalization.yaml) for the full attribution.

## Verification

Run `./verify.sh`

The package builds in Lean `4.35.0-rc2` against Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. See [BUILD.md](BUILD.md).
