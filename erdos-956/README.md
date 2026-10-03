# Erdős #956: unit distances between disjoint convex translates

This package targets Lean 4.35.0-rc2 and formalizes the affirmative superlinear solution and $\Omega(N^{4/3})$ lower bounds for [Erdős problem #956](https://www.erdosproblems.com/956).

For a compact convex planar set $C \subset \mathbb{R}^2$, the set-distance between two translates $C + x$ and $C + y$ is

$$\delta(C+x, C+y) = \inf_{c, d \in C} \|(c + x) - (d + y)\|_2,$$

and $h(n)$ denotes the maximum number of unordered pairs at set-distance $1$ among $n$ pairwise-disjoint translates of a single $C$. [Erdős and Pach (1990)](https://doi.org/10.1007/BF02122780) proved $h(n) = O(n^{4/3})$ and asked whether $h(n) > n^{1+c}$ for some constant $c > 0$ and all sufficiently large $n$. [Valtr (2005)](https://ems.press/content/serial-article-files/45990?nt=1) announced $h(n) = \Theta(n^{4/3})$, and [Chojecki (April 2026)](https://www.ulam.ai/research/erdos956.pdf) gave a six-page elementary construction using a one-sided parabolic cap and two rectangular layers.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exposes six unconditional theorems with zero `sorry` and only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Declaration | Meaning |
| --- | --- |
| `Erdos956.Palomar.erdos_956_superlinear` | Direct affirmative solution: $\exists c > 0,\ \forall^\infty n \in \mathbb{N},\ n^{1+c} < h(n)$ (with $c = 1/4$). |
| `Erdos956.Palomar.erdos_956` | Elaborated Formal Conjectures `True ↔` form of Erdős #956. |
| `Erdos956.Palomar.erdos_956_omega_four_thirds` | Explicit all-$N$ lower bound: $\frac{1}{1000} N^{4/3} \le h(N)$ for all $N \ge 30$. |
| `Erdos956.Palomar.erdos_956_four_layer_polynomial` | Exact four-layer signed-grid bound: $72q^4 + 32q^3 + 24q^2 + 13q + 3 \le h(48q^3 + 16q^2 + 12q + 4)$ for all $q \ge 1$. |
| `Erdos956.Palomar.erdos_956_eventual_two_fifths` | Sharp eventual bound: $\frac{2}{5} N^{4/3} < h(N)$ for all $N \ge N_{162} = 204{,}525{,}328$. |
| `Erdos956.erdos_956` | Literal Formal Conjectures statement over `Erdos956.Extremal.h`. |

[Challenge.lean](Challenge.lean) is a standalone Mathlib-only benchmark declaring `Plane`, `translateDistance`, `IsConfiguration`, `unitPairs`, `h`, and the five `Erdos956.Palomar` theorem targets with intentional `sorry` placeholders. [comparator.json](comparator.json) compares all five theorems in `Challenge` and `Solution` using both NanoDa and Lean's default kernel.

[Statement.lean](Statement.lean) records the literal Formal Conjectures proposition `statement` with no admitted theorem or placeholder. [AxiomAudit.lean](AxiomAudit.lean) proves definitional statement fidelity (`statement_fidelity`) and the finite non-vacuity control `nonvacuity_h_80 : 144 ≤ h 80`, and audits the transitive axioms of all public endpoints.

## Proof architecture

[Proofs/Erdos956SignedFourLayer435.lean](Proofs/Erdos956SignedFourLayer435.lean) is a self-contained 3,193-line Lean 4.35.0-rc2 development organized into eight sections:

1. **Signed Parabolic Cap Geometry (`Erdos956.Geometry`)**: Proves the supporting-hyperplane inequality, exact unit distance `Metric.infDist = 1`, coordinate box containment `[-W^3/2, W^3/2] × [-W^4, W^4]`, compactness, convexity, central symmetry, and nonempty interior for `D = conv {±p(t) : t ∈ T}` over arbitrary finite signed parameter sets `T ⊆ [-W, W]`, handling opposite-sign parameters via the identity `(r_s r_t - (1 - st))(r_s r_t + (1 - st)) = (s + t)^2 ≥ 0`.
2. **Rational Grid Parameters (`Erdos956.Parameters`)**: Establishes the spacing inequalities `W^3/2 < a`, `η < b`, and `k^2 b < 1` for both unsigned `T(k)` and signed `signedT(k)`.
3. **Difference-Body & Remote Padding Reductions (`Erdos956`, `Erdos956.Padding`)**: Identifies `translateSetDistance C x y` with `Metric.infDist (y - x) (C - C)` for `C = (1/2) • D`, reduces closed-set disjointness to `y - x ∉ D`, and pads configurations with remote translates at `(10(j + 1), 0)`.
4. **Two-Layer Baseline (`Erdos956Centers`, `Erdos956Counting`, `Erdos956.Specification`)**: Constructs the two-layer parabolic grid at scale `k = 2m` with `m^4` unordered unit-distance pairs and proves `erdos956_full_answer` (`N ≥ 30`) and `erdos956_strict_superlinear_answer`.
5. **Extremal Function Bridge (`Erdos956.Extremal`)**: Proves `unitPairs_card_le_choose_two` and `attainable_bddAbove` so `le_csSup` transfers every configuration edge count to the `sSup` function `h(n)`.
6. **Four-Layer Signed-Grid Construction (`Erdos956.FourLayer`)**: Formalizes the four-layer signed grid (`m = 3q`, `ℓ = 4q^2`, `L = 4`) with `N_q = 48q^3 + 16q^2 + 12q + 4` translates and `J_q = 72q^4 + 32q^3 + 24q^2 + 13q + 3` unordered unit-distance edges (`J_1 = 144 <= h(80)`), and proves `(2/5) N^(4/3) < h(N)` for all `N ≥ N_162 = 204525328`.
7. **Faulhaber & Degree-21 Tail Polynomial Certificates (`Erdos956.PolynomialCertificates`)**: Proves the closed-form one-sided and two-layer signed edge polynomials and the degree-21 induced-subset tail polynomials `P_sharp(t + 51) > 0` (`P_sharp(50) < 0`) and `P_{2,5}(t + 64) > 0` (`P_{2,5}(63) < 0`).

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [SUBMISSION.md](SUBMISSION.md) for the Palomar submission checklist. All package modules compile from source under Lean `4.35.0-rc2` (`11acb17ec6b07a8f9e9173e6845197929540936b`) and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Both `./verify.sh --no-sandbox` and `lake env lake comparator --config comparator.json --inadvisably-no-sandbox` pass, with both `nanoda_bin` and Lean's default kernel accepting `Solution`.
