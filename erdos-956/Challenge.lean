/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adaptation notice: Linmiao Xu adapted the Erdős 956 definitions and statement
from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/956.lean`)
and added the explicit quantitative $\Omega(N^{4/3})$ and four-layer signed-grid
theorem targets for this standalone Lean 4 benchmark in 2026. This file
imports only Mathlib.
-/

import Mathlib

/-!
# Erdős Problem 956: unit distances between disjoint convex translates

For a compact convex planar set $C \subset \mathbb{R}^2$, define the set-distance
between translates $C + x$ and $C + y$ by
$$\delta(C+x, C+y) = \inf_{c, d \in C} \|(c + x) - (d + y)\|_2.$$
Let $h(n)$ be the maximum number of unordered pairs at set-distance $1$ among $n$
pairwise-disjoint translates of a single $C$. Erdős and Pach asked whether
$h(n) > n^{1+c}$ for some constant $c > 0$ and all sufficiently large $n$.

The five intentional `sorry` placeholders below are matched by proved declarations
in `Solution.lean`; `Solution.lean` does not import this module.
-/

namespace Erdos956.Palomar

open Filter

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Minimum Euclidean distance between the sets $C+x$ and $C+y$. -/
noncomputable def translateDistance (C : Set Plane) (x y : Plane) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

/-- A family of pairwise disjoint translates of one nonempty compact convex set. -/
def IsConfiguration (C : Set Plane) (X : Finset Plane) : Prop :=
  C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
    ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint ((· + x) '' C) ((· + y) '' C)

open scoped Classical in
/-- The unordered pairs of distinct centers whose translates have set-distance one. -/
noncomputable def unitPairs (C : Set Plane) (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 2).filter fun e =>
    ∃ x y : Plane, x ≠ y ∧ e = {x, y} ∧ translateDistance C x y = 1

/-- The maximum number of unordered unit-distance pairs among $n$ disjoint convex translates. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
    X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m}

/-- Direct affirmative solution to the Erdős–Pach superlinear question:
there exists $c > 0$ such that $n^{1+c} < h(n)$ for all sufficiently large $n$. -/
theorem erdos_956_superlinear :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ) := by
  sorry

/-- Elaborated Formal Conjectures `True ↔` form of Erdős Problem 956. -/
theorem erdos_956 : True ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ) := by
  sorry

/-- Explicit $\Omega(n^{4/3})$ lower bound for all $n \ge 80$:
$\frac{1}{26} n^{4/3} < h(n)$. -/
theorem erdos_956_omega_four_thirds :
    ∀ n : ℕ, 80 ≤ n → (1 / 26 : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 3) < (h n : ℝ) := by
  sorry

/-- Exact four-layer signed-grid polynomial lower bound at every scale $q \ge 1$:
$72 q^4 + 32 q^3 + 24 q^2 + 13 q + 3 \le h(48 q^3 + 16 q^2 + 12 q + 4)$. -/
theorem erdos_956_four_layer_polynomial :
    ∀ q : ℕ, 1 ≤ q →
      72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3 ≤
        h (48 * q ^ 3 + 16 * q ^ 2 + 12 * q + 4) := by
  sorry

/-- Sharp eventual $\frac{2}{5} n^{4/3}$ lower bound from the four-layer signed grid:
for all sufficiently large $n$, $\frac{2}{5} n^{4/3} < h(n)$. -/
theorem erdos_956_eventual_two_fifths :
    ∀ᶠ n : ℕ in atTop, (2 / 5 : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 3) < (h n : ℝ) := by
  sorry

end Erdos956.Palomar
