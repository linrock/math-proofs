/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions and statement forms, and the MIT
License for the local proof development.

Adaptation notice: Linmiao Xu adapted the Erdős 956 statements and proved
all public endpoints in Lean 4 in 2026. This module does not import
or reference `Challenge`.
-/

import FourLayer956

/-!
# Erdős Problem 956: complete proved endpoints

This module proves the five independent targets in `Erdos956.Palomar` together
with the literal `Erdos956.erdos_956` declaration.
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

private theorem h_eq_extremal_h (n : ℕ) : h n = Erdos956.Extremal.h n := rfl

/-- Direct affirmative solution to the Erdős–Pach superlinear question:
there exists $c > 0$ such that $n^{1+c} < h(n)$ for all sufficiently large $n$. -/
theorem erdos_956_superlinear :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ) :=
  Erdos956.FourLayer.erdos_956_superlinear

/-- Elaborated Formal Conjectures `True ↔` form of Erdős Problem 956. -/
theorem erdos_956 : True ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ) :=
  ⟨fun _ => erdos_956_superlinear, fun _ => True.intro⟩

/-- Explicit $\Omega(N^{4/3})$ lower bound for all $N \ge 80$:
$\frac{1}{26} N^{4/3} < h(N)$. -/
theorem erdos_956_omega_four_thirds :
    ∀ N : ℕ, 80 ≤ N → (1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (h N : ℝ) :=
  Erdos956.FourLayer.h_omega_four_thirds_from_80

/-- Exact four-layer signed-grid polynomial lower bound at every scale $q \ge 1$:
$72 q^4 + 32 q^3 + 24 q^2 + 13 q + 3 \le h(48 q^3 + 16 q^2 + 12 q + 4)$. -/
theorem erdos_956_four_layer_polynomial :
    ∀ q : ℕ, 1 ≤ q →
      72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3 ≤
        h (48 * q ^ 3 + 16 * q ^ 2 + 12 * q + 4) :=
  Erdos956.FourLayer.h_fourLayer_lower_bound

/-- Sharp eventual $\frac{2}{5} N^{4/3}$ lower bound from the four-layer signed grid:
for all $N \ge N_{162} = 204{,}525{,}328$, $\frac{2}{5} N^{4/3} < h(N)$. -/
theorem erdos_956_two_fifths_from_204525328 :
    ∀ N : ℕ, 204525328 ≤ N → (2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (h N : ℝ) := by
  intro N hN
  have hgrid : Erdos956.FourLayer.fourLayerSize 162 ≤ N := by
    change 48 * 162 ^ 3 + 16 * 162 ^ 2 + 12 * 162 + 4 ≤ N
    omega
  exact Erdos956.FourLayer.h_eventual_two_fifths N hgrid

/-- Sharp eventual $\frac{2}{5} N^{4/3}$ lower bound from the four-layer signed grid:
for all sufficiently large $N$, $\frac{2}{5} N^{4/3} < h(N)$. -/
theorem erdos_956_eventual_two_fifths :
    ∀ᶠ N : ℕ in atTop, (2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (h N : ℝ) :=
  Filter.eventually_atTop.mpr ⟨204525328, erdos_956_two_fifths_from_204525328⟩

end Erdos956.Palomar

namespace Erdos956

open Filter

/-- Literal Formal Conjectures statement of Erdős Problem 956,
with `answer(True)` elaborated as `True`. -/
theorem erdos_956 : True ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (Erdos956.Extremal.h n : ℝ) :=
  Erdos956.Palomar.erdos_956

end Erdos956
