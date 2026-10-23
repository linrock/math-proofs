module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

Adaptation notice: Linmiao Xu adapted the Erdős 1105 statements and proved
all public endpoints in Lean 4.35.0-rc2 in 2026. This module does not import
or reference `Challenge`.
-/

public import PathKernelAndUniversalExact

@[expose] public section

/-!
# Erdős Problem 1105: complete proved endpoints for cycles and paths

This module proves the eight independent targets in `Erdos1105.Results`
together with the literal `Erdos1105.erdos_1105.parts.i` and
`Erdos1105.erdos_1105.parts.ii` declarations over `SimpleGraph.antiRamseyNum`.
-/

namespace Erdos1105.Results

open SimpleGraph Asymptotics Filter

/-- A homomorphism `f : H →g G` is rainbow for an edge labeling `c` of `G` if it maps distinct
edges of `H` to edges of `G` with distinct labels. -/
def IsRainbow {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V} (f : H →g G)
    (c : G.EdgeLabeling K) : Prop :=
  Function.Injective (c.pullback f)

/-- The anti-Ramsey number $\mathrm{AR}(n, H)$: the maximum number of colors in an edge coloring of
$K_n$ (that is, a labeling of the edges of $K_n$ using every color) that contains no rainbow copy
of $H$, i.e. no injective homomorphism (copy) of $H$ whose edges all receive different colors. -/
noncomputable def antiRamseyNum {α : Type*} [Fintype α] (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {k | ∃ c : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective c ∧
    ∀ f : H.Copy ⊤, ¬IsRainbow f.toHom c}

/-- Part (i) of Erdős Problem 1105: for every fixed $k \ge 3$,
$\mathrm{AR}(n, C_k) = \left(\frac{k-2}{2} + \frac{1}{k-1}\right) n + O(1)$. -/
theorem erdos_1105_cycles :
    ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) :=
  ErdosProblems.AntiRamseyCycleOriginalHighNewStructure.cycle_asymptotic_all

/-- Part (ii) of Erdős Problem 1105: for every $n \ge k \ge 5$,
$\mathrm{AR}(n, P_k) = \max\left(\binom{k-2}{2}+1, \binom{\ell-1}{2}+(\ell-1)(n-\ell+1)+\varepsilon\right)$. -/
theorem erdos_1105_paths :
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε) :=
  ErdosProblems.PathUpperReduction.PathEightNineBase1105.erdos_1105_parts_ii_exact

/-- Formal Conjectures statement of Part (i), restated with `SimpleGraph.antiRamseyNum`. -/
theorem erdos_1105_parts_i :
    ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) :=
  erdos_1105_cycles

/-- Formal Conjectures statement of Part (ii), restated with `SimpleGraph.antiRamseyNum`. -/
theorem erdos_1105_parts_ii :
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε) :=
  erdos_1105_paths

/-- Erdős–Simonovits–Sós (1975) exact anti-Ramsey formula for the triangle $C_3$:
for every $n \ge 3$, $\mathrm{AR}(n, C_3) = n - 1$. -/
theorem antiRamseyNum_triangle (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNum (cycleGraph 3) n = n - 1 :=
  ErdosProblems.AntiRamseyTriangle.antiRamseyNum_cycleGraph_three n hn

/-- Erdős–Simonovits–Sós (1975) ordered $(k - 1)$-clique block lower bound for
cycles: for every $k \ge 3$ and $n \ge k$,
$\lfloor n / (k - 1) \rfloor \left(\binom{k - 1}{2} + 1\right) - 1 \le \mathrm{AR}(n, C_k)$. -/
theorem cycle_fullBlock_lower (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    n / (k - 1) * ((k - 1).choose 2 + 1) - 1 ≤
      antiRamseyNum (cycleGraph k) n :=
  ErdosProblems.AntiRamseyCycleCounted.cycle_fullBlock_antiRamseyNum_lower k n hk hn

/-- Explicit real linear lower bound for $\mathrm{AR}(n, C_k)$ derived from the
ordered $(k - 1)$-clique block construction for all $k \ge 3$ and $n \ge k$. -/
theorem cycle_real_lower (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) -
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * ((k - 1 : ℕ) : ℝ) - 1 ≤
      (antiRamseyNum (cycleGraph k) n : ℝ) :=
  ErdosProblems.AntiRamseyCycleCounted.cycle_fullBlock_real_lower k n hk hn

/-- Explicit linear upper bound for $\mathrm{AR}(n, C_k)$ across all $k \ge 3$
and $n \ge k$ (Montellano-Ballesteros and Neumann-Lara 2005; Choi 2011):
$\mathrm{AR}(n, C_k) \le \left(\frac{k - 2}{2} + \frac{1}{k - 1}\right) n - 1$. -/
theorem cycle_linear_upper (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n - 1 :=
  ErdosProblems.AntiRamseyCycleOriginalHighNewStructure.cycle_linear_upper k n hk hn

end Erdos1105.Results

namespace Erdos1105

open SimpleGraph Asymptotics Filter

/-- Literal Formal Conjectures statement of Erdős Problem 1105, Part (i),
over `SimpleGraph.antiRamseyNum`. -/
theorem erdos_1105.parts.i :
    ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) :=
  Erdos1105.Results.erdos_1105_parts_i

/-- Literal Formal Conjectures statement of Erdős Problem 1105, Part (ii),
over `SimpleGraph.antiRamseyNum`. -/
theorem erdos_1105.parts.ii :
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε) :=
  Erdos1105.Results.erdos_1105_parts_ii

end Erdos1105
