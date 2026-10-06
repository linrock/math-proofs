module

/-
Copyright 2025-2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adaptation notice: Linmiao Xu adapted the Erdős 1105 statements and the
attributed `IsRainbow` / `antiRamseyNum` definitions from
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1105.lean`
and `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`)
for this standalone Lean 4.35.0-rc2 benchmark in 2026. This file imports only
Mathlib.
-/

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Erdős Problem 1105: anti-Ramsey numbers for cycles and paths

The anti-Ramsey number $\mathrm{AR}(n, H)$ is the maximum number of colors in a
surjective edge-coloring of $K_n$ that contains no rainbow copy of $H$.

- Part (i) (`erdos_1105_cycles` / `erdos_1105_parts_i`): For every fixed cycle
  order $k \ge 3$,
  $$\mathrm{AR}(n, C_k) = \left(\frac{k - 2}{2} + \frac{1}{k - 1}\right) n + O(1).$$
- Part (ii) (`erdos_1105_paths` / `erdos_1105_parts_ii`): For every path order
  $k \ge 5$ and host order $n \ge k$, with $\ell = \lfloor (k - 1) / 2 \rfloor$
  and $\varepsilon = 1$ if $k$ is odd and $\varepsilon = 2$ if $k$ is even,
  $$\mathrm{AR}(n, P_k) = \max\left\{\binom{k - 2}{2} + 1,\;
    \binom{\ell - 1}{2} + (\ell - 1)(n - \ell + 1) + \varepsilon\right\}.$$
- Explicit cycle bounds (`antiRamseyNum_triangle`, `cycle_fullBlock_lower`,
  `cycle_real_lower`, `cycle_linear_upper`): For all $n \ge 3$,
  $\mathrm{AR}(n, C_3) = n - 1$, and for all $n \ge k \ge 3$,
  $$\left\lfloor \frac{n}{k - 1} \right\rfloor \left(\binom{k - 1}{2} + 1\right) - 1
    \le \mathrm{AR}(n, C_k)
    \le \left(\frac{k - 2}{2} + \frac{1}{k - 1}\right) n - 1.$$

The eight intentional `sorry` placeholders below are matched by proved
declarations in `Solution.lean`; `Solution.lean` does not import this module.
-/

namespace Erdos1105.Palomar

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
      =O[atTop] (fun _ => (1 : ℝ))) := by
  sorry

/-- Part (ii) of Erdős Problem 1105: for every $n \ge k \ge 5$,
$\mathrm{AR}(n, P_k) = \max\left(\binom{k-2}{2}+1, \binom{\ell-1}{2}+(\ell-1)(n-\ell+1)+\varepsilon\right)$. -/
theorem erdos_1105_paths :
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε) := by
  sorry

/-- Elaborated Formal Conjectures `True ↔` form of Part (i). -/
theorem erdos_1105_parts_i : True ↔
    ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  sorry

/-- Elaborated Formal Conjectures `True ↔` form of Part (ii). -/
theorem erdos_1105_parts_ii : True ↔
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε) := by
  sorry

/-- Erdős–Simonovits–Sós (1975) exact anti-Ramsey formula for the triangle $C_3$:
for every $n \ge 3$, $\mathrm{AR}(n, C_3) = n - 1$. -/
theorem antiRamseyNum_triangle (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNum (cycleGraph 3) n = n - 1 := by
  sorry

/-- Erdős–Simonovits–Sós (1975) ordered $(k - 1)$-clique block lower bound for
cycles: for every $k \ge 3$ and $n \ge k$,
$\lfloor n / (k - 1) \rfloor \left(\binom{k - 1}{2} + 1\right) - 1 \le \mathrm{AR}(n, C_k)$. -/
theorem cycle_fullBlock_lower (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    n / (k - 1) * ((k - 1).choose 2 + 1) - 1 ≤
      antiRamseyNum (cycleGraph k) n := by
  sorry

/-- Explicit real linear lower bound for $\mathrm{AR}(n, C_k)$ derived from the
ordered $(k - 1)$-clique block construction for all $k \ge 3$ and $n \ge k$. -/
theorem cycle_real_lower (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) -
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * ((k - 1 : ℕ) : ℝ) - 1 ≤
      (antiRamseyNum (cycleGraph k) n : ℝ) := by
  sorry

/-- Explicit linear upper bound for $\mathrm{AR}(n, C_k)$ across all $k \ge 3$
and $n \ge k$ (Montellano-Ballesteros and Neumann-Lara 2005; Choi 2011):
$\mathrm{AR}(n, C_k) \le \left(\frac{k - 2}{2} + \frac{1}{k - 1}\right) n - 1$. -/
theorem cycle_linear_upper (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n - 1 := by
  sorry

end Erdos1105.Palomar
