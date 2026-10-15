module

/-
Copyright 2025 The Formal Conjectures Authors.
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
-/

public import Mathlib

@[expose] public section

open SimpleGraph Filter

namespace Erdos667

/-- A graph `G` on `n` vertices is *`(p, q)`-locally dense* if every set of `p` of its vertices
spans at least `q` edges of `G`; equivalently, every induced subgraph on `p` vertices has at
least `q` edges. -/
def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard

open Classical in
/-- `H p q n` is `H(n) = H(n; p, q)`: the largest `m` such that *every* `(p, q)`-locally dense
graph on `n` vertices must contain a complete graph on `m` vertices `Kₘ`. -/
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n

/-- The growth exponent `c(p, q) = liminf_{n → ∞} (log H(n)) / (log n)`. -/
noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop

namespace variants

/-- Monotonicity of `c(p, q)` in `q` on `[1, C(p - 1, 2) + 1]`
(`FormalConjectures` `Erdos667.erdos_667.variants.monotoneOn`). -/
theorem monotoneOn (p : ℕ) :
    MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) := by
  sorry

/-- Right-endpoint identity `c(p, C(p - 1, 2) + 1) = 1` for all `p ≥ 2`
(`FormalConjectures` `Erdos667.erdos_667.variants.endpoint`). -/
theorem endpoint (p : ℕ) (hp : 2 ≤ p) :
    c p (Nat.choose (p - 1) 2 + 1) = 1 := by
  sorry

/-- Universal Erdős–Szekeres Ramsey lower bound `1 / (p - 1) ≤ c(p, 1)` for all `p ≥ 2`,
resolving the lower bound of `FormalConjectures` `Erdos667.erdos_667.variants.ramsey_bounds`. -/
theorem ramsey_lower_bound (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ≤ c p 1 := by
  sorry

/-- Universal lower bound `1 / (p - 1) ≤ c(p, q)` for all `p ≥ 2` and `q ≥ 1`. -/
theorem c_ge_inv_pred {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    1 / ((p : ℝ) - 1) ≤ c p q := by
  sorry

end variants
end Erdos667
