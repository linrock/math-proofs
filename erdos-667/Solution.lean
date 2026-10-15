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

public import LocalDensityEndpointAndRamseyBounds667

@[expose] public section

open SimpleGraph Filter

namespace Erdos667

def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard

open Classical in
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n

noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop

namespace variants

theorem monotoneOn (p : ℕ) :
    MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) :=
  Erdos667.Core.variantsMonotoneOn p

theorem endpoint (p : ℕ) (hp : 2 ≤ p) :
    c p (Nat.choose (p - 1) 2 + 1) = 1 :=
  Erdos667.Core.variantsEndpoint p hp

theorem ramsey_lower_bound (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ≤ c p 1 :=
  Erdos667.Core.ramseyLowerBound p hp

theorem c_ge_inv_pred {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    1 / ((p : ℝ) - 1) ≤ c p q :=
  Erdos667.Core.cGeInvPred hp hq

end variants
end Erdos667
