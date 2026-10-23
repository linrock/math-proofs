module

public import Layer1258

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
-/

public section

/-! ## The main proof -/

universe u_1

namespace Erdos58

open SimpleGraph

/-- Erdős #58: at most `k` distinct odd simple-cycle lengths imply chromatic
number at most `2 * k + 2`, with equality exactly when the graph contains a
copy of `K_(2 * k + 2)`. -/
theorem erdos_58 {V : Type u_1} (G : SimpleGraph V) (k : ℕ)
    (hG : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
      (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained G) := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    statement_apply (statement_of_finite_gyarfas finite_gyarfas) G k hG hk

end Erdos58
