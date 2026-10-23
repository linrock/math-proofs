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
-/

public import Mathlib
public import Layer1358

@[expose] public section

universe u_1

namespace Erdos58.Challenge

open SimpleGraph

/-- The exact statement of Erdős #58 as a proposition with no admitted theorem:
at most `k` distinct odd simple-cycle lengths imply chromatic number at most
`2 * k + 2`, and equality is equivalent to containment of `K_(2 * k + 2)`. -/
def statement : Prop :=
  ∀ {V : Type u_1} (G : SimpleGraph V) (k : ℕ),
    G.oddCycleLengths.Finite →
    G.oddCycleLengths.ncard ≤ k →
      G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
        (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
          (completeGraph (Fin (2 * k + 2))).IsContained G)

end Erdos58.Challenge
