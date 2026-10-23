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

@[expose] public section

universe u_1

namespace SimpleGraph

/-- Cycle lengths follow the exact Formal Conjectures definition used by the
Solution package. -/
def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m | ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

end SimpleGraph

namespace Erdos58

open SimpleGraph

/-- Erdős #58: if a simple graph has at most `k` distinct odd simple-cycle
lengths, then its chromatic number is at most `2 * k + 2`, and equality holds
exactly when it contains a copy of `K_(2 * k + 2)`. -/
theorem erdos_58 {V : Type u_1} (G : SimpleGraph V) (k : ℕ)
    (hG : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
      (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
        (completeGraph (Fin (2 * k + 2))).IsContained G) := by
  sorry

end Erdos58
