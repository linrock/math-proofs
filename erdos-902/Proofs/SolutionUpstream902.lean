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
public import Erdos902Unified435
public import SzekeresParityRefinementAndTightenedBinomialBounds902
public import SecondOrderBinomialDecayAndTransitiveTripleCounting902
public import QuinticBinomialDecayAndKendallBabingtonSmithBounds902
public import Blueprint902
public import Alignment902

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 200000
set_option exponentiation.threshold 4096

noncomputable section
open scoped Classical BigOperators

namespace Erdos902

theorem hasParadoxicalTournament_zero_iff_and_upstream_f_zero (N : ℕ) :
    (HasParadoxicalTournament 0 N ↔ 1 ≤ N) ∧ f 0 = 1 := by
  have h := hasParadoxicalTournament_zero_iff_and_f_zero N
  exact ⟨h.1, by rw [← legacyF_eq_f]; exact h.2⟩


theorem paley7Digraph_dom2_and_upstream_f_two (N : ℕ) :
    IsParadoxicalTournament 2 paley7Digraph ∧
      (HasParadoxicalTournament 2 N ↔ 7 ≤ N) ∧ f 2 = 7 := by
  have h := paley7Digraph_dom2_and_f_two N
  exact ⟨isParadoxicalTournament_paley7Digraph, h.1,
    by rw [← legacyF_eq_f]; exact h.2⟩

theorem hasParadoxicalTournament_three_iff_and_upstream_f_three (N : ℕ) :
    IsParadoxicalTournament 3 paley19Digraph ∧
      (HasParadoxicalTournament 3 N ↔ 19 ≤ N) ∧
      14 ≤ f 3 ∧ f 3 ≤ 19 ∧ f 3 = 19 := by
  have h := hasParadoxicalTournament_three_iff_and_f_three N
  refine ⟨isParadoxicalTournament_paley19Digraph, h.1,
    by rw [← legacyF_eq_f]; omega, by rw [← legacyF_eq_f]; omega,
    by rw [← legacyF_eq_f]; exact h.2⟩




theorem erdos_szekeres_upstream_f_sandwich (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 1) - 1 ≤ f n ∧
      (n + 2) * 2 ^ (n - 1) - 1 ≤ f n ∧
      f n ≤ n + 2 * n * (n + 1) * 2 ^ n ∧
      f n ≤ 5 * n ^ 2 * 2 ^ n := by
  have h := erdos_szekeres_f_sandwich n hn
  rw [legacyF_eq_f] at h
  exact h





end Erdos902
end
