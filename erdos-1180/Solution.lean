module

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
-/

public import PigeonholeAndAsymptoticOptimality1180

@[expose] public section

open Filter

namespace Erdos1180

theorem erdos_1180 :
    True ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s :=
  ⟨fun _ ↦ Erdos1180.erdos_1180_multiset, fun _ ↦ trivial⟩

theorem erdos_1180.variants.glibichuk :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 2 ∧ Represents ε p a s :=
  Erdos1180.erdos_1180_glibichuk

theorem erdos_1180.variants.shparlinski :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 3 ∧ Represents ε p a s :=
  Erdos1180.erdos_1180_shparlinski

theorem erdos_1180.variants.lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → K * ε⁻¹ ≤ (C ε : ℝ) :=
  Erdos1180.erdos_1180_lower_bound

theorem erdos_1180.variants.lower_bound_large_primes :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∃ a : ZMod p,
        ∀ s : Multiset ℕ, Represents ε p a s → K * ε⁻¹ ≤ s.card :=
  Erdos1180.erdos_1180_lower_bound_large_primes

theorem not_erdos_1180_variants_optimal :
    ¬ Erdos1180OptimalConjecture :=
  Erdos1180.not_erdos1180OptimalConjecture

namespace Palomar

def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

def AsymptoticBoundSet (ε : ℝ) : Set ℕ :=
  {C | ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

noncomputable def CAsymptotic (ε : ℝ) : ℕ :=
  sInf (AsymptoticBoundSet ε)

def Erdos1180OptimalConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (C ε : ℝ) ≤ ε⁻¹ ^ (1 + δ)

theorem erdos_1180 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s :=
  Erdos1180.erdos_1180_multiset

theorem erdos_1180_variants_glibichuk :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 2 ∧ Represents ε p a s :=
  Erdos1180.erdos_1180_glibichuk

theorem erdos_1180_variants_shparlinski :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 3 ∧ Represents ε p a s :=
  Erdos1180.erdos_1180_shparlinski

theorem erdos_1180_variants_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → K * ε⁻¹ ≤ (C ε : ℝ) :=
  Erdos1180.erdos_1180_lower_bound

theorem erdos_1180_variants_lower_bound_large_primes :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∃ a : ZMod p,
        ∀ s : Multiset ℕ, Represents ε p a s → K * ε⁻¹ ≤ s.card :=
  Erdos1180.erdos_1180_lower_bound_large_primes

theorem not_erdos_1180_variants_optimal :
    ¬ Erdos1180OptimalConjecture :=
  Erdos1180.not_erdos1180OptimalConjecture

theorem two_rpow_inv_le_four_mul_C {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ^ (ε⁻¹) ≤ 4 * (C ε : ℝ) :=
  Erdos1180.two_rpow_inv_le_four_mul_C hε

theorem inv_le_CAsymptotic {ε : ℝ} (hε : 0 < ε) :
    ε⁻¹ ≤ (CAsymptotic ε : ℝ) :=
  Erdos1180.inv_le_CAsymptotic hε

theorem natCeil_inv_le_CAsymptotic {ε : ℝ} (hε : 0 < ε) :
    ⌈ε⁻¹⌉₊ ≤ CAsymptotic ε :=
  Erdos1180.natCeil_inv_le_CAsymptotic hε

theorem CAsymptotic_le_thirty_two_mul_inv_sq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (CAsymptotic ε : ℝ) ≤ 32 * ε⁻¹ ^ 2 :=
  Erdos1180.CAsymptotic_le_thirty_two_mul_inv_sq hε0 hε1

theorem CAsymptotic_le_eight_mul_sq_of_one_lt_mul {ε : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 1 ≤ k) (hkε : 1 < (k : ℝ) * ε) :
    CAsymptotic ε ≤ 8 * k ^ 2 :=
  Erdos1180.CAsymptotic_le_eight_mul_sq_of_one_lt_mul hε hk hkε

theorem CAsymptotic_le_eight_mul_succ_of_two_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : 2 < (2 * (k : ℝ) + 1) * ε) :
    CAsymptotic ε ≤ 8 * k * (k + 1) :=
  Erdos1180.CAsymptotic_le_eight_mul_succ_of_two_lt_mul hk hkε

theorem CAsymptotic_le_eight_mul_of_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : (k : ℝ) < (2 * (k : ℝ) - 1) * ε) :
    CAsymptotic ε ≤ 8 * k :=
  Erdos1180.CAsymptotic_le_eight_mul_of_lt_mul hk hkε

theorem CAsymptotic_le_sixteen_of_two_thirds_lt {ε : ℝ} (hε : 2 / 3 < ε) :
    CAsymptotic ε ≤ 16 :=
  Erdos1180.CAsymptotic_le_sixteen_of_two_thirds_lt hε

theorem CAsymptotic_le_eight_mul_floor_inv_add_one_sq {ε : ℝ} (hε : 0 < ε) :
    CAsymptotic ε ≤ 8 * (⌊ε⁻¹⌋₊ + 1) ^ 2 :=
  Erdos1180.CAsymptotic_le_eight_mul_floor_inv_add_one_sq hε

theorem eventually_CAsymptotic_le_eight_add_mul_inv_sq {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (CAsymptotic ε : ℝ) ≤ (8 + η) * ε⁻¹ ^ 2 :=
  Erdos1180.eventually_CAsymptotic_le_eight_add_mul_inv_sq hη

theorem CAsymptotic_inv_nat_lt_C_inv_nat {n : ℕ} (hn : 15 ≤ n) :
    CAsymptotic ((n : ℝ)⁻¹) < C ((n : ℝ)⁻¹) :=
  Erdos1180.CAsymptotic_inv_nat_lt_C_inv_nat hn

end Palomar
end Erdos1180
