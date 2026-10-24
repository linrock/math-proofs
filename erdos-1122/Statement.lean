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

public import Erdos1122Unified435
public import WirsingWindowAveragingAndLittleODiffRigidity1122
public import ControlledDescentTelescopingAndBoundedJumpRigidity1122
public import ControlledDescentLogRatioSqueezeAndRigidity1122
public import Blueprint1122

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos1122.Challenge

open Erdos1122

/-- Named alias for the canonical Erdős Problem 1122 statement (`Erdos1122Conjecture`). -/
abbrev statement_erdos_1122_open_conjecture : Prop :=
  Erdos1122Conjecture

/-- Canonical Erdős (1946) empty-descent baseline statement (`Erdos1122EmptyDescentProp`). -/
abbrev statement_erdos_1122_empty_descent : Prop :=
  Erdos1122EmptyDescentProp

/-- Canonical Erdős (1946) vanishing consecutive-difference baseline statement (`Erdos1122LittleODiffProp`). -/
abbrev statement_erdos_1122_littleO_diff : Prop :=
  Erdos1122LittleODiffProp

theorem statement_erdos1122_conjecture_implies_empty_descent_prop :
    Erdos1122Conjecture → Erdos1122EmptyDescentProp :=
  Erdos1122.erdos1122_conjecture_implies_empty_descent_prop

theorem statement_coprime_cross_step_diff_eq {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop1 : a.Coprime (b + 1)) (hcop2 : (a + 1).Coprime b) :
    f ((a + 1) * b) - f (a * (b + 1)) = (f (a + 1) - f a) - (f (b + 1) - f b) :=
  Erdos1122.coprime_cross_step_diff_eq hf ha hb hcop1 hcop2

theorem statement_finitely_supported_erdos1122_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {Q : ℕ} (hQ : 1 ≤ Q) (hsupp : ∀ m > 0, Q.Coprime m → f m = 0)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ))) :
    descentSet f = ∅ ∧ (∀ n : ℕ, 1 ≤ n → f n = 0) ∧ IsScaledLogOnPos f :=
  Erdos1122.finitely_supported_erdos1122_unconditional hf hQ hsupp ho

theorem statement_coprime_additive_mul_of_descentSet_empty {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b :=
  Erdos1122.coprime_additive_mul_of_descentSet_empty hf hempty ha hb

theorem statement_empty_descent_eq_scaled_log_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.empty_descent_eq_scaled_log_unconditional hf hempty

theorem statement_erdos1122_empty_descent_prop_holds :
    Erdos1122EmptyDescentProp ∧
    ∀ f : ℕ → ℝ, IsCoprimeAdditive f → descentSet f = ∅ → IsScaledLogOnPos f :=
  Erdos1122.erdos1122_empty_descent_prop_holds

theorem statement_coprime_additive_mul_of_isLittleO_diff {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b :=
  Erdos1122.coprime_additive_mul_of_isLittleO_diff hf ho ha hb

theorem statement_littleO_diff_eq_scaled_log_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.littleO_diff_eq_scaled_log_unconditional hf ho

theorem statement_erdos1122_littleO_diff_prop_holds :
    Erdos1122LittleODiffProp ∧
    ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) →
      IsScaledLogOnPos f :=
  Erdos1122.erdos1122_littleO_diff_prop_holds

theorem statement_wirsing_zero_density_eventually_exists_good_sandwich_shift {f : ℕ → ℝ}
    (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀,
      ∃ k ∈ Finset.Icc 1 K,
        |f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) :=
  Erdos1122.wirsing_zero_density_eventually_exists_good_sandwich_shift hf ho ha hb

theorem statement_controlled_descent_telescoping_additive_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ)
    (hX_in : sandwichWLow a b (K + 1) ≤ X + 1)
    (hX_out : a * sandwichWHigh a b K ≤ X + 1) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤
      f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) +
      2 * D * (descentCount f X : ℝ) :=
  Erdos1122.controlled_descent_telescoping_additive_defect_bound hf hD0 hD ha hb K hX_in hX_out

theorem statement_coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b :=
  Erdos1122.coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps hf ho hD ha hb

theorem statement_controlled_descent_log_ratio_diff_le_descentCount {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b)
    {m n : ℕ} (k : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hX : n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1) :
    |f m / Real.log (m : ℝ) - f n / Real.log (n : ℝ)| ≤
      (|f n| + D * (descentCount f X : ℝ)) / ((k : ℝ) * Real.log (m : ℝ)) :=
  Erdos1122.controlled_descent_log_ratio_diff_le_descentCount hD0 hD hpow k hm hn hk hX

theorem statement_sublogarithmic_descentCount_eq_scaled_log_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f) {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    (ho_lin : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    (ho_log : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => Real.log (X : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.sublogarithmic_descentCount_eq_scaled_log_of_hasBoundedDownwardJumps hf hD ho_lin ho_log

theorem statement_trajectory_sublinear_descent_eq_scaled_log_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    (htraj : ∀ b : ℕ, 2 ≤ b →
      (fun k : ℕ => (trajDescentCount f (2 * ((b ^ k) / 2 + 1)) 2 (b ^ k) (Nat.log 2 (b ^ k)) : ℝ))
        =o[Filter.atTop] (fun k : ℕ => (k : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.trajectory_sublinear_descent_eq_scaled_log_of_hasBoundedDownwardJumps hf ho hD htraj

theorem statement_exists_zero_descent_shifted_div_trajectory_of_mul_descentCount_lt (f : ℕ → ℝ) (X : ℕ)
    {a m s U : ℕ} (ha : 1 ≤ a) (hm : a ^ s ≤ m) (hU : s * descentCount f X < U) :
    ∃ u ∈ Finset.Icc 1 U, trajDescentCount f X a (u * m) s = 0 :=
  Erdos1122.exists_zero_descent_shifted_div_trajectory_of_mul_descentCount_lt f X ha hm hU

theorem statement_isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D) :
    IsScaledLogOnPos f ↔ ∃ C : ℝ, HasBoundedDyadicShellOscillation f C :=
  Erdos1122.isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps hf ho hD

theorem statement_erdos1122_conjecture_of_boundedDownwardJumps_and_dyadicShellOscillation
    (hjump : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ D : ℝ, HasBoundedDownwardJumps f D)
    (hshell : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ C : ℝ, HasBoundedDyadicShellOscillation f C) :
    Erdos1122Conjecture :=
  Erdos1122.erdos1122_conjecture_of_boundedDownwardJumps_and_dyadicShellOscillation hjump hshell

theorem statement_completely_additive_dyadic_step_bounds_of_hasBoundedDownwardJumps {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {D : ℝ} (hD : HasBoundedDownwardJumps f D) {m : ℕ} (hm : 1 ≤ m) :
    -D ≤ f (2 * m + 1) - f (2 * m) ∧
    f (2 * m + 1) - f (2 * m) ≤ (f (m + 1) - f m) + D ∧
    -D ≤ f (2 * m) - f (2 * m - 1) :=
  Erdos1122.completely_additive_dyadic_step_bounds_of_hasBoundedDownwardJumps hmul hD hm

theorem statement_completely_additive_dyadic_shell_complement_eq {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {u : ℕ} (hu : 1 ≤ u) (q : ℕ) :
    (f q - f u) + (f (2 * u) - f q) = f 2 :=
  Erdos1122.completely_additive_dyadic_shell_complement_eq hmul hu q

theorem statement_completely_additive_dyadic_shell_window_oscillation_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {u q : ℕ} (hu : 1 ≤ u) (huq : u ≤ q) (hq2u : q ≤ 2 * u) (hX : 2 * u ≤ X + 1) :
    |f q - f u| ≤ |f 2| + D * ((Finset.Ico u (2 * u) ∩ descentFinset f X).card : ℝ) :=
  Erdos1122.completely_additive_dyadic_shell_window_oscillation_bound hmul hD0 hD hu huq hq2u hX

theorem statement_completely_additive_iterated_binary_halving_defect_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    (s : ℕ) {q : ℕ} (hq : 1 ≤ q / 2 ^ s) :
    |f q - (s : ℝ) * f 2 - f (q / 2 ^ s)| ≤ (s : ℝ) * B :=
  Erdos1122.completely_additive_iterated_binary_halving_defect_le hmul hB0 hcarry s hq

theorem statement_completely_additive_iterated_simultaneous_binary_halving_diff_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    (s : ℕ) {u q : ℕ} (hu : 1 ≤ u / 2 ^ s) (hq : 1 ≤ q / 2 ^ s) :
    |(f q - f u) - (f (q / 2 ^ s) - f (u / 2 ^ s))| ≤ 2 * (s : ℝ) * B :=
  Erdos1122.completely_additive_iterated_simultaneous_binary_halving_diff_le hmul hB0 hcarry s hu hq

theorem statement_completely_additive_pow_two_shell_oscillation_of_hasBoundedDyadicShellOscillation
    {f : ℕ → ℝ} (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {C : ℝ} (hC : HasBoundedDyadicShellOscillation f C)
    (s : ℕ) {u q : ℕ} (hu : 1 ≤ u) (hlow : 2 ^ s * u ≤ q) (hhigh : q ≤ 2 ^ (s + 1) * u) :
    |f q - f u - (s : ℝ) * f 2| ≤ C ∧ |f q - f u| ≤ C + (s : ℝ) * |f 2| :=
  Erdos1122.completely_additive_pow_two_shell_oscillation_of_hasBoundedDyadicShellOscillation hmul hC s hu hlow hhigh

theorem statement_isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_subshell_downward_drift
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D M : ℝ} (hD : HasBoundedDownwardJumps f D)
    (hdrift : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
      f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_subshell_downward_drift hf ho hD hdrift

theorem statement_isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_shell_descent_card_le
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {K : ℕ} (hcard : ∀ u : ℕ, 1 ≤ u → (Finset.Ico u (2 * u) ∩ descentFinset f (2 * u)).card ≤ K) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_shell_descent_card_le hf ho hD hcard

theorem statement_isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_bitLength_zero_shell_bound
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D B : ℝ} (hD : HasBoundedDownwardJumps f D)
    (hB : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q < 2 * u → |f q - f u| ≤ B) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  Erdos1122.isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_bitLength_zero_shell_bound hf ho hD hB

theorem statement_erdos_1122_of_boundedDownwardJumps_and_subshell_downward_drift
    (hjump : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ D : ℝ, HasBoundedDownwardJumps f D)
    (hdrift : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ M : ℝ, ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
        f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    Erdos1122Conjecture :=
  Erdos1122.erdos_1122_of_boundedDownwardJumps_and_subshell_downward_drift hjump hdrift

end Erdos1122.Challenge

end
