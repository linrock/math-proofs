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

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace Erdos1122

/-!
# Binary-Carry / Even-Odd Doubling Decomposition and Dyadic-Shell Oscillation Bounds (Erdős Problem #1122)

This module establishes universal (`∀`) structural theorems connecting complete additivity,
binary-carry / even-odd doubling decompositions, `Nat.log 2 (q / u)` bit-length induction,
and dyadic-shell oscillation bounds (`HasBoundedDyadicShellOscillation f C`), and composes them
with `isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps`
from `ControlledDescentLogRatioSqueezeAndRigidity1122`.
-/

/-! ## Section 1: Binary-Step Identities and Even-Odd Doubling Decomposition -/

/-- **Binary-Step Doubling Identity**:
For any completely additive function `f : ℕ → ℝ` and `m ≥ 1`, `f (2 * m) = f 2 + f m`. -/
theorem completely_additive_two_mul {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {m : ℕ} (hm : 1 ≤ m) :
    f (2 * m) = f 2 + f m :=
  hmul 2 (by omega) m hm

/-- **Iterated Power-of-Two Doubling Identity**:
For any completely additive function `f : ℕ → ℝ`, `m ≥ 1`, and `s : ℕ`,
`f (2 ^ s * m) = (s : ℝ) * f 2 + f m`. -/
theorem completely_additive_two_pow_mul {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    f (2 ^ s * m) = (s : ℝ) * f 2 + f m := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h2s_pos : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by omega)
    have hprod_pos : 1 ≤ 2 ^ s * m := Nat.mul_pos h2s_pos hm
    have hrew : 2 ^ (s + 1) * m = 2 * (2 ^ s * m) := by
      rw [pow_succ']
      ring
    rw [hrew, completely_additive_two_mul hmul hprod_pos, ih]
    push_cast
    ring

/-- **Even-Difference Scale Invariance (`f 2` Cancellation Identity)**:
For any completely additive function `f : ℕ → ℝ` and `a, b ≥ 1`,
`f (2 * b) - f (2 * a) = f b - f a`. -/
theorem completely_additive_two_mul_sub_two_mul {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (2 * b) - f (2 * a) = f b - f a := by
  rw [completely_additive_two_mul hmul hb, completely_additive_two_mul hmul ha]
  ring

/-- **Consecutive Even Step Identity**:
For any completely additive function `f : ℕ → ℝ` and `m ≥ 1`,
`f (2 * m + 2) - f (2 * m) = f (m + 1) - f m`. -/
theorem completely_additive_even_succ_even_diff {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {m : ℕ} (hm : 1 ≤ m) :
    f (2 * m + 2) - f (2 * m) = f (m + 1) - f m := by
  have hrew : 2 * m + 2 = 2 * (m + 1) := by ring
  rw [hrew]
  exact completely_additive_two_mul_sub_two_mul hmul hm (by omega)

/-- **Two-Step Even-Odd Doubling Decomposition**:
For any completely additive function `f : ℕ → ℝ` and `m ≥ 1`, the sum of the two consecutive
steps across `2 * m + 1` equals the single step `f (m + 1) - f m`:
`(f (2 * m + 1) - f (2 * m)) + (f (2 * m + 2) - f (2 * m + 1)) = f (m + 1) - f m`. -/
theorem completely_additive_odd_step_sum_eq {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {m : ℕ} (hm : 1 ≤ m) :
    (f (2 * m + 1) - f (2 * m)) + (f (2 * m + 2) - f (2 * m + 1)) = f (m + 1) - f m := by
  have h := completely_additive_even_succ_even_diff hmul hm
  linarith

/-- **Two-Sided Binary-Carry Step Bounds Between `m` and `2 * m` Under `HasBoundedDownwardJumps`**:
For any completely additive function `f : ℕ → ℝ` satisfying `HasBoundedDownwardJumps f D` and
any `m ≥ 1`:
1. `-D ≤ f (2 * m + 1) - f (2 * m)` and `f (2 * m + 1) - f (2 * m) ≤ f (m + 1) - f m + D`
2. `-D ≤ f (2 * m) - f (2 * m - 1)` and (for `2 ≤ m`) `f (2 * m) - f (2 * m - 1) ≤ f m - f (m - 1) + D`. -/
theorem completely_additive_dyadic_step_bounds_of_hasBoundedDownwardJumps {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {D : ℝ} (hD : HasBoundedDownwardJumps f D) {m : ℕ} (hm : 1 ≤ m) :
    -D ≤ f (2 * m + 1) - f (2 * m) ∧
    f (2 * m + 1) - f (2 * m) ≤ (f (m + 1) - f m) + D ∧
    -D ≤ f (2 * m) - f (2 * m - 1) := by
  have h1 : f (2 * m) - f (2 * m + 1) ≤ D := hD (2 * m) (by omega)
  have h2 : f (2 * m + 1) - f (2 * m + 2) ≤ D := hD (2 * m + 1) (by omega)
  have h3 : f (2 * m - 1) - f (2 * m) ≤ D := by
    have hstep := hD (2 * m - 1) (by omega)
    have hsucc : 2 * m - 1 + 1 = 2 * m := by omega
    rwa [hsucc] at hstep
  have hsum := completely_additive_odd_step_sum_eq hmul hm
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## Section 2: Dyadic-Shell Complementary Decomposition and Downward-Drift Oscillation Bounds -/

/-- **Dyadic-Shell Complementary Identity**:
For any completely additive function `f : ℕ → ℝ`, `u ≥ 1`, and any `q : ℕ`,
`(f q - f u) + (f (2 * u) - f q) = f 2`. -/
theorem completely_additive_dyadic_shell_complement_eq {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {u : ℕ} (hu : 1 ≤ u) (q : ℕ) :
    (f q - f u) + (f (2 * u) - f q) = f 2 := by
  have h2u := completely_additive_two_mul hmul hu
  linarith

/-- **Window-Localized Dyadic-Shell Oscillation Bound Under `HasPrefixBoundedDownwardJumps`**:
For any completely additive function `f : ℕ → ℝ` with `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`),
if `1 ≤ u`, `u ≤ q ≤ 2 * u`, and `2 * u ≤ X + 1`, then
`|f q - f u| ≤ |f 2| + D * ((Finset.Ico u (2 * u) ∩ descentFinset f X).card : ℝ)`. -/
theorem completely_additive_dyadic_shell_window_oscillation_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {u q : ℕ} (hu : 1 ≤ u) (huq : u ≤ q) (hq2u : q ≤ 2 * u) (hX : 2 * u ≤ X + 1) :
    |f q - f u| ≤ |f 2| + D * ((Finset.Ico u (2 * u) ∩ descentFinset f X).card : ℝ) := by
  have hq_ge1 : 1 ≤ q := le_trans hu huq
  have hq_le_X : q ≤ X + 1 := le_trans hq2u hX
  have hlow := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hu huq hq_le_X
  have hhigh := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hq_ge1 hq2u hX
  have hsplit := card_Ico_inter_add_card_Ico_inter huq hq2u (descentFinset f X)
  have hsplit_real :
      ((Finset.Ico u q ∩ descentFinset f X).card : ℝ) +
      ((Finset.Ico q (2 * u) ∩ descentFinset f X).card : ℝ) =
      ((Finset.Ico u (2 * u) ∩ descentFinset f X).card : ℝ) := by
    exact_mod_cast hsplit
  have hcomp := completely_additive_dyadic_shell_complement_eq hmul hu q
  have h1_nonneg : 0 ≤ D * ((Finset.Ico u q ∩ descentFinset f X).card : ℝ) := by positivity
  have h2_nonneg : 0 ≤ D * ((Finset.Ico q (2 * u) ∩ descentFinset f X).card : ℝ) := by positivity
  have hf2_le : f 2 ≤ |f 2| := le_abs_self (f 2)
  have hf2_nonneg : 0 ≤ |f 2| := abs_nonneg (f 2)
  have hsum_D :
      D * ((Finset.Ico u q ∩ descentFinset f X).card : ℝ) +
      D * ((Finset.Ico q (2 * u) ∩ descentFinset f X).card : ℝ) =
      D * ((Finset.Ico u (2 * u) ∩ descentFinset f X).card : ℝ) := by
    rw [← mul_add, hsplit_real]
  rw [abs_le]
  constructor <;> linarith

/-- **Discharging `HasBoundedDyadicShellOscillation` from Bounded Sub-Shell Downward Drift**:
For any completely additive function `f : ℕ → ℝ`, if the downward drift across subintervals of
every dyadic shell `[u, 2 * u]` is bounded by `M ≥ 0` (`f u - f q ≤ M` and `f q - f (2 * u) ≤ M`),
then `HasBoundedDyadicShellOscillation f (|f 2| + M)` holds. -/
theorem completely_additive_hasBoundedDyadicShellOscillation_of_subshell_downward_drift {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {M : ℝ}
    (hdrift : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
      f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    HasBoundedDyadicShellOscillation f (|f 2| + M) := by
  intro u hu q huq hq2u
  obtain ⟨hlow, hhigh⟩ := hdrift u hu q huq hq2u
  have hcomp := completely_additive_dyadic_shell_complement_eq hmul hu q
  have hf2_le : f 2 ≤ |f 2| := le_abs_self (f 2)
  have hf2_nonneg : 0 ≤ |f 2| := abs_nonneg (f 2)
  rw [abs_le]
  constructor <;> linarith

/-- **Discharging `HasBoundedDyadicShellOscillation` from Bounded Dyadic-Shell Descent Count**:
If `f : ℕ → ℝ` is completely additive, satisfies `HasBoundedDownwardJumps f D` (`0 ≤ D`), and
every dyadic shell `[u, 2 * u)` contains at most `K` descents, then
`HasBoundedDyadicShellOscillation f (|f 2| + D * (K : ℝ))` holds. -/
theorem completely_additive_hasBoundedDyadicShellOscillation_of_shell_descent_card_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : HasBoundedDownwardJumps f D)
    {K : ℕ} (hcard : ∀ u : ℕ, 1 ≤ u → (Finset.Ico u (2 * u) ∩ descentFinset f (2 * u)).card ≤ K) :
    HasBoundedDyadicShellOscillation f (|f 2| + D * (K : ℝ)) := by
  intro u hu q huq hq2u
  have hpref : HasPrefixBoundedDownwardJumps f (2 * u) D :=
    hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps hD (2 * u)
  have hwin := completely_additive_dyadic_shell_window_oscillation_bound
    hmul hD0 hpref hu huq hq2u (by omega)
  have hK_le : D * ((Finset.Ico u (2 * u) ∩ descentFinset f (2 * u)).card : ℝ) ≤ D * (K : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard u hu) hD0
  linarith

/-! ## Section 3: Binary Bit-Length (`Nat.log 2 (q / u)`) Induction and Binary-Carry Halving Bounds -/

/-- **Single Binary-Halving Step Defect Bound**:
For any completely additive function `f : ℕ → ℝ`, if the odd binary-carry step satisfies
`∀ m ≥ 1, |f (2 * m + 1) - f 2 - f m| ≤ B` (with `0 ≤ B`), then for every `q ≥ 2`,
`|f q - f 2 - f (q / 2)| ≤ B`. -/
theorem completely_additive_binary_halving_step_defect_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    {q : ℕ} (hq : 2 ≤ q) :
    |f q - f 2 - f (q / 2)| ≤ B := by
  set m : ℕ := q / 2
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hdiv := Nat.div_add_mod q 2
  have hmod : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · have hq_eq : q = 2 * m := by dsimp [m]; omega
    rw [hq_eq, completely_additive_two_mul hmul hm]
    ring_nf
    simpa using hB0
  · have hq_eq : q = 2 * m + 1 := by dsimp [m]; omega
    rw [hq_eq]
    exact hcarry m hm

/-- **Iterated Binary-Halving Bit-Length Induction Bound**:
For any completely additive function `f : ℕ → ℝ`, if `∀ m ≥ 1, |f (2 * m + 1) - f 2 - f m| ≤ B`
(`0 ≤ B`), then by induction on the binary bit-shift `s : ℕ`, for every `q` with `1 ≤ q / 2 ^ s`,
`|f q - (s : ℝ) * f 2 - f (q / 2 ^ s)| ≤ (s : ℝ) * B`. -/
theorem completely_additive_iterated_binary_halving_defect_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    (s : ℕ) {q : ℕ} (hq : 1 ≤ q / 2 ^ s) :
    |f q - (s : ℝ) * f 2 - f (q / 2 ^ s)| ≤ (s : ℝ) * B := by
  induction s generalizing q with
  | zero => simp
  | succ s ih =>
    have hpow_eq : q / 2 ^ (s + 1) = (q / 2) / 2 ^ s := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have hq_div : 1 ≤ (q / 2) / 2 ^ s := by rwa [← hpow_eq]
    have hq_half : 1 ≤ q / 2 := le_trans hq_div (Nat.div_le_self (q / 2) (2 ^ s))
    have hq_ge2 : 2 ≤ q := by omega
    have hstep := completely_additive_binary_halving_step_defect_le hmul hB0 hcarry hq_ge2
    have ih_step := ih hq_div
    rw [hpow_eq]
    rw [abs_le] at hstep ih_step ⊢
    push_cast
    constructor <;> linarith

/-- **Iterated Simultaneous Binary-Halving Difference Bound**:
For any completely additive function `f : ℕ → ℝ` with `∀ m ≥ 1, |f (2 * m + 1) - f 2 - f m| ≤ B`
(`0 ≤ B`), for every `s : ℕ` and `u, q` with `1 ≤ u / 2 ^ s` and `1 ≤ q / 2 ^ s`,
`|(f q - f u) - (f (q / 2 ^ s) - f (u / 2 ^ s))| ≤ 2 * (s : ℝ) * B`. -/
theorem completely_additive_iterated_simultaneous_binary_halving_diff_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    (s : ℕ) {u q : ℕ} (hu : 1 ≤ u / 2 ^ s) (hq : 1 ≤ q / 2 ^ s) :
    |(f q - f u) - (f (q / 2 ^ s) - f (u / 2 ^ s))| ≤ 2 * (s : ℝ) * B := by
  have hq_it := completely_additive_iterated_binary_halving_defect_le hmul hB0 hcarry s hq
  have hu_it := completely_additive_iterated_binary_halving_defect_le hmul hB0 hcarry s hu
  rw [abs_le] at hq_it hu_it ⊢
  constructor <;> linarith

/-- **Multi-Shell Oscillation Bound by Induction on Binary Bit-Length `s`**:
If `f : ℕ → ℝ` is completely additive and satisfies `HasBoundedDyadicShellOscillation f C`,
then by induction on `s : ℕ`, for all `u ≥ 1` and `q` in the `s`-th dyadic shell
`2 ^ s * u ≤ q ≤ 2 ^ (s + 1) * u`:
`|f q - f u - (s : ℝ) * f 2| ≤ C` and `|f q - f u| ≤ C + (s : ℝ) * |f 2|`. -/
theorem completely_additive_pow_two_shell_oscillation_of_hasBoundedDyadicShellOscillation
    {f : ℕ → ℝ} (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {C : ℝ} (hC : HasBoundedDyadicShellOscillation f C)
    (s : ℕ) {u q : ℕ} (hu : 1 ≤ u) (hlow : 2 ^ s * u ≤ q) (hhigh : q ≤ 2 ^ (s + 1) * u) :
    |f q - f u - (s : ℝ) * f 2| ≤ C ∧ |f q - f u| ≤ C + (s : ℝ) * |f 2| := by
  set u_s : ℕ := 2 ^ s * u
  have h2s_pos : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by omega)
  have hus_ge1 : 1 ≤ u_s := Nat.mul_pos h2s_pos hu
  have hhigh' : q ≤ 2 * u_s := by
    dsimp [u_s]
    have hrew : 2 ^ (s + 1) * u = 2 * (2 ^ s * u) := by
      rw [pow_succ']
      ring
    linarith
  have hshell := hC u_s hus_ge1 q hlow hhigh'
  have hfus : f u_s = (s : ℝ) * f 2 + f u := completely_additive_two_pow_mul hmul hu s
  have hshift : f q - f u_s = f q - f u - (s : ℝ) * f 2 := by linarith
  rw [hshift] at hshell
  have hmul_le : (s : ℝ) * f 2 ≤ (s : ℝ) * |f 2| :=
    mul_le_mul_of_nonneg_left (le_abs_self (f 2)) (Nat.cast_nonneg s)
  have hmul_ge : -((s : ℝ) * |f 2|) ≤ (s : ℝ) * f 2 := by
    have h := mul_le_mul_of_nonneg_left (neg_abs_le (f 2)) (Nat.cast_nonneg s)
    linarith
  refine ⟨hshell, ?_⟩
  rw [abs_le] at hshell ⊢
  constructor <;> linarith

/-- **Dyadic-Shell Bit-Length (`Nat.log 2 (q / u)`) Decomposition and `HasBoundedDyadicShellOscillation`**:
For any completely additive function `f : ℕ → ℝ`, on any dyadic shell `u ≤ q ≤ 2 * u` (`u ≥ 1`),
the binary bit-length `Nat.log 2 (q / u)` is either `0` (when `u ≤ q < 2 * u`) or `1`
(when `q = 2 * u`, where `f (2 * u) - f u = f 2`). Consequently, if `|f q - f u| ≤ B` on the
half-open bit-length-`0` shell `u ≤ q < 2 * u`, then `HasBoundedDyadicShellOscillation f (max B |f 2|)`
holds across the closed dyadic shell `u ≤ q ≤ 2 * u`. -/
theorem completely_additive_hasBoundedDyadicShellOscillation_of_bitLength_zero_shell_bound
    {f : ℕ → ℝ} (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q < 2 * u → |f q - f u| ≤ B) :
    HasBoundedDyadicShellOscillation f (max B |f 2|) := by
  intro u hu q huq hq2u
  rcases lt_or_eq_of_le hq2u with hlt | rfl
  · exact le_trans (hB u hu q huq hlt) (le_max_left B |f 2|)
  · rw [completely_additive_two_mul hmul hu]
    ring_nf
    exact le_max_right B |f 2|

/-! ## Section 4: Composition with `isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation` -/

/-- **Scaled-Logarithm Rigidity from Sub-Shell Downward Drift Bounds**:
Composes `completely_additive_hasBoundedDyadicShellOscillation_of_subshell_downward_drift` with
`isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps`
to deduce `IsScaledLogOnPos f` and `f m = (f 2 / Real.log 2) * Real.log m`. -/
theorem isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_subshell_downward_drift
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D M : ℝ} (hD : HasBoundedDownwardJumps f D)
    (hdrift : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
      f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y :=
    fun x hx y hy => coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hx hy
  have hC : HasBoundedDyadicShellOscillation f (|f 2| + M) :=
    completely_additive_hasBoundedDyadicShellOscillation_of_subshell_downward_drift hmul hdrift
  have hiff :=
    (isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD).mpr ⟨|f 2| + M, hC⟩
  exact ⟨(dyadic_shell_oscillation_eq_scaled_log_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    hf ho hD hC).1, hiff⟩

/-- **Scaled-Logarithm Rigidity from Bounded Dyadic-Shell Descent Counts**:
Composes `completely_additive_hasBoundedDyadicShellOscillation_of_shell_descent_card_le` with
`isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps`
to deduce `IsScaledLogOnPos f`. -/
theorem isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_shell_descent_card_le
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {K : ℕ} (hcard : ∀ u : ℕ, 1 ≤ u → (Finset.Ico u (2 * u) ∩ descentFinset f (2 * u)).card ≤ K) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y :=
    fun x hx y hy => coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hx hy
  set Dpos : ℝ := max D 0
  have hDpos0 : 0 ≤ Dpos := le_max_right D 0
  have hDpos : HasBoundedDownwardJumps f Dpos :=
    hasBoundedDownwardJumps_mono hD (le_max_left D 0)
  have hC : HasBoundedDyadicShellOscillation f (|f 2| + Dpos * (K : ℝ)) :=
    completely_additive_hasBoundedDyadicShellOscillation_of_shell_descent_card_le
      hmul hDpos0 hDpos hcard
  have hiff :=
    (isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD).mpr ⟨|f 2| + Dpos * (K : ℝ), hC⟩
  exact ⟨(dyadic_shell_oscillation_eq_scaled_log_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    hf ho hD hC).1, hiff⟩

/-- **Scaled-Logarithm Rigidity from Bit-Length-Zero Half-Open Shell Bounds**:
Composes `completely_additive_hasBoundedDyadicShellOscillation_of_bitLength_zero_shell_bound` with
`isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps`
to deduce `IsScaledLogOnPos f`. -/
theorem isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_bitLength_zero_shell_bound
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D B : ℝ} (hD : HasBoundedDownwardJumps f D)
    (hB : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q < 2 * u → |f q - f u| ≤ B) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y :=
    fun x hx y hy => coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hx hy
  have hC : HasBoundedDyadicShellOscillation f (max B |f 2|) :=
    completely_additive_hasBoundedDyadicShellOscillation_of_bitLength_zero_shell_bound hmul hB
  have hiff :=
    (isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD).mpr ⟨max B |f 2|, hC⟩
  exact ⟨(dyadic_shell_oscillation_eq_scaled_log_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    hf ho hD hC).1, hiff⟩

/-- **Top-Down Conditional Reduction of `Erdos1122Conjecture` via Sub-Shell Downward Drift**:
Reduces `Erdos1122Conjecture` to bounded downward jumps and bounded downward drift across
dyadic sub-shells `[u, q]` and `[q, 2 * u]`. -/
theorem erdos_1122_of_boundedDownwardJumps_and_subshell_downward_drift
    (hjump : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ D : ℝ, HasBoundedDownwardJumps f D)
    (hdrift : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ M : ℝ, ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
        f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    Erdos1122Conjecture := by
  intro f hf ho
  obtain ⟨D, hD⟩ := hjump f hf ho
  obtain ⟨M, hM⟩ := hdrift f hf ho
  exact (isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_subshell_downward_drift
    hf ho hD hM).2

end Erdos1122

end
