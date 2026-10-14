module

/-
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

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

/-!
# Near-Square Divisor Intervals and Hyperbolic Gap Identities for Erdős Problem #886

This module proves universal (`∀`) structural results for
`Erdos886.Erdos886Divisors n ε C`:

1. **Monotonicity & Anti-Monotonicity:**
   - `erdos886Divisors_mono_C` and `card_erdos886Divisors_mono_C`
   - `erdos886Divisors_antitone_eps` and `card_erdos886Divisors_antitone_eps`

2. **Regime $\varepsilon \ge 1/2$ (Oblong Characterization & Perfect-Square Exclusion):**
   - `rpow_half_sub_eps_le_one`
   - `eq_of_mem_erdos886Divisors_of_half_le` and `card_erdos886Divisors_le_one_of_half_le`
   - `card_erdos886Divisors_le_floor_add_one_of_half_le`
   - `erdos886Divisors_sq_eq_empty_of_half_le`: `Erdos886Divisors (m^2) ε 1 = ∅` for all `m : ℕ` and `ε ≥ 1/2`
   - `eq_pred_mul_self_of_mem_erdos886Divisors_of_half_le`: every `d ∈ Erdos886Divisors n ε 1`
     with `ε ≥ 1/2` forces `n = (d - 1) * d` (an oblong number)
   - `mem_erdos886Divisors_mul_succ_half` and `erdos886Divisors_mul_succ_half`: for every `m ≥ 1`,
     `Erdos886Divisors (m * (m + 1)) (1/2) 1 = {m + 1}`

3. **Complementary Divisor Hyperbolic Identity & Unconditional Resolution for $\varepsilon \ge 1/4$:**
   - `complementary_divisor_hyperbolic_identity`:
     $(d : \mathbb{R})((d : \mathbb{R}) + n/d - 2 n^{1/2}) = (d - n^{1/2})^2$
   - `four_mul_eq_sum_sq_sub_diff_sq`:
     $4n = (d + n/d)^2 - (d - n/d)^2$
   - `complementary_sum_strict_mono_of_ge_sqrt`:
     For divisors $n^{1/2} \le d_1 < d_2$, the integer sum $d \mapsto d + n/d$ is strictly increasing
   - `card_erdos886Divisors_le_one_of_quarter_le` and `erdos_886_of_quarter_le`:
     Unconditional proof that `(Erdos886Divisors n ε 1).card ≤ 1` for all $n \in \mathbb{N}$
     and all $\varepsilon \ge 1/4$
   - `eventually_card_erdos886Divisors_le_one_of_quarter_lt`:
     For every $\varepsilon > 1/4$ and every $C \in \mathbb{R}$, eventually `(Erdos886Divisors n ε C).card ≤ 1`

4. **Complete Proofs of Both Erdős-Rosenfeld [ErRo97] Variants in `FormalConjectures/ErdosProblems/886.lean`:**
   - `rosenfeld_closed_interval_bound_all_n` and `erdos_886_rosenfeld_bound`:
     For all $C > 0$ and all $n \in \mathbb{N}$, the number of divisors of $n$ in
     $[n^{1/2}, n^{1/2} + C n^{1/4}]$ is at most $1 + C^2$
   - `four_le_card_erdos886Divisors_rosenfeldN` and `erdos_886_rosenfeld_infinite`:
     Infinitely many $n$ have at least $4$ divisors in $(n^{1/2}, n^{1/2} + 16 n^{1/4})$
-/

namespace Erdos886

/-! ## Section 0: Canonical Definition and Foundational Power-Exponent Identities -/

/--
The set of divisors of $n$ in the open interval $(n^{1/2}, n^{1/2} + C n^{1/2-\varepsilon})$.
Matches `Erdos886.Erdos886Divisors` in `FormalConjectures/ErdosProblems/886.lean`.
-/
noncomputable def Erdos886Divisors (n : ℕ) (ε : ℝ) (C : ℝ) : Finset ℕ :=
  (Nat.divisors n).filter (fun d =>
    (n : ℝ) ^ (1 / 2 : ℝ) < d ∧ (d : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 2 - ε))

/-- Membership characterization for `Erdos886Divisors n ε C`. -/
theorem mem_erdos886Divisors_iff (n d : ℕ) (ε C : ℝ) :
    d ∈ Erdos886Divisors n ε C ↔
      d ∈ Nat.divisors n ∧
      (n : ℝ) ^ (1 / 2 : ℝ) < d ∧
      (d : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 2 - ε) := by
  simp [Erdos886Divisors]

/-- At `n = 0`, `Erdos886Divisors 0 ε C` is empty for all `ε, C`. -/
theorem erdos886Divisors_zero (ε C : ℝ) : Erdos886Divisors 0 ε C = ∅ := by
  simp [Erdos886Divisors]

/-- At `n = 1`, `Erdos886Divisors 1 ε C` is empty for all `ε, C` since the unique divisor `1`
does not satisfy `1 < 1`. -/
theorem erdos886Divisors_one (ε C : ℝ) : Erdos886Divisors 1 ε C = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro d hd
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨hd1, hlt, _⟩
  rw [Nat.divisors_one, Finset.mem_singleton] at hd1
  subst hd1
  norm_num at hlt

/-- Whenever `C ≤ 0`, the open interval $(n^{1/2}, n^{1/2} + C n^{1/2 - \varepsilon})$ is empty. -/
theorem erdos886Divisors_eq_empty_of_nonpos (n : ℕ) (ε C : ℝ) (hC : C ≤ 0) :
    Erdos886Divisors n ε C = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro d hd
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨_, h1, h2⟩
  have hpow : 0 ≤ (n : ℝ) ^ (1 / 2 - ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmul : C * (n : ℝ) ^ (1 / 2 - ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hpow
  linarith

/-- Square identity `((n : ℝ) ^ (1/2)) ^ 2 = n` for all `n : ℕ`. -/
theorem rpow_half_sq (n : ℕ) : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := sq _
    _ = (n : ℝ) ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := (Real.rpow_add' hn (by norm_num)).symm
    _ = (n : ℝ) ^ (1 : ℝ) := by norm_num
    _ = (n : ℝ) := Real.rpow_one (n : ℝ)

/-- Square identity `((n : ℝ) ^ (1/4)) ^ 2 = (n : ℝ) ^ (1/2)` for all `n : ℕ`. -/
theorem rpow_quarter_sq (n : ℕ) : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := sq _
    _ = (n : ℝ) ^ ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := (Real.rpow_add' hn (by norm_num)).symm
    _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num

/-- Exact evaluation `((m^2 : ℕ) : ℝ) ^ (1/2) = m` for all `m : ℕ`. -/
theorem rpow_half_nat_sq (m : ℕ) : (((m ^ 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) = (m : ℝ) := by
  have hsq : (((m ^ 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by
    calc
      (((m ^ 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = ((m ^ 2 : ℕ) : ℝ) := rpow_half_sq (m ^ 2)
      _ = (m : ℝ) ^ 2 := by push_cast; ring
  have h1 : 0 ≤ (((m ^ 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-! ## Section 1: Monotonicity in `C` and Anti-Monotonicity in `ε` -/

/-- `Erdos886Divisors n ε C` is monotone in the interval multiplier `C`. -/
theorem erdos886Divisors_mono_C (n : ℕ) (ε C₁ C₂ : ℝ) (hC : C₁ ≤ C₂) :
    Erdos886Divisors n ε C₁ ⊆ Erdos886Divisors n ε C₂ := by
  intro d hd
  rw [mem_erdos886Divisors_iff] at hd ⊢
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  refine ⟨hdiv, hlow, ?_⟩
  have hpow : 0 ≤ (n : ℝ) ^ (1 / 2 - ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmul : C₁ * (n : ℝ) ^ (1 / 2 - ε) ≤ C₂ * (n : ℝ) ^ (1 / 2 - ε) :=
    mul_le_mul_of_nonneg_right hC hpow
  linarith

/-- Cardinality monotonicity of `Erdos886Divisors n ε C` in `C`. -/
theorem card_erdos886Divisors_mono_C (n : ℕ) (ε C₁ C₂ : ℝ) (hC : C₁ ≤ C₂) :
    (Erdos886Divisors n ε C₁).card ≤ (Erdos886Divisors n ε C₂).card :=
  Finset.card_le_card (erdos886Divisors_mono_C n ε C₁ C₂ hC)

/-- `Erdos886Divisors n ε C` is antitone in `ε` for `C ≥ 0`. -/
theorem erdos886Divisors_antitone_eps (n : ℕ) (ε₁ ε₂ C : ℝ) (hε : ε₁ ≤ ε₂) (hC : 0 ≤ C) :
    Erdos886Divisors n ε₂ C ⊆ Erdos886Divisors n ε₁ C := by
  intro d hd
  rw [mem_erdos886Divisors_iff] at hd ⊢
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hdiv).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow : (n : ℝ) ^ (1 / 2 - ε₂) ≤ (n : ℝ) ^ (1 / 2 - ε₁) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hmul : C * (n : ℝ) ^ (1 / 2 - ε₂) ≤ C * (n : ℝ) ^ (1 / 2 - ε₁) :=
    mul_le_mul_of_nonneg_left hpow hC
  exact ⟨hdiv, hlow, by linarith⟩

/-- Cardinality anti-monotonicity of `Erdos886Divisors n ε C` in `ε` for `C ≥ 0`. -/
theorem card_erdos886Divisors_antitone_eps (n : ℕ) (ε₁ ε₂ C : ℝ) (hε : ε₁ ≤ ε₂) (hC : 0 ≤ C) :
    (Erdos886Divisors n ε₂ C).card ≤ (Erdos886Divisors n ε₁ C).card :=
  Finset.card_le_card (erdos886Divisors_antitone_eps n ε₁ ε₂ C hε hC)

/-! ## Section 2: General Cardinality Principle for Strictly Monotone Integer Statistics -/

/-- If `f : ℕ → ℕ` is strictly monotone on a finite set `s : Finset ℕ` and its values on `s`
have pairwise difference at most `B ≥ 0`, then `(s.card : ℝ) ≤ 1 + B`. -/
theorem card_nat_finset_le_of_strictMonoOn_image_diff
    (s : Finset ℕ) (f : ℕ → ℕ)
    (hmono : ∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b)
    (B : ℝ) (hB : 0 ≤ B)
    (hdiff : ∀ a ∈ s, ∀ b ∈ s, (f b : ℝ) - (f a : ℝ) ≤ B) :
    (s.card : ℝ) ≤ 1 + B := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp; linarith
  · have hinj : Set.InjOn f s := by
      intro a ha b hb hab
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact False.elim (ne_of_lt (hmono a ha b hb hlt) hab)
      · rfl
      · exact False.elim (ne_of_gt (hmono b hb a ha hgt) hab)
    have hcard_eq : (s.image f).card = s.card := Finset.card_image_of_injOn hinj
    let amin := s.min' hne
    let amax := s.max' hne
    have hamin : amin ∈ s := Finset.min'_mem s hne
    have hamax : amax ∈ s := Finset.max'_mem s hne
    have hsub : s.image f ⊆ Finset.Icc (f amin) (f amax) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rw [Finset.mem_Icc]
      constructor
      · rcases lt_or_eq_of_le (Finset.min'_le s x hx) with hlt | heq
        · exact le_of_lt (hmono amin hamin x hx hlt)
        · exact le_of_eq (congrArg f heq)
      · rcases lt_or_eq_of_le (Finset.le_max' s x hx) with hlt | heq
        · exact le_of_lt (hmono x hx amax hamax hlt)
        · exact le_of_eq (congrArg f heq)
    have hle_icc : s.card ≤ (Finset.Icc (f amin) (f amax)).card := by
      rw [← hcard_eq]
      exact Finset.card_le_card hsub
    rw [Nat.card_Icc] at hle_icc
    have hamin_le_amax : f amin ≤ f amax := by
      rcases lt_or_eq_of_le (Finset.min'_le s amax hamax) with hlt | heq
      · exact le_of_lt (hmono amin hamin amax hamax hlt)
      · exact le_of_eq (congrArg f heq)
    have hcast : (s.card : ℝ) ≤ (f amax : ℝ) + 1 - (f amin : ℝ) := by
      have h1 : (s.card : ℝ) ≤ ((f amax + 1 - f amin : ℕ) : ℝ) := by exact_mod_cast hle_icc
      have h2 : ((f amax + 1 - f amin : ℕ) : ℝ) = (f amax : ℝ) + 1 - (f amin : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      linarith
    have hdiff_bound := hdiff amin hamin amax hamax
    linarith

/-! ## Section 3: Regime $\varepsilon \ge 1/2$, Perfect Squares, and Oblong Numbers -/

/-- For `n ≥ 1` and `ε ≥ 1/2`, `(n : ℝ) ^ (1/2 - ε) ≤ 1`. -/
theorem rpow_half_sub_eps_le_one (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 1 / 2 ≤ ε) :
    (n : ℝ) ^ (1 / 2 - ε) ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = 1 := Real.rpow_zero (n : ℝ)

/-- For `ε ≥ 1/2` and `C = 1`, any two elements of `Erdos886Divisors n ε 1` are equal. -/
theorem eq_of_mem_erdos886Divisors_of_half_le (n d₁ d₂ : ℕ) (ε : ℝ) (hε : 1 / 2 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1) (hd₂ : d₂ ∈ Erdos886Divisors n ε 1) :
    d₁ = d₂ := by
  rw [mem_erdos886Divisors_iff] at hd₁ hd₂
  rcases hd₁ with ⟨hdiv₁, hlow₁, hhigh₁⟩
  rcases hd₂ with ⟨_, hlow₂, hhigh₂⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.mem_divisors.mp hdiv₁).2
  have hpow : (n : ℝ) ^ (1 / 2 - ε) ≤ 1 := rpow_half_sub_eps_le_one n hn1 ε hε
  have hlt1 : (d₁ : ℝ) < (d₂ : ℝ) + 1 := by linarith
  have hlt2 : (d₂ : ℝ) < (d₁ : ℝ) + 1 := by linarith
  have hnat1 : d₁ < d₂ + 1 := by exact_mod_cast hlt1
  have hnat2 : d₂ < d₁ + 1 := by exact_mod_cast hlt2
  omega

/-- For all `n : ℕ` and `ε ≥ 1/2`, `(Erdos886Divisors n ε 1).card ≤ 1`. -/
theorem card_erdos886Divisors_le_one_of_half_le (n : ℕ) (ε : ℝ) (hε : 1 / 2 ≤ ε) :
    (Erdos886Divisors n ε 1).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  exact eq_of_mem_erdos886Divisors_of_half_le n a b ε hε ha hb

/-- For all `n : ℕ`, `ε ≥ 1/2`, and `C ≥ 0`, `(Erdos886Divisors n ε C).card ≤ ⌊C⌋₊ + 1`. -/
theorem card_erdos886Divisors_le_floor_add_one_of_half_le
    (n : ℕ) (ε C : ℝ) (hε : 1 / 2 ≤ ε) (hC : 0 ≤ C) :
    (Erdos886Divisors n ε C).card ≤ ⌊C⌋₊ + 1 := by
  have hreal : ((Erdos886Divisors n ε C).card : ℝ) ≤ 1 + C := by
    apply card_nat_finset_le_of_strictMonoOn_image_diff (Erdos886Divisors n ε C) id
    · intro a _ b _ hlt; exact hlt
    · exact hC
    · intro a ha b hb
      rw [mem_erdos886Divisors_iff] at ha hb
      rcases ha with ⟨hdiv_a, hlow_a, _⟩
      rcases hb with ⟨_, _, hhigh_b⟩
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.mem_divisors.mp hdiv_a).2
      have hpow : (n : ℝ) ^ (1 / 2 - ε) ≤ 1 := rpow_half_sub_eps_le_one n hn1 ε hε
      have hmul : C * (n : ℝ) ^ (1 / 2 - ε) ≤ C := by nlinarith
      dsimp
      linarith
  rcases (Erdos886Divisors n ε C).eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  · have hcard_pos : 1 ≤ (Erdos886Divisors n ε C).card := Finset.card_pos.mpr hne
    have hsub_le : ((Erdos886Divisors n ε C).card - 1 : ℕ) ≤ ⌊C⌋₊ := by
      apply Nat.le_floor
      have hcast : (((Erdos886Divisors n ε C).card - 1 : ℕ) : ℝ) =
          ((Erdos886Divisors n ε C).card : ℝ) - 1 := by
        rw [Nat.cast_sub hcard_pos, Nat.cast_one]
      linarith
    omega

/-- Perfect-square exclusion: for every `m : ℕ` and `ε ≥ 1/2`, `Erdos886Divisors (m^2) ε 1 = ∅`. -/
theorem erdos886Divisors_sq_eq_empty_of_half_le (m : ℕ) (ε : ℝ) (hε : 1 / 2 ≤ ε) :
    Erdos886Divisors (m ^ 2) ε 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro d hd
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  have hm0 : m ^ 2 ≠ 0 := (Nat.mem_divisors.mp hdiv).2
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr hm0
  have hpow : ((m ^ 2 : ℕ) : ℝ) ^ (1 / 2 - ε) ≤ 1 := rpow_half_sub_eps_le_one (m ^ 2) hm1 ε hε
  rw [rpow_half_nat_sq m] at hlow hhigh
  have hlt1 : (m : ℝ) < (d : ℝ) := hlow
  have hlt2 : (d : ℝ) < (m : ℝ) + 1 := by linarith
  have hnat1 : m < d := by exact_mod_cast hlt1
  have hnat2 : d < m + 1 := by exact_mod_cast hlt2
  omega

/-- Oblong-number necessity: if `d ∈ Erdos886Divisors n ε 1` for `ε ≥ 1/2`, then `n = (d - 1) * d`. -/
theorem eq_pred_mul_self_of_mem_erdos886Divisors_of_half_le
    (n d : ℕ) (ε : ℝ) (hε : 1 / 2 ≤ ε) (hd : d ∈ Erdos886Divisors n ε 1) :
    (d - 1) * d = n := by
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hdiv).1
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hdiv).2
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hdiv
  have hpow : (n : ℝ) ^ (1 / 2 - ε) ≤ 1 := rpow_half_sub_eps_le_one n hn1 ε hε
  set e := n / d
  have hde : e * d = n := Nat.div_mul_cancel hdvd
  have hdeR : (e : ℝ) * (d : ℝ) = (n : ℝ) := by exact_mod_cast hde
  have hs_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have hlt_sq : (n : ℝ) < (d : ℝ) ^ 2 := by nlinarith
  have hd_sub : (d : ℝ) - 1 < (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
  have hgt_sq : ((d : ℝ) - 1) ^ 2 < (n : ℝ) := by nlinarith
  have he_lt : (e : ℝ) < (d : ℝ) := by nlinarith
  have he_lt_nat : e < d := by exact_mod_cast he_lt
  have he_gt : (d : ℝ) - 2 < (e : ℝ) := by nlinarith
  have he_eq : e = d - 1 := by
    by_contra hne
    have hle : e + 2 ≤ d := by omega
    have hleR : ((e + 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hle
    push_cast at hleR
    linarith
  rw [← he_eq, hde]

/-- Oblong-number sufficiency: for every `m ≥ 1`, `m + 1 ∈ Erdos886Divisors (m * (m + 1)) (1/2) 1`. -/
theorem mem_erdos886Divisors_mul_succ_half (m : ℕ) (hm : 1 ≤ m) :
    m + 1 ∈ Erdos886Divisors (m * (m + 1)) (1 / 2) 1 := by
  rw [mem_erdos886Divisors_iff]
  have hm0 : m * (m + 1) ≠ 0 := by positivity
  have hdvd : m + 1 ∣ m * (m + 1) := dvd_mul_left (m + 1) m
  have hdiv : m + 1 ∈ Nat.divisors (m * (m + 1)) := Nat.mem_divisors.mpr ⟨hdvd, hm0⟩
  set n := m * (m + 1)
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have hs_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hn_cast : (n : ℝ) = (m : ℝ) * ((m : ℝ) + 1) := by simp [n]
  have hm_pos : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlow : (n : ℝ) ^ (1 / 2 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hhigh : ((m + 1 : ℕ) : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + 1 * (n : ℝ) ^ (1 / 2 - (1 / 2 : ℝ)) := by
    have hrpow0 : (n : ℝ) ^ (1 / 2 - (1 / 2 : ℝ)) = 1 := by norm_num
    rw [hrpow0, mul_one]
    push_cast
    have : (m : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
    linarith
  exact ⟨hdiv, hlow, hhigh⟩

/-- Exact set equality `Erdos886Divisors (m * (m + 1)) (1/2) 1 = {m + 1}` for all `m ≥ 1`. -/
theorem erdos886Divisors_mul_succ_half (m : ℕ) (hm : 1 ≤ m) :
    Erdos886Divisors (m * (m + 1)) (1 / 2) 1 = {m + 1} := by
  ext d
  simp only [Finset.mem_singleton]
  constructor
  · intro hd
    exact eq_of_mem_erdos886Divisors_of_half_le (m * (m + 1)) d (m + 1) (1 / 2) le_rfl
      hd (mem_erdos886Divisors_mul_succ_half m hm)
  · rintro rfl
    exact mem_erdos886Divisors_mul_succ_half m hm

/-! ## Section 4: Complementary Divisor Hyperbolic Identity & Unconditional Resolution for $\varepsilon \ge 1/4$ -/

/-- Division-free hyperbolic sum identity for any divisor `d ∈ n.divisors`:
`(d : ℝ) * (d + n / d - 2 * n^(1/2)) = (d - n^(1/2))^2`. -/
theorem complementary_divisor_hyperbolic_identity (n d : ℕ) (hd : d ∈ Nat.divisors n) :
    (d : ℝ) * ((d : ℝ) + (n / d : ℕ) - 2 * (n : ℝ) ^ (1 / 2 : ℝ)) =
      ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hde : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hdeR : (d : ℝ) * (n / d : ℕ) = (n : ℝ) := by exact_mod_cast hde
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  calc
    (d : ℝ) * ((d : ℝ) + (n / d : ℕ) - 2 * (n : ℝ) ^ (1 / 2 : ℝ))
      = (d : ℝ) ^ 2 + (d : ℝ) * (n / d : ℕ) - 2 * (d : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
    _ = (d : ℝ) ^ 2 + (n : ℝ) - 2 * (d : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hdeR]
    _ = (d : ℝ) ^ 2 + ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 - 2 * (d : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hs_sq]
    _ = ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by ring

/-- Difference-of-squares factorization identity `4n = (d + n/d)^2 - (d - n/d)^2` for `d ∈ n.divisors`. -/
theorem four_mul_eq_sum_sq_sub_diff_sq (n d : ℕ) (hd : d ∈ Nat.divisors n) :
    4 * (n : ℝ) = ((d : ℝ) + (n / d : ℕ)) ^ 2 - ((d : ℝ) - (n / d : ℕ)) ^ 2 := by
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hde : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hdeR : (d : ℝ) * (n / d : ℕ) = (n : ℝ) := by exact_mod_cast hde
  calc
    4 * (n : ℝ) = 4 * ((d : ℝ) * (n / d : ℕ)) := by rw [hdeR]
    _ = ((d : ℝ) + (n / d : ℕ)) ^ 2 - ((d : ℝ) - (n / d : ℕ)) ^ 2 := by ring

/-- Every `d ∈ Erdos886Divisors n ε C` has complementary sum strictly above `2 * n^(1/2)`. -/
theorem complementary_sum_gt_two_sqrt_of_mem_erdos886Divisors
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    2 * (n : ℝ) ^ (1 / 2 : ℝ) < (d : ℝ) + (n / d : ℕ) := by
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨hdiv, hlow, _⟩
  have hid := complementary_divisor_hyperbolic_identity n d hdiv
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hdiv
  have hsq_pos : 0 < ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
    have : 0 < (d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
    positivity
  nlinarith

/-- Whenever `1/4 ≤ ε`, every `d ∈ Erdos886Divisors n ε 1` has complementary sum
strictly below `2 * n^(1/2) + 1`. -/
theorem complementary_sum_lt_two_sqrt_add_one_of_quarter_le
    (n d : ℕ) (ε : ℝ) (hε : 1 / 4 ≤ ε) (hd : d ∈ Erdos886Divisors n ε 1) :
    (d : ℝ) + (n / d : ℕ) < 2 * (n : ℝ) ^ (1 / 2 : ℝ) + 1 := by
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  have hid := complementary_divisor_hyperbolic_identity n d hdiv
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hdiv).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow : (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hdiff_pos : 0 < (d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
  have hdiff_lt : (d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
  have hsq_lt : ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 < ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    nlinarith
  rw [rpow_quarter_sq n] at hsq_lt
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hdiv
  nlinarith

/-- Strict monotonicity of the integer complementary-divisor sum `d ↦ d + n / d` on
divisors `n^(1/2) ≤ d₁ < d₂`. -/
theorem complementary_sum_strict_mono_of_ge_sqrt
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    d₁ + n / d₁ < d₂ + n / d₂ := by
  have hdvd₁ : d₁ ∣ n := (Nat.mem_divisors.mp hd₁).1
  have hdvd₂ : d₂ ∣ n := (Nat.mem_divisors.mp hd₂).1
  set e₁ := n / d₁
  set e₂ := n / d₂
  have hde₁ : (d₁ : ℝ) * (e₁ : ℝ) = (n : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hdvd₁
  have hde₂ : (d₂ : ℝ) * (e₂ : ℝ) = (n : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hdvd₂
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have hs_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hltR : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have he₂_lt_d₁ : (e₂ : ℝ) < (d₁ : ℝ) := by nlinarith
  have hpoly : (d₁ : ℝ) * (((d₂ : ℝ) + (e₂ : ℝ)) - ((d₁ : ℝ) + (e₁ : ℝ))) =
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₁ : ℝ) - (e₂ : ℝ)) := by
    calc
      (d₁ : ℝ) * (((d₂ : ℝ) + (e₂ : ℝ)) - ((d₁ : ℝ) + (e₁ : ℝ)))
        = (d₁ : ℝ) * (d₂ : ℝ) + (d₁ : ℝ) * (e₂ : ℝ) - (d₁ : ℝ) ^ 2 - (d₁ : ℝ) * (e₁ : ℝ) := by ring
      _ = (d₁ : ℝ) * (d₂ : ℝ) + (d₁ : ℝ) * (e₂ : ℝ) - (d₁ : ℝ) ^ 2 - (d₂ : ℝ) * (e₂ : ℝ) := by
          rw [hde₁, hde₂]
      _ = ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₁ : ℝ) - (e₂ : ℝ)) := by ring
  have hrhs_pos : 0 < ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₁ : ℝ) - (e₂ : ℝ)) := by
    have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₁ : ℝ) - (e₂ : ℝ) := by linarith
    positivity
  have hsum_ltR : (d₁ : ℝ) + (e₁ : ℝ) < (d₂ : ℝ) + (e₂ : ℝ) := by nlinarith
  have hsum_cast : ((d₁ + e₁ : ℕ) : ℝ) < ((d₂ + e₂ : ℕ) : ℝ) := by
    push_cast
    exact hsum_ltR
  exact_mod_cast hsum_cast

/-- Any two divisors in `Erdos886Divisors n ε 1` with `1/4 ≤ ε` are equal. -/
theorem eq_of_mem_erdos886Divisors_of_quarter_le
    (n d₁ d₂ : ℕ) (ε : ℝ) (hε : 1 / 4 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1) (hd₂ : d₂ ∈ Erdos886Divisors n ε 1) :
    d₁ = d₂ := by
  rcases lt_trichotomy d₁ d₂ with hlt | rfl | hgt
  · exfalso
    have hdiv₁ : d₁ ∈ Nat.divisors n := (mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁ |>.1
    have hdiv₂ : d₂ ∈ Nat.divisors n := (mem_erdos886Divisors_iff n d₂ ε 1).mp hd₂ |>.1
    have hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) :=
      le_of_lt ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁ |>.2.1)
    have hmono := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hdiv₁ hdiv₂ hs₁ hlt
    have hstep : (d₁ : ℝ) + (n / d₁ : ℕ) + 1 ≤ (d₂ : ℝ) + (n / d₂ : ℕ) := by
      have : d₁ + n / d₁ + 1 ≤ d₂ + n / d₂ := hmono
      have hR : ((d₁ + n / d₁ + 1 : ℕ) : ℝ) ≤ ((d₂ + n / d₂ : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hR
      linarith
    have hgt₁ := complementary_sum_gt_two_sqrt_of_mem_erdos886Divisors n d₁ ε 1 hd₁
    have hlt₂ := complementary_sum_lt_two_sqrt_add_one_of_quarter_le n d₂ ε hε hd₂
    linarith
  · rfl
  · exfalso
    have hdiv₁ : d₁ ∈ Nat.divisors n := (mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁ |>.1
    have hdiv₂ : d₂ ∈ Nat.divisors n := (mem_erdos886Divisors_iff n d₂ ε 1).mp hd₂ |>.1
    have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) :=
      le_of_lt ((mem_erdos886Divisors_iff n d₂ ε 1).mp hd₂ |>.2.1)
    have hmono := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₁ hdiv₂ hdiv₁ hs₂ hgt
    have hstep : (d₂ : ℝ) + (n / d₂ : ℕ) + 1 ≤ (d₁ : ℝ) + (n / d₁ : ℕ) := by
      have : d₂ + n / d₂ + 1 ≤ d₁ + n / d₁ := hmono
      have hR : ((d₂ + n / d₂ + 1 : ℕ) : ℝ) ≤ ((d₁ + n / d₁ : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hR
      linarith
    have hgt₂ := complementary_sum_gt_two_sqrt_of_mem_erdos886Divisors n d₂ ε 1 hd₂
    have hlt₁ := complementary_sum_lt_two_sqrt_add_one_of_quarter_le n d₁ ε hε hd₁
    linarith

/-- Unconditional bound `(Erdos886Divisors n ε 1).card ≤ 1` for all `n : ℕ` and `1/4 ≤ ε`. -/
theorem card_erdos886Divisors_le_one_of_quarter_le (n : ℕ) (ε : ℝ) (hε : 1 / 4 ≤ ε) :
    (Erdos886Divisors n ε 1).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  exact eq_of_mem_erdos886Divisors_of_quarter_le n a b ε hε ha hb

/-- Unconditional resolution of `erdos_886` in the entire regime `ε ≥ 1/4` with `K = 1`. -/
theorem erdos_886_of_quarter_le (ε : ℝ) (hε : 1 / 4 ≤ ε) :
    ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K :=
  ⟨1, Filter.Eventually.of_forall (fun n => card_erdos886Divisors_le_one_of_quarter_le n ε hε)⟩

/-- Whenever `C ≤ (n : ℝ) ^ (ε - 1/4)`, `Erdos886Divisors n ε C ⊆ Erdos886Divisors n (1/4) 1`. -/
theorem erdos886Divisors_subset_quarter_one_of_rpow_ge
    (n : ℕ) (ε C : ℝ) (hC : C ≤ (n : ℝ) ^ (ε - 1 / 4)) :
    Erdos886Divisors n ε C ⊆ Erdos886Divisors n (1 / 4) 1 := by
  intro d hd
  rw [mem_erdos886Divisors_iff] at hd ⊢
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hdiv).2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 - ε) := Real.rpow_nonneg (le_of_lt hn_pos) _
  have hmul : C * (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (ε - 1 / 4) * (n : ℝ) ^ (1 / 2 - ε) :=
    mul_le_mul_of_nonneg_right hC hpow_nonneg
  have hadd : (n : ℝ) ^ (ε - 1 / 4) * (n : ℝ) ^ (1 / 2 - ε) = (n : ℝ) ^ (1 / 2 - (1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hn_pos]
    congr 1
    ring
  refine ⟨hdiv, hlow, ?_⟩
  linarith

/-- For every `ε > 1/4` and every `C : ℝ`, eventually `(Erdos886Divisors n ε C).card ≤ 1`. -/
theorem eventually_card_erdos886Divisors_le_one_of_quarter_lt
    (ε C : ℝ) (hε : 1 / 4 < ε) :
    ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε C).card ≤ 1 := by
  have hpos : 0 < ε - 1 / 4 := by linarith
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (ε - 1 / 4)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop C] with n hn
  exact le_trans
    (Finset.card_le_card (erdos886Divisors_subset_quarter_one_of_rpow_ge n ε C hn))
    (card_erdos886Divisors_le_one_of_quarter_le n (1 / 4) le_rfl)

/-! ## Section 5: Erdős-Rosenfeld [ErRo97] Upper Bound and Infinite 4-Divisor Family -/

/-- All-`n` strengthening of `erdos_886.variants.rosenfeld_bound`: for every `n : ℕ` and `C : ℝ`,
the number of divisors of `n` in `[n^(1/2), n^(1/2) + C * n^(1/4)]` is at most `1 + C^2`. -/
theorem rosenfeld_closed_interval_bound_all_n (n : ℕ) (C : ℝ) :
    (((Nat.divisors n).filter (fun d : ℕ =>
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ) ≤ 1 + C ^ 2 := by
  set D := (Nat.divisors n).filter (fun d : ℕ =>
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
    (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))
  apply card_nat_finset_le_of_strictMonoOn_image_diff D (fun d => d + n / d)
  · intro a ha b hb hlt
    rw [Finset.mem_filter] at ha hb
    exact complementary_sum_strict_mono_of_ge_sqrt n a b ha.1 hb.1 ha.2.1 hlt
  · positivity
  · intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    rcases ha with ⟨hdiv_a, hlow_a, _⟩
    rcases hb with ⟨hdiv_b, hlow_b, hhigh_b⟩
    have hid_a := complementary_divisor_hyperbolic_identity n a hdiv_a
    have hid_b := complementary_divisor_hyperbolic_identity n b hdiv_b
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hdiv_a
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hdiv_b
    have hsq_a_nonneg : 0 ≤ ((a : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
    have hsum_a_ge : 2 * (n : ℝ) ^ (1 / 2 : ℝ) ≤ (a : ℝ) + (n / a : ℕ) := by nlinarith
    have hdiff_b_nonneg : 0 ≤ (b : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
    have hdiff_b_le : (b : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) ≤ C * (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
    have hsq_b_le : ((b : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 ≤ (C * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
      nlinarith
    have hC_sq : (C * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = C ^ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        (C * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = C ^ 2 * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by ring
        _ = C ^ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [rpow_quarter_sq n]
    have hsum_b_le : (b : ℝ) + (n / b : ℕ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) + C ^ 2 := by nlinarith
    push_cast
    linarith

/-- Complete proof of `erdos_886.variants.rosenfeld_bound` from
`FormalConjectures/ErdosProblems/886.lean`. -/
theorem erdos_886_rosenfeld_bound :
    ∀ C > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
    (((Nat.divisors n).filter (fun (d : ℕ) =>
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
      ≤ 1 + C ^ 2 := by
  intro C _
  exact Filter.Eventually.of_forall (fun n => rosenfeld_closed_interval_bound_all_n n C)

/-- Universal upper bound `(Erdos886Divisors n ε C).card ≤ ⌊C^2⌋₊ + 1` for all `n : ℕ`,
`ε ≥ 1/4`, and `C ≥ 0`. -/
theorem card_erdos886Divisors_le_floor_sq_add_one_of_quarter_le
    (n : ℕ) (ε C : ℝ) (hε : 1 / 4 ≤ ε) (hC : 0 ≤ C) :
    (Erdos886Divisors n ε C).card ≤ ⌊C ^ 2⌋₊ + 1 := by
  have hsub1 : Erdos886Divisors n ε C ⊆ Erdos886Divisors n (1 / 4) C :=
    erdos886Divisors_antitone_eps n (1 / 4) ε C hε hC
  have hsub2 : Erdos886Divisors n (1 / 4) C ⊆
      (Nat.divisors n).filter (fun d : ℕ =>
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ)) := by
    intro d hd
    rw [mem_erdos886Divisors_iff] at hd
    rw [Finset.mem_filter]
    have hexp : (1 / 2 : ℝ) - (1 / 4 : ℝ) = (1 / 4 : ℝ) := by ring
    rw [hexp] at hd
    exact ⟨hd.1, le_of_lt hd.2.1, le_of_lt hd.2.2⟩
  have hcard_le : ((Erdos886Divisors n ε C).card : ℝ) ≤ 1 + C ^ 2 := by
    have hle_nat : (Erdos886Divisors n ε C).card ≤
        ((Nat.divisors n).filter (fun d : ℕ =>
          (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
          (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card :=
      Finset.card_le_card (Finset.Subset.trans hsub1 hsub2)
    have hle_R : ((Erdos886Divisors n ε C).card : ℝ) ≤
        (((Nat.divisors n).filter (fun d : ℕ =>
          (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
          (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ) := by
      exact_mod_cast hle_nat
    exact le_trans hle_R (rosenfeld_closed_interval_bound_all_n n C)
  rcases (Erdos886Divisors n ε C).eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  · have hcard_pos : 1 ≤ (Erdos886Divisors n ε C).card := Finset.card_pos.mpr hne
    have hsub_le : ((Erdos886Divisors n ε C).card - 1 : ℕ) ≤ ⌊C ^ 2⌋₊ := by
      apply Nat.le_floor
      have hcast : (((Erdos886Divisors n ε C).card - 1 : ℕ) : ℝ) =
          ((Erdos886Divisors n ε C).card : ℝ) - 1 := by
        rw [Nat.cast_sub hcard_pos, Nat.cast_one]
      linarith
    omega

/-- Parametric family `n(m) = ∏_{j ∈ {3,4,5,6,8,9,10,11}} (m + j)` (i.e., `(k^2 - 1)(k^2 - 4)(k^2 - 9)(k^2 - 16)`
at `k = m + 7`) with at least 4 divisors in `(n^(1/2), n^(1/2) + 16 n^(1/4))`. -/
def rosenfeldN (m : ℕ) : ℕ :=
  (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 8) * (m + 9) * (m + 10) * (m + 11)

/-- First near-square divisor of `rosenfeldN m` above `(rosenfeldN m)^(1/2)`. -/
def rosenfeldD1 (m : ℕ) : ℕ := (m + 4) * (m + 5) * (m + 8) * (m + 11)
/-- Second near-square divisor of `rosenfeldN m` above `(rosenfeldN m)^(1/2)`. -/
def rosenfeldD2 (m : ℕ) : ℕ := (m + 4) * (m + 5) * (m + 9) * (m + 10)
/-- Third near-square divisor of `rosenfeldN m` above `(rosenfeldN m)^(1/2)`. -/
def rosenfeldD3 (m : ℕ) : ℕ := (m + 4) * (m + 6) * (m + 8) * (m + 10)
/-- Fourth near-square divisor of `rosenfeldN m` above `(rosenfeldN m)^(1/2)`. -/
def rosenfeldD4 (m : ℕ) : ℕ := (m + 5) * (m + 6) * (m + 8) * (m + 9)

/-- Strict ordering `rosenfeldD1 m < rosenfeldD2 m`. -/
theorem rosenfeldD1_lt_D2 (m : ℕ) : rosenfeldD1 m < rosenfeldD2 m := by
  have h : (rosenfeldD2 m : ℝ) - (rosenfeldD1 m : ℝ) = 2 * (m : ℝ) ^ 2 + 18 * (m : ℝ) + 40 := by
    unfold rosenfeldD1 rosenfeldD2; push_cast; ring
  have hlt : (rosenfeldD1 m : ℝ) < (rosenfeldD2 m : ℝ) := by
    linarith [sq_nonneg (m : ℝ), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact_mod_cast hlt

/-- Strict ordering `rosenfeldD2 m < rosenfeldD3 m`. -/
theorem rosenfeldD2_lt_D3 (m : ℕ) : rosenfeldD2 m < rosenfeldD3 m := by
  have h : (rosenfeldD3 m : ℝ) - (rosenfeldD2 m : ℝ) = 3 * (m : ℝ) ^ 2 + 42 * (m : ℝ) + 120 := by
    unfold rosenfeldD2 rosenfeldD3; push_cast; ring
  have hlt : (rosenfeldD2 m : ℝ) < (rosenfeldD3 m : ℝ) := by
    linarith [sq_nonneg (m : ℝ), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact_mod_cast hlt

/-- Strict ordering `rosenfeldD3 m < rosenfeldD4 m`. -/
theorem rosenfeldD3_lt_D4 (m : ℕ) : rosenfeldD3 m < rosenfeldD4 m := by
  have h : (rosenfeldD4 m : ℝ) - (rosenfeldD3 m : ℝ) = 5 * (m : ℝ) ^ 2 + 70 * (m : ℝ) + 240 := by
    unfold rosenfeldD3 rosenfeldD4; push_cast; ring
  have hlt : (rosenfeldD3 m : ℝ) < (rosenfeldD4 m : ℝ) := by
    linarith [sq_nonneg (m : ℝ), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact_mod_cast hlt

/-- All four divisors `rosenfeldD1 m, ..., rosenfeldD4 m` belong to `Erdos886Divisors (rosenfeldN m) (1/4) 16`. -/
theorem rosenfeld_divisors_mem (m : ℕ) :
    rosenfeldD1 m ∈ Erdos886Divisors (rosenfeldN m) (1 / 4) 16 ∧
    rosenfeldD2 m ∈ Erdos886Divisors (rosenfeldN m) (1 / 4) 16 ∧
    rosenfeldD3 m ∈ Erdos886Divisors (rosenfeldN m) (1 / 4) 16 ∧
    rosenfeldD4 m ∈ Erdos886Divisors (rosenfeldN m) (1 / 4) 16 := by
  have hn0 : rosenfeldN m ≠ 0 := by unfold rosenfeldN; positivity
  have hdvd1 : rosenfeldD1 m ∣ rosenfeldN m := ⟨(m + 3) * (m + 6) * (m + 9) * (m + 10), by unfold rosenfeldN rosenfeldD1; ring⟩
  have hdvd2 : rosenfeldD2 m ∣ rosenfeldN m := ⟨(m + 3) * (m + 6) * (m + 8) * (m + 11), by unfold rosenfeldN rosenfeldD2; ring⟩
  have hdvd3 : rosenfeldD3 m ∣ rosenfeldN m := ⟨(m + 3) * (m + 5) * (m + 9) * (m + 11), by unfold rosenfeldN rosenfeldD3; ring⟩
  have hdvd4 : rosenfeldD4 m ∣ rosenfeldN m := ⟨(m + 3) * (m + 4) * (m + 10) * (m + 11), by unfold rosenfeldN rosenfeldD4; ring⟩
  have hlt12 : (rosenfeldD1 m : ℝ) < (rosenfeldD2 m : ℝ) := by exact_mod_cast rosenfeldD1_lt_D2 m
  have hlt23 : (rosenfeldD2 m : ℝ) < (rosenfeldD3 m : ℝ) := by exact_mod_cast rosenfeldD2_lt_D3 m
  have hlt34 : (rosenfeldD3 m : ℝ) < (rosenfeldD4 m : ℝ) := by exact_mod_cast rosenfeldD3_lt_D4 m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlow1 : (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) < (rosenfeldD1 m : ℝ) := by
    have hsq : ((rosenfeldN m : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (rosenfeldN m : ℝ) := rpow_half_sq (rosenfeldN m)
    have hdiff : (rosenfeldD1 m : ℝ) ^ 2 - (rosenfeldN m : ℝ) =
        20 * (m : ℝ) ^ 5 + 700 * (m : ℝ) ^ 4 + 9500 * (m : ℝ) ^ 3 + 62500 * (m : ℝ) ^ 2 + 199280 * (m : ℝ) + 246400 := by
      unfold rosenfeldD1 rosenfeldN; push_cast; ring
    have hpos : 0 < (rosenfeldD1 m : ℝ) ^ 2 - (rosenfeldN m : ℝ) := by rw [hdiff]; positivity
    have hd1_nonneg : 0 ≤ (rosenfeldD1 m : ℝ) := Nat.cast_nonneg _
    nlinarith
  set s_low : ℝ := (m : ℝ) ^ 4 + 28 * (m : ℝ) ^ 3 + 279 * (m : ℝ) ^ 2 + 1162 * (m : ℝ) + 1666
  set q_low : ℝ := (m : ℝ) ^ 2 + 14 * (m : ℝ) + 41
  have hs_lt : s_low < (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) := by
    have hsq : ((rosenfeldN m : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (rosenfeldN m : ℝ) := rpow_half_sq (rosenfeldN m)
    have hdiff : (rosenfeldN m : ℝ) - s_low ^ 2 =
        48 * (m : ℝ) ^ 4 + 1344 * (m : ℝ) ^ 3 + 13292 * (m : ℝ) ^ 2 + 54376 * (m : ℝ) + 75644 := by
      unfold rosenfeldN s_low; push_cast; ring
    have hpos : 0 < (rosenfeldN m : ℝ) - s_low ^ 2 := by rw [hdiff]; positivity
    have hs_nonneg : 0 ≤ (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hq_lt : q_low < (rosenfeldN m : ℝ) ^ (1 / 4 : ℝ) := by
    have hsq1 : ((rosenfeldN m : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (rosenfeldN m : ℝ) := rpow_half_sq (rosenfeldN m)
    have hsq2 : ((rosenfeldN m : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) := rpow_quarter_sq (rosenfeldN m)
    have hdiff : (rosenfeldN m : ℝ) - (q_low ^ 2) ^ 2 =
        2 * (m : ℝ) ^ 6 + 84 * (m : ℝ) ^ 5 + 1359 * (m : ℝ) ^ 4 + 10612 * (m : ℝ) ^ 3 + 40624 * (m : ℝ) ^ 2 + 66584 * (m : ℝ) + 25439 := by
      unfold rosenfeldN q_low; push_cast; ring
    have hpos : 0 < (rosenfeldN m : ℝ) - (q_low ^ 2) ^ 2 := by rw [hdiff]; positivity
    have hs_nonneg : 0 ≤ (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hq_nonneg : 0 ≤ (rosenfeldN m : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hq2_lt : q_low ^ 2 < (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
    nlinarith
  have hhigh4 : (rosenfeldD4 m : ℝ) < (rosenfeldN m : ℝ) ^ (1 / 2 : ℝ) + 16 * (rosenfeldN m : ℝ) ^ (1 / 2 - (1 / 4 : ℝ)) := by
    have hexp : (1 / 2 : ℝ) - (1 / 4 : ℝ) = (1 / 4 : ℝ) := by ring
    rw [hexp]
    have hdiff : s_low + 16 * q_low - (rosenfeldD4 m : ℝ) = 6 * (m : ℝ) ^ 2 + 84 * (m : ℝ) + 162 := by
      unfold rosenfeldD4 s_low q_low; push_cast; ring
    have hpos : 0 < s_low + 16 * q_low - (rosenfeldD4 m : ℝ) := by rw [hdiff]; positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_erdos886Divisors_iff]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd1, hn0⟩, hlow1, by linarith⟩
  · rw [mem_erdos886Divisors_iff]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd2, hn0⟩, by linarith, by linarith⟩
  · rw [mem_erdos886Divisors_iff]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd3, hn0⟩, by linarith, by linarith⟩
  · rw [mem_erdos886Divisors_iff]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd4, hn0⟩, by linarith, hhigh4⟩

/-- For every `m : ℕ`, `rosenfeldN m` has at least 4 divisors in `(n^(1/2), n^(1/2) + 16 n^(1/4))`. -/
theorem four_le_card_erdos886Divisors_rosenfeldN (m : ℕ) :
    4 ≤ (Erdos886Divisors (rosenfeldN m) (1 / 4) 16).card := by
  obtain ⟨h1, h2, h3, h4⟩ := rosenfeld_divisors_mem m
  have hlt12 := rosenfeldD1_lt_D2 m
  have hlt23 := rosenfeldD2_lt_D3 m
  have hlt34 := rosenfeldD3_lt_D4 m
  let S : Finset ℕ := {rosenfeldD1 m, rosenfeldD2 m, rosenfeldD3 m, rosenfeldD4 m}
  have hsub : S ⊆ Erdos886Divisors (rosenfeldN m) (1 / 4) 16 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : S.card = 4 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Unbounded growth `m < rosenfeldN m` for all `m : ℕ`. -/
theorem lt_rosenfeldN (m : ℕ) : m < rosenfeldN m := by
  have hpos : 0 < (m + 4) * (m + 5) * (m + 6) * (m + 8) * (m + 9) * (m + 10) * (m + 11) := by positivity
  have hle : m + 3 ≤ rosenfeldN m := by
    have hmul := Nat.mul_le_mul_left (m + 3) hpos
    have heq : (m + 3) * ((m + 4) * (m + 5) * (m + 6) * (m + 8) * (m + 9) * (m + 10) * (m + 11)) = rosenfeldN m := by
      unfold rosenfeldN; ring
    omega
  omega

/-- Complete proof of `erdos_886.variants.rosenfeld_infinite` from
`FormalConjectures/ErdosProblems/886.lean`. -/
theorem erdos_886_rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card} := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  exact ⟨rosenfeldN a, four_le_card_erdos886Divisors_rosenfeldN a, lt_rosenfeldN a⟩

end Erdos886




/-!
# Complementary Divisor Involution, Difference-of-Squares Factorization, and Second-Order Hyperbolic Determinant Constraints for Erdős Problem #886

Complementary divisor involution and mirror-window geometry, difference-of-squares
factorization, and second-order hyperbolic determinant constraints for Erdős Problem #886:

1. **Complementary Divisor Involution $d \leftrightarrow n/d$ and Mirror-Window Geometry:**
   - `div_self_mem_divisors_of_mem_erdos886Divisors`
   - `div_self_lt_sqrt_of_mem_erdos886Divisors`
   - `div_self_lt_self_of_mem_erdos886Divisors`
   - `not_mem_erdos886Divisors_div_self`
   - `div_div_self_of_mem_erdos886Divisors`
   - `injOn_div_self_erdos886Divisors`
   - `disjoint_erdos886Divisors_image_div_self`
   - `two_mul_card_erdos886Divisors_le_card_divisors`
   - `mul_sqrt_sub_complementary_eq_sqrt_mul_sub_sqrt`
   - `sqrt_sub_complementary_lt_sub_sqrt`
   - `complementary_divisor_gt_sqrt_sub_window`

2. **Difference-of-Squares Factorization $a^2 - b^2 = n$ and Factor-Difference Spacing:**
   - `complementary_diff_lt_two_mul_window`
   - `complementary_diff_step_two_of_ge_sqrt`
   - `diff_of_squares_factorization_of_even_diff`
   - `pairwise_sum_sq_sub_eq_diff_sq_sub`
   - `complementary_sum_diff_product_identity`
   - `complementary_diff_product_identity`

3. **Second-Order Hyperbolic Gap & Bambah–Chowla Determinant Constraints on 3-Tuples and 4-Tuples:**
   - `second_order_hyperbolic_gap_triple_identity`
   - `second_order_hyperbolic_gap_lower_bound_of_lt`
   - `bambah_chowla_quadruple_cross_identity`
   - `bambah_chowla_quadruple_pos_of_strict_mono`

4. **General Ruzsa / Béal–Tenenbaum Hyperbolic-Sum Span Bounds & $1/6 \le \varepsilon < 1/4$ Thresholds:**
   - `complementary_sum_sub_two_sqrt_lt_of_mem_erdos886Divisors`
   - `complementary_sum_span_lt_of_mem_erdos886Divisors`
   - `card_erdos886Divisors_le_one_add_sq_mul_rpow`
   - `two_lt_sq_mul_rpow_of_three_mem_erdos886Divisors`
   - `three_lt_sq_mul_rpow_of_four_mem_erdos886Divisors`
   - `gt_729_of_four_mem_erdos886Divisors_of_sixth_le`
-/

namespace Erdos886

/-! ## Section 6: Complementary Divisor Involution $d \leftrightarrow n/d$ and Mirror-Window Geometry -/

/-- For every divisor `d ∈ Erdos886Divisors n ε C`, its complementary quotient `n / d`
belongs to `Nat.divisors n`. -/
theorem div_self_mem_divisors_of_mem_erdos886Divisors
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    n / d ∈ Nat.divisors n := by
  rcases Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d ε C).mp hd).1 with ⟨hdvd, hn0⟩
  exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0⟩

/-- For every `d ∈ Erdos886Divisors n ε C`, its complementary divisor `n / d` lies
strictly below `n^(1/2)`. -/
theorem div_self_lt_sqrt_of_mem_erdos886Divisors
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    ((n / d : ℕ) : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by
  rcases (mem_erdos886Divisors_iff n d ε C).mp hd with ⟨hdiv, hlow, _⟩
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hdiv).1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hdiv).2
  have hde : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have hs_pos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  nlinarith

/-- Every `d ∈ Erdos886Divisors n ε C` is strictly larger than its complementary divisor `n / d`. -/
theorem div_self_lt_self_of_mem_erdos886Divisors
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    n / d < d := by
  have h1 : ((n / d : ℕ) : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) :=
    div_self_lt_sqrt_of_mem_erdos886Divisors n d ε C hd
  have h2 : (n : ℝ) ^ (1 / 2 : ℝ) < (d : ℝ) :=
    ((mem_erdos886Divisors_iff n d ε C).mp hd).2.1
  have hlt : ((n / d : ℕ) : ℝ) < (d : ℝ) := lt_trans h1 h2
  exact_mod_cast hlt

/-- For every `d ∈ Erdos886Divisors n ε C`, its complementary divisor `n / d` does not belong
to `Erdos886Divisors n ε C`. -/
theorem not_mem_erdos886Divisors_div_self
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    n / d ∉ Erdos886Divisors n ε C := by
  intro hmem
  have hlt : ((n / d : ℕ) : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) :=
    div_self_lt_sqrt_of_mem_erdos886Divisors n d ε C hd
  have hgt : (n : ℝ) ^ (1 / 2 : ℝ) < ((n / d : ℕ) : ℝ) :=
    ((mem_erdos886Divisors_iff n (n / d) ε C).mp hmem).2.1
  linarith

/-- Exact involution `n / (n / d) = d` for every `d ∈ Erdos886Divisors n ε C`. -/
theorem div_div_self_of_mem_erdos886Divisors
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    n / (n / d) = d := by
  rcases Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d ε C).mp hd).1 with ⟨hdvd, hn0⟩
  exact Nat.div_div_self hdvd hn0

/-- The complementary divisor map `d ↦ n / d` is injective on `Erdos886Divisors n ε C`. -/
theorem injOn_div_self_erdos886Divisors (n : ℕ) (ε C : ℝ) :
    Set.InjOn (fun d => n / d) (Erdos886Divisors n ε C) := by
  intro d₁ hd₁ d₂ hd₂ heq
  dsimp at heq
  have h1 := div_div_self_of_mem_erdos886Divisors n d₁ ε C hd₁
  have h2 := div_div_self_of_mem_erdos886Divisors n d₂ ε C hd₂
  rw [← h1, ← h2, heq]

/-- `Erdos886Divisors n ε C` is disjoint from its complementary-divisor image under `d ↦ n / d`. -/
theorem disjoint_erdos886Divisors_image_div_self (n : ℕ) (ε C : ℝ) :
    Disjoint (Erdos886Divisors n ε C) ((Erdos886Divisors n ε C).image (fun d => n / d)) := by
  rw [Finset.disjoint_right]
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
  exact not_mem_erdos886Divisors_div_self n d ε C hd

/-- Involution pairing bound: `2 * (Erdos886Divisors n ε C).card ≤ (Nat.divisors n).card`. -/
theorem two_mul_card_erdos886Divisors_le_card_divisors (n : ℕ) (ε C : ℝ) :
    2 * (Erdos886Divisors n ε C).card ≤ (Nat.divisors n).card := by
  set A := Erdos886Divisors n ε C
  set B := A.image (fun d => n / d)
  have hdisj : Disjoint A B := disjoint_erdos886Divisors_image_div_self n ε C
  have hcardB : B.card = A.card :=
    Finset.card_image_of_injOn (injOn_div_self_erdos886Divisors n ε C)
  have hsub : A ∪ B ⊆ Nat.divisors n := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact ((mem_erdos886Divisors_iff n x ε C).mp hxA).1
    · rcases Finset.mem_image.mp hxB with ⟨d, hd, rfl⟩
      exact div_self_mem_divisors_of_mem_erdos886Divisors n d ε C hd
  have hle : (A ∪ B).card ≤ (Nat.divisors n).card := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcardB] at hle
  omega

/-- Exact scaling relation between the lower gap `n^(1/2) - n/d` and upper gap `d - n^(1/2)`:
`d * (n^(1/2) - n/d) = n^(1/2) * (d - n^(1/2))` for every divisor `d ∈ Nat.divisors n`. -/
theorem mul_sqrt_sub_complementary_eq_sqrt_mul_sub_sqrt
    (n d : ℕ) (hd : d ∈ Nat.divisors n) :
    (d : ℝ) * ((n : ℝ) ^ (1 / 2 : ℝ) - (n / d : ℕ)) =
      (n : ℝ) ^ (1 / 2 : ℝ) * ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) := by
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdeR : (d : ℝ) * (n / d : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  calc
    (d : ℝ) * ((n : ℝ) ^ (1 / 2 : ℝ) - (n / d : ℕ))
      = (d : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) - (d : ℝ) * (n / d : ℕ) := by ring
    _ = (d : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) - (n : ℝ) := by rw [hdeR]
    _ = (d : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) - ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by rw [hs_sq]
    _ = (n : ℝ) ^ (1 / 2 : ℝ) * ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) := by ring

/-- Hyperbolic gap asymmetry: for every `d ∈ Erdos886Divisors n ε C`, the lower gap
`n^(1/2) - n/d` is strictly smaller than the upper gap `d - n^(1/2)`. -/
theorem sqrt_sub_complementary_lt_sub_sqrt
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    (n : ℝ) ^ (1 / 2 : ℝ) - (n / d : ℕ) < (d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hsum := complementary_sum_gt_two_sqrt_of_mem_erdos886Divisors n d ε C hd
  linarith

/-- Mirror-window lower bound: for every `d ∈ Erdos886Divisors n ε C`, its complementary
divisor `n / d` lies in `(n^(1/2) - C * n^(1/2 - ε), n^(1/2))`. -/
theorem complementary_divisor_gt_sqrt_sub_window
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    (n : ℝ) ^ (1 / 2 : ℝ) - C * (n : ℝ) ^ (1 / 2 - ε) < (n / d : ℕ) := by
  have h1 := sqrt_sub_complementary_lt_sub_sqrt n d ε C hd
  have h2 := ((mem_erdos886Divisors_iff n d ε C).mp hd).2.2
  linarith

/-! ## Section 7: Difference-of-Squares Factorization $a^2 - b^2 = n$ and Factor-Difference Spacing -/

/-- Every `d ∈ Erdos886Divisors n ε C` has factor difference `d - n / d < 2 * C * n^(1/2 - ε)`. -/
theorem complementary_diff_lt_two_mul_window
    (n d : ℕ) (ε C : ℝ) (hd : d ∈ Erdos886Divisors n ε C) :
    ((d - n / d : ℕ) : ℝ) < 2 * C * (n : ℝ) ^ (1 / 2 - ε) := by
  have hle : n / d ≤ d := le_of_lt (div_self_lt_self_of_mem_erdos886Divisors n d ε C hd)
  rw [Nat.cast_sub hle]
  have h1 := complementary_divisor_gt_sqrt_sub_window n d ε C hd
  have h2 := ((mem_erdos886Divisors_iff n d ε C).mp hd).2.2
  linarith

/-- On divisors `n^(1/2) ≤ d₁ < d₂`, the factor difference `d ↦ d - n / d` increases by at least `2`. -/
theorem complementary_diff_step_two_of_ge_sqrt
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    d₁ - n / d₁ + 2 ≤ d₂ - n / d₂ := by
  have hdvd₁ : d₁ ∣ n := (Nat.mem_divisors.mp hd₁).1
  have hdvd₂ : d₂ ∣ n := (Nat.mem_divisors.mp hd₂).1
  have hde₁ : (d₁ : ℝ) * ((n / d₁ : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd₁
  have hde₂ : (d₂ : ℝ) * ((n / d₂ : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd₂
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have hs_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hltR : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have he₁_pos : (0 : ℝ) < ((n / d₁ : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors
      (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd₁, (Nat.mem_divisors.mp hd₁).2⟩)
  have he₁_le_d₁R : ((n / d₁ : ℕ) : ℝ) ≤ (d₁ : ℝ) := by nlinarith
  have he₂_lt_e₁R : ((n / d₂ : ℕ) : ℝ) < ((n / d₁ : ℕ) : ℝ) := by nlinarith
  have he₁_le_d₁ : n / d₁ ≤ d₁ := by exact_mod_cast he₁_le_d₁R
  have he₂_lt_e₁ : n / d₂ < n / d₁ := by exact_mod_cast he₂_lt_e₁R
  omega

/-- Integer difference-of-squares factorization: whenever `d ∈ Nat.divisors n` satisfies
`n / d ≤ d` and `2 ∣ d - n / d`, the integers `a = (d + n / d) / 2` and `b = (d - n / d) / 2`
satisfy `a ^ 2 - b ^ 2 = n`. -/
theorem diff_of_squares_factorization_of_even_diff
    (n d : ℕ) (hd : d ∈ Nat.divisors n) (hle : n / d ≤ d) (heven : 2 ∣ d - n / d) :
    ((d + n / d) / 2) ^ 2 - ((d - n / d) / 2) ^ 2 = n := by
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hde : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  generalize he : n / d = e at hle heven hde ⊢
  rcases heven with ⟨b, hb⟩
  have hd_eq : d = e + 2 * b := by omega
  have hsum_div : (d + e) / 2 = e + b := by omega
  have hdiff_div : (d - e) / 2 = b := by omega
  rw [hsum_div, hdiff_div]
  have hle_eb : b ≤ e + b := by omega
  have hsq_ge : b ^ 2 ≤ (e + b) ^ 2 := Nat.pow_le_pow_left hle_eb 2
  have hR : ((((e + b) ^ 2 - b ^ 2 : ℕ)) : ℝ) = (n : ℝ) := by
    rw [Nat.cast_sub hsq_ge]
    have hdeR : (d : ℝ) * (e : ℝ) = (n : ℝ) := by exact_mod_cast hde
    have hdR : (d : ℝ) = (e : ℝ) + 2 * (b : ℝ) := by exact_mod_cast hd_eq
    push_cast
    linear_combination -(e : ℝ) * hdR + hdeR
  exact_mod_cast hR

/-- Hyperbolic secant identity for any two divisors `d₁, d₂ ∈ Nat.divisors n`:
`(d₂ + n/d₂)^2 - (d₁ + n/d₁)^2 = (d₂ - n/d₂)^2 - (d₁ - n/d₁)^2`. -/
theorem pairwise_sum_sq_sub_eq_diff_sq_sub
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    ((d₂ : ℝ) + (n / d₂ : ℕ)) ^ 2 - ((d₁ : ℝ) + (n / d₁ : ℕ)) ^ 2 =
      ((d₂ : ℝ) - (n / d₂ : ℕ)) ^ 2 - ((d₁ : ℝ) - (n / d₁ : ℕ)) ^ 2 := by
  have h1 := four_mul_eq_sum_sq_sub_diff_sq n d₁ hd₁
  have h2 := four_mul_eq_sum_sq_sub_diff_sq n d₂ hd₂
  linarith

/-- Exact first-order secant product identity for complementary divisor sums:
`d₁ * d₂ * ((d₂ + n/d₂) - (d₁ + n/d₁)) = (d₂ - d₁) * (d₁ * d₂ - n)`. -/
theorem complementary_sum_diff_product_identity
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₁ : ℝ) * (d₂ : ℝ) - (n : ℝ)) := by
  have hde₁ : (d₁ : ℝ) * (n / d₁ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₁).1
  have hde₂ : (d₂ : ℝ) * (n / d₂ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₂).1
  linear_combination (d₁ : ℝ) * hde₂ - (d₂ : ℝ) * hde₁

/-- Dual first-order secant product identity for complementary divisor differences:
`d₁ * d₂ * ((d₂ - n/d₂) - (d₁ - n/d₁)) = (d₂ - d₁) * (d₁ * d₂ + n)`. -/
theorem complementary_diff_product_identity
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (((d₂ : ℝ) - (n / d₂ : ℕ)) - ((d₁ : ℝ) - (n / d₁ : ℕ))) =
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₁ : ℝ) * (d₂ : ℝ) + (n : ℝ)) := by
  have hde₁ : (d₁ : ℝ) * (n / d₁ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₁).1
  have hde₂ : (d₂ : ℝ) * (n / d₂ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₂).1
  linear_combination (d₂ : ℝ) * hde₁ - (d₁ : ℝ) * hde₂

/-! ## Section 8: Second-Order Hyperbolic Gap & Bambah–Chowla Determinant Constraints -/

/-- Exact second-order hyperbolic gap identity on any 3 divisors `d₁, d₂, d₃ ∈ Nat.divisors n`:
eliminating `n` between adjacent secants yields the exact Vandermonde product
`(d₂ - d₁) * d₃ * (s₃ - s₂) - (d₃ - d₂) * d₁ * (s₂ - s₁) = (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁)`. -/
theorem second_order_hyperbolic_gap_triple_identity
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
      ((d₃ : ℝ) - (d₂ : ℝ)) * (d₁ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h23 := complementary_sum_diff_product_identity n d₂ d₃ hd₂ hd₃
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hmul :
      (d₂ : ℝ) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (d₁ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
      (d₂ : ℝ) * (((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ))) := by
    linear_combination ((d₂ : ℝ) - (d₁ : ℝ)) * h23 - ((d₃ : ℝ) - (d₂ : ℝ)) * h12
  exact mul_left_cancel₀ (ne_of_gt hd₂_pos) hmul

/-- For any strictly increasing triple of divisors `d₁ < d₂ < d₃` of `n`, the weighted
second-order hyperbolic gap is at least `2`. -/
theorem second_order_hyperbolic_gap_lower_bound_of_lt
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    ((d₃ : ℝ) - (d₂ : ℝ)) * (d₁ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 2 ≤
      ((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) := by
  have hid := second_order_hyperbolic_gap_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  have h12_nat : d₁ + 1 ≤ d₂ := hlt12
  have h23_nat : d₂ + 1 ≤ d₃ := hlt23
  have h13_nat : d₁ + 2 ≤ d₃ := by omega
  have h12R : (1 : ℝ) ≤ (d₂ : ℝ) - (d₁ : ℝ) := by
    have : ((d₁ + 1 : ℕ) : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast h12_nat
    push_cast at this; linarith
  have h23R : (1 : ℝ) ≤ (d₃ : ℝ) - (d₂ : ℝ) := by
    have : ((d₂ + 1 : ℕ) : ℝ) ≤ (d₃ : ℝ) := by exact_mod_cast h23_nat
    push_cast at this; linarith
  have h13R : (2 : ℝ) ≤ (d₃ : ℝ) - (d₁ : ℝ) := by
    have : ((d₁ + 2 : ℕ) : ℝ) ≤ (d₃ : ℝ) := by exact_mod_cast h13_nat
    push_cast at this; linarith
  have hprod1 : (1 : ℝ) ≤ ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) := by nlinarith
  have hprod2 : (2 : ℝ) ≤ ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    nlinarith
  linarith

/-- Bambah–Chowla 4-divisor cross-determinant identity: for any four divisors
`d₁, d₂, d₃, d₄ ∈ Nat.divisors n`, eliminating `n` between the `(d₁, d₂)` and `(d₃, d₄)`
hyperbolic secants yields `(d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂)`. -/
theorem bambah_chowla_quadruple_cross_identity
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (d₄ : ℝ) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
      ((d₄ : ℝ) - (d₃ : ℝ)) * (d₁ : ℝ) * (d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₃ : ℝ) * (d₄ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h34 := complementary_sum_diff_product_identity n d₃ d₄ hd₃ hd₄
  linear_combination ((d₂ : ℝ) - (d₁ : ℝ)) * h34 - ((d₄ : ℝ) - (d₃ : ℝ)) * h12

/-- Strict positivity of the Bambah–Chowla 4-divisor cross-determinant for any strictly
increasing quadruple `d₁ < d₂ < d₃ < d₄` of divisors of `n`. -/
theorem bambah_chowla_quadruple_pos_of_strict_mono
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    ((d₄ : ℝ) - (d₃ : ℝ)) * (d₁ : ℝ) * (d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) <
      ((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (d₄ : ℝ) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) := by
  have hid := bambah_chowla_quadruple_cross_identity n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄
  have h12R : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
  have h23R : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
  have h34R : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hprod_lt : (d₁ : ℝ) * (d₂ : ℝ) < (d₃ : ℝ) * (d₄ : ℝ) := by nlinarith
  have hrhs_pos :
      0 < ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₃ : ℝ) * (d₄ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
    have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₃ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) * (d₄ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) := by linarith
    positivity
  linarith

/-! ## Section 9: General Ruzsa / Béal–Tenenbaum Hyperbolic-Sum Span Bounds & $1/6 \le \varepsilon < 1/4$ Thresholds -/

/-- Universal upper bound on the complementary-sum excess above `2 * n^(1/2)`:
for every `d ∈ Erdos886Divisors n ε C` with `C ≥ 0`,
`(d : ℝ) + (n / d : ℕ) - 2 * n^(1/2) < C^2 * n^(1/2 - 2 * ε)`. -/
theorem complementary_sum_sub_two_sqrt_lt_of_mem_erdos886Divisors
    (n d : ℕ) (ε C : ℝ) (hC : 0 ≤ C) (hd : d ∈ Erdos886Divisors n ε C) :
    (d : ℝ) + (n / d : ℕ) - 2 * (n : ℝ) ^ (1 / 2 : ℝ) <
      C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  rw [mem_erdos886Divisors_iff] at hd
  rcases hd with ⟨hdiv, hlow, hhigh⟩
  have hid := complementary_divisor_hyperbolic_identity n d hdiv
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hdiv).2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hdiv
  have hdiff_pos : 0 < (d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
  have hdiff_lt : (d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ) < C * (n : ℝ) ^ (1 / 2 - ε) := by linarith
  have hsq_lt : ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 < (C * (n : ℝ) ^ (1 / 2 - ε)) ^ 2 := by
    nlinarith
  have hrpow_eq : ((n : ℝ) ^ (1 / 2 - ε)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
    rw [sq, ← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]
    congr 1
    ring
  have hsq_eq :
      (C * (n : ℝ) ^ (1 / 2 - ε)) ^ 2 =
        (n : ℝ) ^ (1 / 2 : ℝ) * (C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε)) := by
    linear_combination C ^ 2 * hrpow_eq
  have hnonneg : 0 ≤ C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
    have : 0 ≤ (n : ℝ) ^ (1 / 2 - 2 * ε) := Real.rpow_nonneg (le_of_lt hn_pos) _
    positivity
  have hle_d :
      (n : ℝ) ^ (1 / 2 : ℝ) * (C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε)) ≤
        (d : ℝ) * (C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε)) :=
    mul_le_mul_of_nonneg_right (le_of_lt hlow) hnonneg
  nlinarith

/-- Pairwise complementary-sum span bound on `Erdos886Divisors n ε C`: for any
`a, b ∈ Erdos886Divisors n ε C` with `C ≥ 0`,
`((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)) < C^2 * n^(1/2 - 2 * ε)`. -/
theorem complementary_sum_span_lt_of_mem_erdos886Divisors
    (n a b : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (ha : a ∈ Erdos886Divisors n ε C) (hb : b ∈ Erdos886Divisors n ε C) :
    ((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)) <
      C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have ha_gt := complementary_sum_gt_two_sqrt_of_mem_erdos886Divisors n a ε C ha
  have hb_lt := complementary_sum_sub_two_sqrt_lt_of_mem_erdos886Divisors n b ε C hC hb
  linarith

/-- General hyperbolic-sum cardinality bound across all `ε ∈ ℝ` and `C ≥ 0`:
`((Erdos886Divisors n ε C).card : ℝ) ≤ 1 + C^2 * n^(1/2 - 2 * ε)`. -/
theorem card_erdos886Divisors_le_one_add_sq_mul_rpow
    (n : ℕ) (ε C : ℝ) (hC : 0 ≤ C) :
    ((Erdos886Divisors n ε C).card : ℝ) ≤ 1 + C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hB : 0 ≤ C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
    have : 0 ≤ (n : ℝ) ^ (1 / 2 - 2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  apply card_nat_finset_le_of_strictMonoOn_image_diff
    (Erdos886Divisors n ε C) (fun d => d + n / d)
  · intro a ha b hb hlt
    have ha_mem := (mem_erdos886Divisors_iff n a ε C).mp ha
    have hb_mem := (mem_erdos886Divisors_iff n b ε C).mp hb
    exact complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt
  · exact hB
  · intro a ha b hb
    have hlt := complementary_sum_span_lt_of_mem_erdos886Divisors n a b ε C hC ha hb
    push_cast
    linarith

/-- Any strictly increasing triple `d₁ < d₂ < d₃` in `Erdos886Divisors n ε C` with `C ≥ 0`
forces `2 < C^2 * n^(1/2 - 2 * ε)`. -/
theorem two_lt_sq_mul_rpow_of_three_mem_erdos886Divisors
    (n d₁ d₂ d₃ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    2 < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hm2.1 hm3.1 (le_of_lt hm2.2.1) hlt23
  have hstep : d₁ + n / d₁ + 2 ≤ d₃ + n / d₃ := by omega
  have hstepR : (2 : ℝ) ≤ ((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 2 : ℕ) : ℝ) ≤ ((d₃ + n / d₃ : ℕ) : ℝ) := by exact_mod_cast hstep
    push_cast at hcast
    linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₃ ε C hC hd₁ hd₃
  linarith

/-- Any strictly increasing quadruple `d₁ < d₂ < d₃ < d₄` in `Erdos886Divisors n ε C`
with `C ≥ 0` forces `3 < C^2 * n^(1/2 - 2 * ε)`. -/
theorem three_lt_sq_mul_rpow_of_four_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    3 < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hm2.1 hm3.1 (le_of_lt hm2.2.1) hlt23
  have hs34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hm3.1 hm4.1 (le_of_lt hm3.2.1) hlt34
  have hstep : d₁ + n / d₁ + 3 ≤ d₄ + n / d₄ := by omega
  have hstepR : (3 : ℝ) ≤ ((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 3 : ℕ) : ℝ) ≤ ((d₄ + n / d₄ : ℕ) : ℝ) := by exact_mod_cast hstep
    push_cast at hcast
    linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₄ ε C hC hd₁ hd₄
  linarith

/-- Explicit threshold for 4-tuples in the `1/6 ≤ ε` regime: if `d₁ < d₂ < d₃ < d₄` belong to
`Erdos886Divisors n ε 1` with `1 / 6 ≤ ε`, then `729 < n` (since `3^6 = 729`). -/
theorem gt_729_of_four_mem_erdos886Divisors_of_sixth_le
    (n d₁ d₂ d₃ d₄ : ℕ) (ε : ℝ) (hε : 1 / 6 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε 1)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε 1)
    (hd₄ : d₄ ∈ Erdos886Divisors n ε 1)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    729 < n := by
  have h3 := three_lt_sq_mul_rpow_of_four_mem_erdos886Divisors n d₁ d₂ d₃ d₄ ε 1 (by norm_num)
    hd₁ hd₂ hd₃ hd₄ hlt12 hlt23 hlt34
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁).1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h3_lt : (3 : ℝ) < (n : ℝ) ^ (1 / 6 : ℝ) := by linarith
  by_contra hle
  have hn_le : (n : ℝ) ≤ 729 := by
    have : n ≤ 729 := by omega
    exact_mod_cast this
  have hrpow_le : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (729 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by norm_num)
  have h729 : (729 : ℝ) ^ (1 / 6 : ℝ) = 3 := by
    have h_eq : (729 : ℝ) = (3 : ℝ) ^ (6 : ℝ) := by norm_num
    rw [h_eq, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith


/-! ## Section 10: Complementary Quotient Anti-Monotonicity and Minimum Divisor Spacing Above $n^{1/2}$ -/

/-- Exact product identity for complementary quotient differences of any two divisors of `n`:
`d₁ * d₂ * (n/d₁ - n/d₂) = n * (d₂ - d₁)`. -/
theorem complementary_quotient_diff_product_identity
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * ((n / d₁ : ℕ) - (n / d₂ : ℕ)) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) := by
  have hde₁ : (d₁ : ℝ) * (n / d₁ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₁).1
  have hde₂ : (d₂ : ℝ) * (n / d₂ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₂).1
  linear_combination (d₂ : ℝ) * hde₁ - (d₁ : ℝ) * hde₂

/-- Strict anti-monotonicity of the complementary quotient `d ↦ n / d` on `Nat.divisors n`:
whenever `d₁ < d₂` are divisors of `n`, `n / d₂ < n / d₁`. -/
theorem complementary_quotient_strict_anti_of_lt
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hlt : d₁ < d₂) :
    n / d₂ < n / d₁ := by
  have hid := complementary_quotient_diff_product_identity n d₁ d₂ hd₁ hd₂
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hltR : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt
  have hprod_pos : 0 < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) := by
    have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
    positivity
  have hd12_pos : 0 < (d₁ : ℝ) * (d₂ : ℝ) := by positivity
  have hdiff_pos : 0 < ((n / d₁ : ℕ) : ℝ) - ((n / d₂ : ℕ) : ℝ) := by nlinarith
  have hlt_q : ((n / d₂ : ℕ) : ℝ) < ((n / d₁ : ℕ) : ℝ) := by linarith
  exact_mod_cast hlt_q

/-- Exact decomposition of a divisor gap into the complementary-sum step plus the
complementary-quotient drop. -/
theorem divisor_diff_eq_complementary_sum_diff_add_quotient_diff
    (n d₁ d₂ : ℕ) :
    (d₂ : ℝ) - (d₁ : ℝ) =
      (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) +
        ((n / d₁ : ℕ) - (n / d₂ : ℕ)) := by
  ring

/-- For any two divisors `d₁ < d₂` of `n`, the complementary-sum change is strictly less
than the divisor gap: `(s₂ - s₁) + 1 ≤ d₂ - d₁`. -/
theorem complementary_sum_diff_lt_divisor_diff_of_lt
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hlt : d₁ < d₂) :
    (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 1 ≤
      (d₂ : ℝ) - (d₁ : ℝ) := by
  have hq : n / d₂ + 1 ≤ n / d₁ := complementary_quotient_strict_anti_of_lt n d₁ d₂ hd₁ hd₂ hlt
  have hqR : ((n / d₂ + 1 : ℕ) : ℝ) ≤ ((n / d₁ : ℕ) : ℝ) := by exact_mod_cast hq
  push_cast at hqR
  linarith

/-- Minimum spacing of `2` between any two divisors `n^(1/2) ≤ d₁ < d₂` of `n`:
since both `d + n/d` increases by at least `1` and `n/d` decreases by at least `1`,
`d₁ + 2 ≤ d₂`. -/
theorem divisor_step_two_of_ge_sqrt
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    d₁ + 2 ≤ d₂ := by
  have hsum : d₁ + n / d₁ + 1 ≤ d₂ + n / d₂ :=
    complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt
  have hquot : n / d₂ + 1 ≤ n / d₁ :=
    complementary_quotient_strict_anti_of_lt n d₁ d₂ hd₁ hd₂ hlt
  omega

/-- For any strictly increasing triple of divisors `n^(1/2) ≤ d₁ < d₂ < d₃` of `n`,
the Vandermonde product `(d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁)` is at least `16`. -/
theorem divisor_vandermonde_ge_sixteen_of_ge_sqrt
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    16 ≤ (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) := by
  have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) := by
    have hltR : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have h12 : d₁ + 2 ≤ d₂ := divisor_step_two_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have h23 : d₂ + 2 ≤ d₃ := divisor_step_two_of_ge_sqrt n d₂ d₃ hd₂ hd₃ hs₂ hlt23
  have hu : 2 ≤ d₂ - d₁ := by omega
  have hv : 2 ≤ d₃ - d₂ := by omega
  have hw : 4 ≤ d₃ - d₁ := by omega
  have huv : 4 ≤ (d₂ - d₁) * (d₃ - d₂) := by nlinarith
  nlinarith

/-- Sharp 8-fold improvement of `second_order_hyperbolic_gap_lower_bound_of_lt` for divisors
above `n^(1/2)`: the weighted second-order hyperbolic gap is at least `16`. -/
theorem second_order_hyperbolic_gap_ge_sixteen_of_ge_sqrt
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    ((d₃ : ℝ) - (d₂ : ℝ)) * (d₁ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 16 ≤
      ((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) := by
  have hid := second_order_hyperbolic_gap_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) := by
    have hltR : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have h12 : d₁ + 2 ≤ d₂ := divisor_step_two_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have h23 : d₂ + 2 ≤ d₃ := divisor_step_two_of_ge_sqrt n d₂ d₃ hd₂ hd₃ hs₂ hlt23
  have h13 : d₁ + 4 ≤ d₃ := by omega
  have h12R : (2 : ℝ) ≤ (d₂ : ℝ) - (d₁ : ℝ) := by
    have : ((d₁ + 2 : ℕ) : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast h12
    push_cast at this; linarith
  have h23R : (2 : ℝ) ≤ (d₃ : ℝ) - (d₂ : ℝ) := by
    have : ((d₂ + 2 : ℕ) : ℝ) ≤ (d₃ : ℝ) := by exact_mod_cast h23
    push_cast at this; linarith
  have h13R : (4 : ℝ) ≤ (d₃ : ℝ) - (d₁ : ℝ) := by
    have : ((d₁ + 4 : ℕ) : ℝ) ≤ (d₃ : ℝ) := by exact_mod_cast h13
    push_cast at this; linarith
  have hprod1 : (4 : ℝ) ≤ ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) := by nlinarith
  have hprod2 : (16 : ℝ) ≤ ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    nlinarith
  linarith

/-! ## Section 11: Unweighted $3 \times 3$ Hyperbolic Vandermonde Determinant & Strict Convexity -/

/-- Exact unweighted $3 \times 3$ hyperbolic Vandermonde determinant identity for any three
divisors `d₁, d₂, d₃ ∈ Nat.divisors n`:
`d₁ * d₂ * d₃ * ((d₂ - d₁)*(s₃ - s₂) - (d₃ - d₂)*(s₂ - s₁)) = n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁)`. -/
theorem unweighted_hyperbolic_vandermonde_triple_identity
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h23 := complementary_sum_diff_product_identity n d₂ d₃ hd₂ hd₃
  linear_combination (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * h23 - (d₃ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h12

/-- Left complementary-quotient representation of the unweighted $3 \times 3$ hyperbolic determinant:
`d₁ * Δ₁₂₃ = (d₂ - d₁) * (d₃ - d₁) * (n/d₂ - n/d₃)`. -/
theorem hyperbolic_vandermonde_quotient_left_identity
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    (d₁ : ℝ) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((n / d₂ : ℕ) - (n / d₃ : ℕ)) := by
  have hv := unweighted_hyperbolic_vandermonde_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  have hq := complementary_quotient_diff_product_identity n d₂ d₃ hd₂ hd₃
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hprod_ne : (d₂ : ℝ) * (d₃ : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hprod_ne
  linear_combination hv - ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * hq

/-- Right complementary-quotient representation of the unweighted $3 \times 3$ hyperbolic determinant:
`d₃ * Δ₁₂₃ = (d₃ - d₂) * (d₃ - d₁) * (n/d₁ - n/d₂)`. -/
theorem hyperbolic_vandermonde_quotient_right_identity
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    (d₃ : ℝ) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
      ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((n / d₁ : ℕ) - (n / d₂ : ℕ)) := by
  have hv := unweighted_hyperbolic_vandermonde_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  have hq := complementary_quotient_diff_product_identity n d₁ d₂ hd₁ hd₂
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hprod_ne : (d₁ : ℝ) * (d₂ : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hprod_ne
  linear_combination hv - ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * hq

/-- Division-free strict convexity of `d ↦ d + n / d` on `Nat.divisors n`:
for any strictly increasing triple `d₁ < d₂ < d₃` of divisors of `n`, the unweighted
hyperbolic determinant `(d₂ - d₁)*(s₃ - s₂) - (d₃ - d₂)*(s₂ - s₁)` is at least `1`. -/
theorem one_le_unweighted_hyperbolic_vandermonde_of_lt
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 1 ≤
      ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) := by
  have hv := unweighted_hyperbolic_vandermonde_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have h12R : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
  have h23R : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
  have hrhs_pos : 0 < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) - (d₂ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) - (d₁ : ℝ) := by linarith
    positivity
  have hdprod_pos : 0 < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) := by positivity
  set q₁ : ℕ := n / d₁
  set q₂ : ℕ := n / d₂
  set q₃ : ℕ := n / d₃
  set z : ℤ :=
    ((d₂ : ℤ) - (d₁ : ℤ)) * (((d₃ : ℤ) + (q₃ : ℤ)) - ((d₂ : ℤ) + (q₂ : ℤ))) -
      ((d₃ : ℤ) - (d₂ : ℤ)) * (((d₂ : ℤ) + (q₂ : ℤ)) - ((d₁ : ℤ) + (q₁ : ℤ)))
  have hz_eq :
      (z : ℝ) =
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (q₃ : ℝ)) - ((d₂ : ℝ) + (q₂ : ℝ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (q₂ : ℝ)) - ((d₁ : ℝ) + (q₁ : ℝ))) := by
    dsimp [z]
    push_cast
    ring
  have hzR_pos : (0 : ℝ) < (z : ℝ) := by
    have hv' :
        (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (z : ℝ) =
          (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
      rw [hz_eq]
      exact hv
    nlinarith
  have hz_pos : 0 < z := by exact_mod_cast hzR_pos
  have hz_ge : (1 : ℤ) ≤ z := hz_pos
  have hzR_ge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge
  linarith

/-- Whenever `n^(1/2) ≤ d₁ < d₂ < d₃` are divisors of `n` with non-decreasing divisor gaps
`d₂ - d₁ ≤ d₃ - d₂`, the complementary-sum steps are strictly increasing:
`(d₂ + n/d₂) - (d₁ + n/d₁) + 1 ≤ (d₃ + n/d₃) - (d₂ + n/d₂)`. -/
theorem complementary_sum_step_strict_mono_of_gap_le
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃)
    (hgap : d₂ - d₁ ≤ d₃ - d₂) :
    (d₂ + n / d₂) - (d₁ + n / d₁) + 1 ≤ (d₃ + n / d₃) - (d₂ + n / d₂) := by
  have hconv := one_le_unweighted_hyperbolic_vandermonde_of_lt n d₁ d₂ d₃ hd₁ hd₂ hd₃ hlt12 hlt23
  have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) := by
    have hltR : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hstep12 : d₁ + n / d₁ + 1 ≤ d₂ + n / d₂ :=
    complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have hstep23 : d₂ + n / d₂ + 1 ≤ d₃ + n / d₃ :=
    complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hd₂ hd₃ hs₂ hlt23
  have hgapR : (d₂ : ℝ) - (d₁ : ℝ) ≤ (d₃ : ℝ) - (d₂ : ℝ) := by
    have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
    have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
    have hcast : ((d₂ - d₁ : ℕ) : ℝ) ≤ ((d₃ - d₂ : ℕ) : ℝ) := by exact_mod_cast hgap
    rw [Nat.cast_sub hle12, Nat.cast_sub hle23] at hcast
    exact hcast
  have h12_pos : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hs12_nonneg : 0 ≤ ((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 1 : ℕ) : ℝ) ≤ ((d₂ + n / d₂ : ℕ) : ℝ) := by exact_mod_cast hstep12
    push_cast at hcast
    linarith
  have hlt_stepR :
      ((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) <
        ((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)) := by
    nlinarith
  have hle_s12 : d₁ + n / d₁ ≤ d₂ + n / d₂ := by omega
  have hle_s23 : d₂ + n / d₂ ≤ d₃ + n / d₃ := by omega
  have hlt_natR : (((d₂ + n / d₂) - (d₁ + n / d₁) : ℕ) : ℝ) < (((d₃ + n / d₃) - (d₂ + n / d₂) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle_s12, Nat.cast_sub hle_s23]
    push_cast
    linarith
  have hlt_nat : (d₂ + n / d₂) - (d₁ + n / d₁) < (d₃ + n / d₃) - (d₂ + n / d₂) := by
    exact_mod_cast hlt_natR
  omega

/-- Conversely, if `d₁ < d₂ < d₃` are divisors of `n` with minimal complementary-sum steps
`d₂ + n/d₂ = d₁ + n/d₁ + 1` and `d₃ + n/d₃ = d₂ + n/d₂ + 1` (total span `2`), then their
divisor gaps must be strictly concave: `d₃ - d₂ + 1 ≤ d₂ - d₁`. -/
theorem divisor_gap_strict_concave_of_minimal_sum_steps
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃)
    (hstep12 : d₂ + n / d₂ = d₁ + n / d₁ + 1)
    (hstep23 : d₃ + n / d₃ = d₂ + n / d₂ + 1) :
    d₃ - d₂ + 1 ≤ d₂ - d₁ := by
  have hconv := one_le_unweighted_hyperbolic_vandermonde_of_lt n d₁ d₂ d₃ hd₁ hd₂ hd₃ hlt12 hlt23
  have hs12R : ((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) = 1 := by
    have hcast : ((d₂ + n / d₂ : ℕ) : ℝ) = ((d₁ + n / d₁ + 1 : ℕ) : ℝ) := by exact_mod_cast hstep12
    push_cast at hcast
    linarith
  have hs23R : ((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)) = 1 := by
    have hcast : ((d₃ + n / d₃ : ℕ) : ℝ) = ((d₂ + n / d₂ + 1 : ℕ) : ℝ) := by exact_mod_cast hstep23
    push_cast at hcast
    linarith
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
  have hgapR : ((d₃ - d₂ + 1 : ℕ) : ℝ) ≤ ((d₂ - d₁ : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hle23, Nat.cast_sub hle12]
    nlinarith
  exact_mod_cast hgapR

/-! ## Section 12: Combining Hyperbolic Vandermonde Determinants with Ruzsa Span Bounds -/

/-- Exact decomposition of the Ruzsa complementary-sum span `s₃ - s₁` into the unweighted
$3 \times 3$ hyperbolic determinant plus `(d₃ - d₁) * (s₂ - s₁)`. -/
theorem ruzsa_span_vandermonde_decomposition
    (n d₁ d₂ d₃ : ℕ) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      ((d₃ : ℝ) - (d₁ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
  ring

/-- Exact factored identity for the weighted Ruzsa complementary-sum span `(d₂ - d₁) * d₃ * (s₃ - s₁)`:
every term factors through the outer divisor span `d₃ - d₁`. -/
theorem weighted_ruzsa_span_identity
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * (d₃ : ℝ) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      ((d₃ : ℝ) - (d₁ : ℝ)) *
        ((d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) +
          ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ))) := by
  have hid := second_order_hyperbolic_gap_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  linear_combination hid

/-- Universal divisor-triple product bound: for any three divisors `d₁ < d₂ < d₃` of `n`,
`d₁ * d₂ * d₃ ≤ n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁)`. -/
theorem triple_product_le_mul_vandermonde_of_lt
    (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    d₁ * d₂ * d₃ ≤ n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) := by
  have hv := unweighted_hyperbolic_vandermonde_triple_identity n d₁ d₂ d₃ hd₁ hd₂ hd₃
  have h1 := one_le_unweighted_hyperbolic_vandermonde_of_lt n d₁ d₂ d₃ hd₁ hd₂ hd₃ hlt12 hlt23
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hdprod_nonneg : 0 ≤ (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) := by positivity
  have hleR :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) ≤
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    nlinarith
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
  have hle13 : d₁ ≤ d₃ := le_of_lt (lt_trans hlt12 hlt23)
  have hcast :
      ((d₁ * d₂ * d₃ : ℕ) : ℝ) ≤
        ((n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle23, Nat.cast_sub hle13]
    linarith
  exact_mod_cast hcast

/-- For any strictly increasing triple `d₁ < d₂ < d₃` in `Erdos886Divisors n ε C`, the
Vandermonde product of divisor gaps strictly exceeds `n^(1/2)`:
`n^(1/2) < (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁)`. -/
theorem sqrt_lt_vandermonde_of_three_mem_erdos886Divisors
    (n d₁ d₂ d₃ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    (n : ℝ) ^ (1 / 2 : ℝ) < ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hprod := triple_product_le_mul_vandermonde_of_lt n d₁ d₂ d₃ hm1.1 hm2.1 hm3.1 hlt12 hlt23
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
  have hle13 : d₁ ≤ d₃ := le_of_lt (lt_trans hlt12 hlt23)
  have hprodR :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) ≤
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    have hcast : ((d₁ * d₂ * d₃ : ℕ) : ℝ) ≤ ((n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) : ℕ) : ℝ) := by
      exact_mod_cast hprod
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle23, Nat.cast_sub hle13] at hcast
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hs_pos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have h1 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₁ : ℝ) := hm1.2.1
  have h2 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₂ : ℝ) := hm2.2.1
  have h3 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₃ : ℝ) := hm3.2.1
  have h12_gt : (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith
  have h123_gt : (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) := by nlinarith
  nlinarith

/-- AM-GM outer-span bound for any triple `d₁ < d₂ < d₃` in `Erdos886Divisors n ε C`:
`4 * n^(1/2) < (d₃ - d₁)^3`. -/
theorem four_mul_sqrt_lt_span_cube_of_three_mem_erdos886Divisors
    (n d₁ d₂ d₃ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    4 * (n : ℝ) ^ (1 / 2 : ℝ) < ((d₃ : ℝ) - (d₁ : ℝ)) ^ 3 := by
  have hv := sqrt_lt_vandermonde_of_three_mem_erdos886Divisors n d₁ d₂ d₃ ε C hd₁ hd₂ hd₃ hlt12 hlt23
  have h13R : 0 < (d₃ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) < (d₃ : ℝ) := by exact_mod_cast (lt_trans hlt12 hlt23)
    linarith
  have hamgm :
      4 * (((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ))) ≤ ((d₃ : ℝ) - (d₁ : ℝ)) ^ 2 := by
    have hsq : 0 ≤ (((d₂ : ℝ) - (d₁ : ℝ)) - ((d₃ : ℝ) - (d₂ : ℝ))) ^ 2 := sq_nonneg _
    linarith
  nlinarith

/-- Combining the unweighted $3 \times 3$ hyperbolic determinant with the Ruzsa complementary-sum
span bound: for any `d₁ < d₂ < d₃` in `Erdos886Divisors n ε C` with `C ≥ 0`,
`Δ₁₂₃ + (d₃ - d₁) < (d₂ - d₁) * C^2 * n^(1/2 - 2*ε)`. -/
theorem unweighted_vandermonde_add_span_lt_of_three_mem_erdos886Divisors
    (n d₁ d₂ d₃ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) :
    (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
      ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      ((d₃ : ℝ) - (d₁ : ℝ)) <
      ((d₂ : ℝ) - (d₁ : ℝ)) * C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hdecomp := ruzsa_span_vandermonde_decomposition n d₁ d₂ d₃
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hs12 : d₁ + n / d₁ + 1 ≤ d₂ + n / d₂ :=
    complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs12R : (1 : ℝ) ≤ ((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 1 : ℕ) : ℝ) ≤ ((d₂ + n / d₂ : ℕ) : ℝ) := by exact_mod_cast hs12
    push_cast at hcast
    linarith
  have h13_nonneg : 0 ≤ (d₃ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) < (d₃ : ℝ) := by exact_mod_cast (lt_trans hlt12 hlt23)
    linarith
  have h12_pos : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₃ ε C hC hd₁ hd₃
  nlinarith

/-- Combining the unweighted $3 \times 3$ hyperbolic determinant with the Ruzsa span inequality:
any triple `d₁ < d₂ < d₃` in `Erdos886Divisors n ε C` (`C ≥ 0`) with non-decreasing divisor gaps
`d₂ - d₁ ≤ d₃ - d₂` forces `3 < C^2 * n^(1/2 - 2 * ε)` (strengthening `2 < C^2 * n^(1/2 - 2 * ε)`). -/
theorem three_lt_sq_mul_rpow_of_three_mem_erdos886Divisors_of_gap_le
    (n d₁ d₂ d₃ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃)
    (hgap : d₂ - d₁ ≤ d₃ - d₂) :
    3 < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hs12 : d₁ + n / d₁ + 1 ≤ d₂ + n / d₂ :=
    complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hstep := complementary_sum_step_strict_mono_of_gap_le n d₁ d₂ d₃ hm1.1 hm2.1 hm3.1
    (le_of_lt hm1.2.1) hlt12 hlt23 hgap
  have hs13 : d₁ + n / d₁ + 3 ≤ d₃ + n / d₃ := by omega
  have hs13R : (3 : ℝ) ≤ ((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 3 : ℕ) : ℝ) ≤ ((d₃ + n / d₃ : ℕ) : ℝ) := by exact_mod_cast hs13
    push_cast at hcast
    linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₃ ε C hC hd₁ hd₃
  linarith

/-- Explicit threshold for convex-gap triples at `1/6 ≤ ε`: if `d₁ < d₂ < d₃` belong to
`Erdos886Divisors n ε 1` with `1 / 6 ≤ ε` and `d₂ - d₁ ≤ d₃ - d₂`, then `729 < n`. -/
theorem gt_729_of_three_mem_erdos886Divisors_of_sixth_le_of_gap_le
    (n d₁ d₂ d₃ : ℕ) (ε : ℝ) (hε : 1 / 6 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε 1)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε 1)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃)
    (hgap : d₂ - d₁ ≤ d₃ - d₂) :
    729 < n := by
  have h3 := three_lt_sq_mul_rpow_of_three_mem_erdos886Divisors_of_gap_le n d₁ d₂ d₃ ε 1
    (by norm_num) hd₁ hd₂ hd₃ hlt12 hlt23 hgap
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁).1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h3_lt : (3 : ℝ) < (n : ℝ) ^ (1 / 6 : ℝ) := by linarith
  by_contra hle
  have hn_le : (n : ℝ) ≤ 729 := by
    have : n ≤ 729 := by omega
    exact_mod_cast this
  have hrpow_le : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (729 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by norm_num)
  have h729 : (729 : ℝ) ^ (1 / 6 : ℝ) = 3 := by
    have h_eq : (729 : ℝ) = (3 : ℝ) ^ (6 : ℝ) := by norm_num
    rw [h_eq, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-! ## Section 13: Unweighted 4-Divisor Bambah–Chowla Determinant & Sharp Ruzsa Cardinality Thresholds -/

/-- Exact unweighted 4-divisor Bambah–Chowla determinant identity for any four divisors
`d₁, d₂, d₃, d₄ ∈ Nat.divisors n`:
`d₁ * d₂ * d₃ * d₄ * ((d₂ - d₁)*(s₄ - s₃) - (d₄ - d₃)*(s₂ - s₁)) = n * (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂)`. -/
theorem unweighted_bambah_chowla_quadruple_identity
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₃ : ℝ) * (d₄ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h34 := complementary_sum_diff_product_identity n d₃ d₄ hd₃ hd₄
  linear_combination (d₁ : ℝ) * (d₂ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * h34 -
    (d₃ : ℝ) * (d₄ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * h12

/-- Exact combination identity eliminating the middle step `s₃ - s₂` between the adjacent
$3 \times 3$ hyperbolic determinants `Δ₁₂₃` and `Δ₂₃₄` to yield `(d₃ - d₂) * Δ₁₂₃₄`. -/
theorem bambah_chowla_determinant_combination_identity
    (n d₁ d₂ d₃ d₄ : ℕ) :
    ((d₃ : ℝ) - (d₂ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
    ((d₂ : ℝ) - (d₁ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) +
    ((d₄ : ℝ) - (d₃ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) := by
  ring

/-- For any strictly increasing quadruple `d₁ < d₂ < d₃ < d₄` of divisors of `n`, the
unweighted Bambah–Chowla determinant `(d₂ - d₁)*(s₄ - s₃) - (d₄ - d₃)*(s₂ - s₁)` is at least `1`. -/
theorem one_le_unweighted_bambah_chowla_of_lt
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 1 ≤
      ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) := by
  have h123 := one_le_unweighted_hyperbolic_vandermonde_of_lt n d₁ d₂ d₃ hd₁ hd₂ hd₃ hlt12 hlt23
  have h234 := one_le_unweighted_hyperbolic_vandermonde_of_lt n d₂ d₃ d₄ hd₂ hd₃ hd₄ hlt23 hlt34
  have h12_pos : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have h23_pos : 0 < (d₃ : ℝ) - (d₂ : ℝ) := by
    have : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
    linarith
  have h34_pos : 0 < (d₄ : ℝ) - (d₃ : ℝ) := by
    have : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
    linarith
  have hcomb := bambah_chowla_determinant_combination_identity n d₁ d₂ d₃ d₄
  set q₁ : ℕ := n / d₁
  set q₂ : ℕ := n / d₂
  set q₃ : ℕ := n / d₃
  set q₄ : ℕ := n / d₄
  set z : ℤ :=
    ((d₂ : ℤ) - (d₁ : ℤ)) * (((d₄ : ℤ) + (q₄ : ℤ)) - ((d₃ : ℤ) + (q₃ : ℤ))) -
      ((d₄ : ℤ) - (d₃ : ℤ)) * (((d₂ : ℤ) + (q₂ : ℤ)) - ((d₁ : ℤ) + (q₁ : ℤ)))
  have hz_eq :
      (z : ℝ) =
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₄ : ℝ) + (q₄ : ℝ)) - ((d₃ : ℝ) + (q₃ : ℝ))) -
          ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₂ : ℝ) + (q₂ : ℝ)) - ((d₁ : ℝ) + (q₁ : ℝ))) := by
    dsimp [z]
    push_cast
    ring
  have hzR_pos : (0 : ℝ) < (z : ℝ) := by
    have hcomb' :
        ((d₃ : ℝ) - (d₂ : ℝ)) * (z : ℝ) =
          ((d₂ : ℝ) - (d₁ : ℝ)) *
            (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (q₄ : ℝ)) - ((d₃ : ℝ) + (q₃ : ℝ))) -
              ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (q₃ : ℝ)) - ((d₂ : ℝ) + (q₂ : ℝ)))) +
          ((d₄ : ℝ) - (d₃ : ℝ)) *
            (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (q₃ : ℝ)) - ((d₂ : ℝ) + (q₂ : ℝ))) -
              ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (q₂ : ℝ)) - ((d₁ : ℝ) + (q₁ : ℝ)))) := by
      rw [hz_eq]
      exact hcomb
    nlinarith
  have hz_pos : 0 < z := by exact_mod_cast hzR_pos
  have hz_ge : (1 : ℤ) ≤ z := hz_pos
  have hzR_ge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge
  linarith

/-- Universal 4-divisor product bound: for any four divisors `d₁ < d₂ < d₃ < d₄` of `n`,
`d₁ * d₂ * d₃ * d₄ ≤ n * (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂)`. -/
theorem quadruple_product_le_mul_bambah_chowla_of_lt
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    d₁ * d₂ * d₃ * d₄ ≤ n * (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂) := by
  have hbc := unweighted_bambah_chowla_quadruple_identity n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄
  have h1 := one_le_unweighted_bambah_chowla_of_lt n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄ hlt12 hlt23 hlt34
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have hdprod_nonneg : 0 ≤ (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) := by positivity
  have hleR :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) ≤
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₃ : ℝ) * (d₄ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
    nlinarith
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle34 : d₃ ≤ d₄ := le_of_lt hlt34
  have hle_prod : d₁ * d₂ ≤ d₃ * d₄ := Nat.mul_le_mul (le_of_lt (lt_trans hlt12 hlt23)) (le_of_lt (lt_trans hlt23 hlt34))
  have hcast :
      ((d₁ * d₂ * d₃ * d₄ : ℕ) : ℝ) ≤
        ((n * (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle34, Nat.cast_sub hle_prod]
    linarith
  exact_mod_cast hcast

/-- For any strictly increasing quadruple `d₁ < d₂ < d₃ < d₄` in `Erdos886Divisors n ε C`,
the Bambah–Chowla gap product strictly exceeds `n`:
`n < (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂)`. -/
theorem lt_bambah_chowla_gap_product_of_four_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C)
    (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C)
    (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    n < (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hprod := quadruple_product_le_mul_bambah_chowla_of_lt n d₁ d₂ d₃ d₄ hm1.1 hm2.1 hm3.1 hm4.1 hlt12 hlt23 hlt34
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle34 : d₃ ≤ d₄ := le_of_lt hlt34
  have hle_prod : d₁ * d₂ ≤ d₃ * d₄ := Nat.mul_le_mul (le_of_lt (lt_trans hlt12 hlt23)) (le_of_lt (lt_trans hlt23 hlt34))
  have hprodR :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) ≤
        (n : ℝ) * (((d₂ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₃ : ℝ) * (d₄ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ))) := by
    have hcast :
        ((d₁ * d₂ * d₃ * d₄ : ℕ) : ℝ) ≤
          ((n * (d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂) : ℕ) : ℝ) := by
      exact_mod_cast hprod
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle34, Nat.cast_sub hle_prod] at hcast
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hs_pos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have h1 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₁ : ℝ) := hm1.2.1
  have h2 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₂ : ℝ) := hm2.2.1
  have h3 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₃ : ℝ) := hm3.2.1
  have h4 : (n : ℝ) ^ (1 / 2 : ℝ) < (d₄ : ℝ) := hm4.2.1
  have h12_gt : (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith
  have h34_gt : (n : ℝ) < (d₃ : ℝ) * (d₄ : ℝ) := by nlinarith
  have h1234_gt : (n : ℝ) * (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) := by nlinarith
  have hltR : (n : ℝ) < ((d₂ - d₁) * (d₄ - d₃) * (d₃ * d₄ - d₁ * d₂) : ℕ) := by
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle34, Nat.cast_sub hle_prod]
    nlinarith
  exact_mod_cast hltR

/-- Strict Ruzsa cardinality inequality whenever `Erdos886Divisors n ε C` is nonempty and `C ≥ 0`:
`((Erdos886Divisors n ε C).card : ℝ) < 1 + C^2 * n^(1/2 - 2 * ε)`. -/
theorem card_erdos886Divisors_lt_one_add_sq_mul_rpow_of_nonempty
    (n : ℕ) (ε C : ℝ) (hC : 0 ≤ C) (hne : (Erdos886Divisors n ε C).Nonempty) :
    ((Erdos886Divisors n ε C).card : ℝ) < 1 + C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  set s := Erdos886Divisors n ε C
  let f : ℕ → ℕ := fun d => d + n / d
  have hmono : ∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b := by
    intro a ha b hb hlt
    have ha_mem := (mem_erdos886Divisors_iff n a ε C).mp ha
    have hb_mem := (mem_erdos886Divisors_iff n b ε C).mp hb
    exact complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt
  have hmin_mem : s.min' hne ∈ s := Finset.min'_mem s hne
  have hmax_mem : s.max' hne ∈ s := Finset.max'_mem s hne
  have hle_Elem : ∀ x ∈ s, f (s.min' hne) ≤ f x ∧ f x ≤ f (s.max' hne) := by
    intro x hx
    constructor
    · rcases lt_or_eq_of_le (Finset.min'_le s x hx) with hlt | heq
      · exact le_of_lt (hmono _ hmin_mem _ hx hlt)
      · rw [heq]
    · rcases lt_or_eq_of_le (Finset.le_max' s x hx) with hlt | heq
      · exact le_of_lt (hmono _ hx _ hmax_mem hlt)
      · rw [heq]
  have hle_span :
      (s.card : ℝ) ≤ 1 + ((f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ)) := by
    apply card_nat_finset_le_of_strictMonoOn_image_diff s f hmono
      ((f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ))
    · have h1 : (f (s.min' hne) : ℝ) ≤ (f (s.max' hne) : ℝ) := by
        exact_mod_cast (hle_Elem (s.max' hne) hmax_mem).1
      linarith
    · intro a ha b hb
      have ha_le : (f (s.min' hne) : ℝ) ≤ (f a : ℝ) := by exact_mod_cast (hle_Elem a ha).1
      have hb_le : (f b : ℝ) ≤ (f (s.max' hne) : ℝ) := by exact_mod_cast (hle_Elem b hb).2
      linarith
  have hlt_span :
      (f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ) < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
    have h := complementary_sum_span_lt_of_mem_erdos886Divisors n (s.min' hne) (s.max' hne) ε C hC hmin_mem hmax_mem
    dsimp [f]
    push_cast
    linarith
  linarith

/-- Sharp integer cardinality bound from the strict Ruzsa span inequality: whenever `0 ≤ C` and
`C^2 * n^(1/2 - 2 * ε) ≤ k` for `k : ℕ`, `(Erdos886Divisors n ε C).card ≤ k`. -/
theorem card_erdos886Divisors_le_nat_of_sq_mul_rpow_le
    (n k : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hle : C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (k : ℝ)) :
    (Erdos886Divisors n ε C).card ≤ k := by
  by_cases hne : (Erdos886Divisors n ε C).Nonempty
  · have hlt := card_erdos886Divisors_lt_one_add_sq_mul_rpow_of_nonempty n ε C hC hne
    have hlt_k : ((Erdos886Divisors n ε C).card : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hlt_nat : (Erdos886Divisors n ε C).card < k + 1 := by exact_mod_cast hlt_k
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le k

/-- Negative control / sharp finite threshold at `1/6 ≤ ε`: for all `n ≤ 64` and `1/6 ≤ ε`,
`(Erdos886Divisors n ε 1).card ≤ 2`. -/
theorem card_erdos886Divisors_le_two_of_le_64_of_sixth_le
    (n : ℕ) (hn : n ≤ 64) (ε : ℝ) (hε : 1 / 6 ≤ ε) :
    (Erdos886Divisors n ε 1).card ≤ 2 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [erdos886Divisors_zero]
  · apply card_erdos886Divisors_le_nat_of_sq_mul_rpow_le n 2 ε 1 (by norm_num)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hn64 : (n : ℝ) ≤ 64 := by exact_mod_cast hn
    have hrpow64 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (64 : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hn64 (by norm_num)
    have h64 : (64 : ℝ) ^ (1 / 6 : ℝ) = 2 := by
      have h_eq : (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) := by norm_num
      rw [h_eq, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith

/-- Negative control / sharp finite threshold at `1/6 ≤ ε`: for all `n ≤ 729` and `1/6 ≤ ε`,
`(Erdos886Divisors n ε 1).card ≤ 3`. -/
theorem card_erdos886Divisors_le_three_of_le_729_of_sixth_le
    (n : ℕ) (hn : n ≤ 729) (ε : ℝ) (hε : 1 / 6 ≤ ε) :
    (Erdos886Divisors n ε 1).card ≤ 3 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [erdos886Divisors_zero]
  · apply card_erdos886Divisors_le_nat_of_sq_mul_rpow_le n 3 ε 1 (by norm_num)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hn729 : (n : ℝ) ≤ 729 := by exact_mod_cast hn
    have hrpow729 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (729 : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hn729 (by norm_num)
    have h729 : (729 : ℝ) ^ (1 / 6 : ℝ) = 3 := by
      have h_eq : (729 : ℝ) = (3 : ℝ) ^ (6 : ℝ) := by norm_num
      rw [h_eq, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith

/-- Positive control: at `n = 1260` (the first 3-divisor witness at `ε = 1/6, C = 1`, with
divisors `d₁ = 36, d₂ = 42, d₃ = 45` and complementary sums `71, 72, 73`), the unweighted
$3 \times 3$ hyperbolic Vandermonde determinant equals `3` and satisfies
`36 * 42 * 45 * 3 = 1260 * (42 - 36) * (45 - 42) * (45 - 36)`. -/
theorem positive_control_witness_1260_vandermonde :
    (36 : ℝ) * (42 : ℝ) * (45 : ℝ) *
      (((42 : ℝ) - (36 : ℝ)) * (((45 : ℝ) + (1260 / 45 : ℕ)) - ((42 : ℝ) + (1260 / 42 : ℕ))) -
        ((45 : ℝ) - (42 : ℝ)) * (((42 : ℝ) + (1260 / 42 : ℕ)) - ((36 : ℝ) + (1260 / 36 : ℕ)))) =
      (1260 : ℝ) * ((42 : ℝ) - (36 : ℝ)) * ((45 : ℝ) - (42 : ℝ)) * ((45 : ℝ) - (36 : ℝ)) ∧
    (((42 : ℝ) - (36 : ℝ)) * (((45 : ℝ) + (1260 / 45 : ℕ)) - ((42 : ℝ) + (1260 / 42 : ℕ))) -
      ((45 : ℝ) - (42 : ℝ)) * (((42 : ℝ) + (1260 / 42 : ℕ)) - ((36 : ℝ) + (1260 / 36 : ℕ)))) = 3 := by
  constructor
  · exact unweighted_hyperbolic_vandermonde_triple_identity 1260 36 42 45 (by decide) (by decide) (by decide)
  · norm_num


/-! ## Section 14: Third- and Fourth-Order Unweighted Hyperbolic Vandermonde Determinants -/

/-- Exact unweighted third-order hyperbolic Vandermonde determinant identity on 4 divisors:
`d₁*d₂*d₃*d₄ * ((d₄-d₃)*(d₄-d₂)*Δ₁₂₃ - (d₂-d₁)*(d₃-d₁)*Δ₂₃₄) = n * V₄(d₁,d₂,d₃,d₄)`. -/
theorem third_order_hyperbolic_vandermonde_quadruple_identity
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
          ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h23 := complementary_sum_diff_product_identity n d₂ d₃ hd₂ hd₃
  have h34 := complementary_sum_diff_product_identity n d₃ d₄ hd₃ hd₄
  have hv123 :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    linear_combination (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * h23 - (d₃ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h12
  have hv234 :
      (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) *
        (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
          ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) =
        (n : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) := by
    linear_combination (d₂ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h34 - (d₄ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * h23
  linear_combination
    (d₄ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * hv123 -
      (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * hv234

/-- Division-free strict decrease of normalized second divided differences on `Nat.divisors n`:
for any `d₁ < d₂ < d₃ < d₄` dividing `n`, the unweighted third-order determinant is at least `1`. -/
theorem one_le_third_order_hyperbolic_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) + 1 ≤
    ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) := by
  have hv := third_order_hyperbolic_vandermonde_quadruple_identity n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have h12R : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
  have h23R : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
  have h34R : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
  have hrhs_pos :
      0 < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) := by
    have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) - (d₂ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₃ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₂ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₁ : ℝ) := by linarith
    positivity
  have hdprod_pos : 0 < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) := by positivity
  set q₁ : ℕ := n / d₁
  set q₂ : ℕ := n / d₂
  set q₃ : ℕ := n / d₃
  set q₄ : ℕ := n / d₄
  set z : ℤ :=
    ((d₄ : ℤ) - (d₃ : ℤ)) * ((d₄ : ℤ) - (d₂ : ℤ)) *
      (((d₂ : ℤ) - (d₁ : ℤ)) * (((d₃ : ℤ) + (q₃ : ℤ)) - ((d₂ : ℤ) + (q₂ : ℤ))) -
        ((d₃ : ℤ) - (d₂ : ℤ)) * (((d₂ : ℤ) + (q₂ : ℤ)) - ((d₁ : ℤ) + (q₁ : ℤ)))) -
    ((d₂ : ℤ) - (d₁ : ℤ)) * ((d₃ : ℤ) - (d₁ : ℤ)) *
      (((d₃ : ℤ) - (d₂ : ℤ)) * (((d₄ : ℤ) + (q₄ : ℤ)) - ((d₃ : ℤ) + (q₃ : ℤ))) -
        ((d₄ : ℤ) - (d₃ : ℤ)) * (((d₃ : ℤ) + (q₃ : ℤ)) - ((d₂ : ℤ) + (q₂ : ℤ))))
  have hz_eq :
      (z : ℝ) =
        ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
          (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (q₃ : ℝ)) - ((d₂ : ℝ) + (q₂ : ℝ))) -
            ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (q₂ : ℝ)) - ((d₁ : ℝ) + (q₁ : ℝ)))) -
        ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
          (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (q₄ : ℝ)) - ((d₃ : ℝ) + (q₃ : ℝ))) -
            ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (q₃ : ℝ)) - ((d₂ : ℝ) + (q₂ : ℝ)))) := by
    dsimp [z]; push_cast; ring
  have hv_z :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (z : ℝ) =
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
          ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) := by
    rw [hz_eq]; exact hv
  have hzR_pos : (0 : ℝ) < (z : ℝ) :=
    (mul_pos_iff_of_pos_left hdprod_pos).mp (hv_z.symm ▸ hrhs_pos)
  have hz_pos : 0 < z := by exact_mod_cast hzR_pos
  have hz_ge : (1 : ℤ) ≤ z := hz_pos
  have hzR_ge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge
  linarith [hz_eq, hzR_ge]

/-- Universal 4-divisor product bound against the full 6-factor Vandermonde product:
`d₁*d₂*d₃*d₄ ≤ n*(d₂-d₁)*(d₃-d₂)*(d₄-d₃)*(d₃-d₁)*(d₄-d₂)*(d₄-d₁)`. -/
theorem quadruple_product_le_mul_full_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    d₁ * d₂ * d₃ * d₄ ≤
      n * (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₃ - d₁) * (d₄ - d₂) * (d₄ - d₁) := by
  have hv := third_order_hyperbolic_vandermonde_quadruple_identity n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄
  have h1 := one_le_third_order_hyperbolic_vandermonde_of_lt n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄
    hlt12 hlt23 hlt34
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have hdprod_nonneg : 0 ≤ (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) := by positivity
  set Δ3 : ℝ :=
    ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))))
  have hΔ3_ge : 1 ≤ Δ3 := by dsimp [Δ3]; linarith [h1]
  have hmul_le :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * 1 ≤
        (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * Δ3 :=
    mul_le_mul_of_nonneg_left hΔ3_ge hdprod_nonneg
  have hleR :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) ≤
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
          ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) := by
    linarith [hmul_le, hv]
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
  have hle34 : d₃ ≤ d₄ := le_of_lt hlt34
  have hle13 : d₁ ≤ d₃ := le_trans hle12 hle23
  have hle24 : d₂ ≤ d₄ := le_trans hle23 hle34
  have hle14 : d₁ ≤ d₄ := le_trans hle13 hle34
  have hcast :
      ((d₁ * d₂ * d₃ * d₄ : ℕ) : ℝ) ≤
        ((n * (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₃ - d₁) * (d₄ - d₂) * (d₄ - d₁) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle23, Nat.cast_sub hle34,
      Nat.cast_sub hle13, Nat.cast_sub hle24, Nat.cast_sub hle14]
    exact hleR
  exact_mod_cast hcast

/-- For any quadruple `d₁ < d₂ < d₃ < d₄` in `Erdos886Divisors n ε C`, the full 6-factor
Vandermonde product strictly exceeds `n`. -/
theorem lt_full_vandermonde_of_four_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) :
    n < (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₃ - d₁) * (d₄ - d₂) * (d₄ - d₁) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hprod := quadruple_product_le_mul_full_vandermonde_of_lt n d₁ d₂ d₃ d₄
    hm1.1 hm2.1 hm3.1 hm4.1 hlt12 hlt23 hlt34
  set V4 : ℕ := (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₃ - d₁) * (d₄ - d₂) * (d₄ - d₁)
  have hprod_assoc : d₁ * d₂ * d₃ * d₄ ≤ n * V4 := by
    dsimp [V4]; simpa [Nat.mul_assoc] using hprod
  have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hs_pos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have h12_gt : (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith [hm1.2.1, hm2.2.1]
  have h34_gt : (n : ℝ) < (d₃ : ℝ) * (d₄ : ℝ) := by nlinarith [hm3.2.1, hm4.2.1]
  have h1234_gtR : ((n * n : ℕ) : ℝ) < ((d₁ * d₂ * d₃ * d₄ : ℕ) : ℝ) := by
    push_cast; nlinarith [h12_gt, h34_gt]
  have h1234_gt : n * n < d₁ * d₂ * d₃ * d₄ := by exact_mod_cast h1234_gtR
  have hmul_lt : n * n < n * V4 := lt_of_lt_of_le h1234_gt hprod_assoc
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

/-- Exact three-term decomposition of the outer 5-tuple Bambah–Chowla determinant `Δ₁₂₄₅`
into the three adjacent $3 \times 3$ hyperbolic Vandermonde determinants `Δ₁₂₃, Δ₂₃₄, Δ₃₄₅`. -/
theorem five_tuple_outer_bambah_chowla_three_term_decomposition
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) :
    ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))) +
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) +
    ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) := by
  ring

/-- Exact coupled $3 \times 3$ hyperbolic Vandermonde determinant identity across a 5-tuple
of divisors `d₁, d₂, d₃, d₄, d₅ ∈ Nat.divisors n` sharing the pivot `d₃`. -/
theorem five_tuple_coupled_vandermonde_identity
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
          ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
        ((d₄ : ℝ) * (d₅ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h23 := complementary_sum_diff_product_identity n d₂ d₃ hd₂ hd₃
  have h34 := complementary_sum_diff_product_identity n d₃ d₄ hd₃ hd₄
  have h45 := complementary_sum_diff_product_identity n d₄ d₅ hd₄ hd₅
  have hv123 :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    linear_combination (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * h23 - (d₃ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h12
  have hv345 :
      (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) *
        (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
          ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))) =
        (n : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) := by
    linear_combination (d₃ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * h45 - (d₅ : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * h34
  linear_combination
    (d₄ : ℝ) * (d₅ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * hv123 -
      (d₁ : ℝ) * (d₂ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * hv345

/-- For any strictly increasing 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` of divisors of `n`,
the coupled $3 \times 3$ hyperbolic Vandermonde determinant is at least `1`. -/
theorem one_le_five_tuple_coupled_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))) + 1 ≤
    ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) := by
  have hv := five_tuple_coupled_vandermonde_identity n d₁ d₂ d₃ d₄ d₅ hd₁ hd₂ hd₃ hd₄ hd₅
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have hd₅_pos : (0 : ℝ) < (d₅ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₅
  have h12R : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
  have h23R : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
  have h34R : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
  have h45R : (d₄ : ℝ) < (d₅ : ℝ) := by exact_mod_cast hlt45
  have hrhs_pos :
      0 < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
        ((d₄ : ℝ) * (d₅ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
    have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) - (d₂ : ℝ) := by linarith
    have : 0 < (d₃ : ℝ) - (d₁ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₃ : ℝ) := by linarith
    have : 0 < (d₅ : ℝ) - (d₄ : ℝ) := by linarith
    have : 0 < (d₅ : ℝ) - (d₃ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) * (d₅ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith
    positivity
  have hdprod_pos : 0 < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) := by positivity
  set q₁ : ℕ := n / d₁
  set q₂ : ℕ := n / d₂
  set q₃ : ℕ := n / d₃
  set q₄ : ℕ := n / d₄
  set q₅ : ℕ := n / d₅
  set z : ℤ :=
    ((d₄ : ℤ) - (d₃ : ℤ)) * ((d₅ : ℤ) - (d₄ : ℤ)) * ((d₅ : ℤ) - (d₃ : ℤ)) *
      (((d₂ : ℤ) - (d₁ : ℤ)) * (((d₃ : ℤ) + (q₃ : ℤ)) - ((d₂ : ℤ) + (q₂ : ℤ))) -
        ((d₃ : ℤ) - (d₂ : ℤ)) * (((d₂ : ℤ) + (q₂ : ℤ)) - ((d₁ : ℤ) + (q₁ : ℤ)))) -
    ((d₂ : ℤ) - (d₁ : ℤ)) * ((d₃ : ℤ) - (d₂ : ℤ)) * ((d₃ : ℤ) - (d₁ : ℤ)) *
      (((d₄ : ℤ) - (d₃ : ℤ)) * (((d₅ : ℤ) + (q₅ : ℤ)) - ((d₄ : ℤ) + (q₄ : ℤ))) -
        ((d₅ : ℤ) - (d₄ : ℤ)) * (((d₄ : ℤ) + (q₄ : ℤ)) - ((d₃ : ℤ) + (q₃ : ℤ))))
  have hz_eq :
      (z : ℝ) =
        ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
          (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (q₃ : ℝ)) - ((d₂ : ℝ) + (q₂ : ℝ))) -
            ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (q₂ : ℝ)) - ((d₁ : ℝ) + (q₁ : ℝ)))) -
        ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
          (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (q₅ : ℝ)) - ((d₄ : ℝ) + (q₄ : ℝ))) -
            ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (q₄ : ℝ)) - ((d₃ : ℝ) + (q₃ : ℝ)))) := by
    dsimp [z]; push_cast; ring
  have hv_z :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (z : ℝ) =
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
          ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
          ((d₄ : ℝ) * (d₅ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
    rw [hz_eq]; exact hv
  have hzR_pos : (0 : ℝ) < (z : ℝ) :=
    (mul_pos_iff_of_pos_left hdprod_pos).mp (hv_z.symm ▸ hrhs_pos)
  have hz_pos : 0 < z := by exact_mod_cast hzR_pos
  have hz_ge : (1 : ℤ) ≤ z := hz_pos
  have hzR_ge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge
  linarith [hz_eq, hzR_ge]

/-- Exact unweighted fourth-order 5-tuple hyperbolic Vandermonde determinant identity:
`d₁*d₂*d₃*d₄*d₅ * Δ⁽⁴⁾₁₂₃₄₅ = n * V₅(d₁,d₂,d₃,d₄,d₅)`. -/
theorem fourth_order_hyperbolic_vandermonde_five_tuple_identity
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) *
      (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) *
        (((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
          (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
            ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
        ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
          (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
            ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
          (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
            ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
          (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
            ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
        ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) *
        ((d₅ : ℝ) - (d₁ : ℝ)) := by
  have h1 := third_order_hyperbolic_vandermonde_quadruple_identity n d₁ d₂ d₃ d₄ hd₁ hd₂ hd₃ hd₄
  have h2 := third_order_hyperbolic_vandermonde_quadruple_identity n d₂ d₃ d₄ d₅ hd₂ hd₃ hd₄ hd₅
  generalize
    (((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))))) = A₁ at h1 ⊢
  generalize
    (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) -
    ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))))) = A₂ at h2 ⊢
  linear_combination
    (d₅ : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) * h1 -
      (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) * h2

/-- Universal 5-divisor product bound from the coupled $3 \times 3$ Vandermonde determinant:
`d₁*d₂*d₃*d₄*d₅ ≤ n*(d₂-d₁)*(d₃-d₂)*(d₃-d₁)*(d₄-d₃)*(d₅-d₄)*(d₅-d₃)*(d₄*d₅ - d₁*d₂)`. -/
theorem five_tuple_product_le_mul_coupled_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    d₁ * d₂ * d₃ * d₄ * d₅ ≤
      n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) * (d₄ - d₃) * (d₅ - d₄) * (d₅ - d₃) *
        (d₄ * d₅ - d₁ * d₂) := by
  have hv := five_tuple_coupled_vandermonde_identity n d₁ d₂ d₃ d₄ d₅ hd₁ hd₂ hd₃ hd₄ hd₅
  have h1 := one_le_five_tuple_coupled_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅ hd₁ hd₂ hd₃ hd₄ hd₅
    hlt12 hlt23 hlt34 hlt45
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have hd₅_pos : (0 : ℝ) < (d₅ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₅
  have hdprod_nonneg : 0 ≤ (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) := by positivity
  set Δc : ℝ :=
    ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))))
  have hΔc_ge : 1 ≤ Δc := by dsimp [Δc]; linarith [h1]
  have hmul_le :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * 1 ≤
        (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * Δc :=
    mul_le_mul_of_nonneg_left hΔc_ge hdprod_nonneg
  have hleR :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) ≤
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
          ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
          ((d₄ : ℝ) * (d₅ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
    linarith [hmul_le, hv]
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
  have hle34 : d₃ ≤ d₄ := le_of_lt hlt34
  have hle45 : d₄ ≤ d₅ := le_of_lt hlt45
  have hle13 : d₁ ≤ d₃ := le_trans hle12 hle23
  have hle35 : d₃ ≤ d₅ := le_trans hle34 hle45
  have hle_prod : d₁ * d₂ ≤ d₄ * d₅ :=
    Nat.mul_le_mul (le_trans hle13 hle34) (le_trans hle23 hle35)
  have hcast :
      ((d₁ * d₂ * d₃ * d₄ * d₅ : ℕ) : ℝ) ≤
        ((n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) * (d₄ - d₃) * (d₅ - d₄) * (d₅ - d₃) *
          (d₄ * d₅ - d₁ * d₂) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle12, Nat.cast_sub hle23, Nat.cast_sub hle13,
      Nat.cast_sub hle34, Nat.cast_sub hle45, Nat.cast_sub hle35, Nat.cast_sub hle_prod]
    exact hleR
  exact_mod_cast hcast

/-! ## Section 15: Divisor-Ratio and 5-Tuple Spacing Lower Bounds Above $n^{1/2}$ -/

/-- For any strictly increasing 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` in `Erdos886Divisors n ε C`,
the coupled 5-tuple gap product strictly exceeds `n * n^(1/2) = n^(3/2)`. -/
theorem mul_sqrt_lt_coupled_vandermonde_of_five_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) <
      (((d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) * (d₄ - d₃) * (d₅ - d₄) * (d₅ - d₃) *
        (d₄ * d₅ - d₁ * d₂) : ℕ) : ℝ) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hprod := five_tuple_product_le_mul_coupled_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅
    hm1.1 hm2.1 hm3.1 hm4.1 hm5.1 hlt12 hlt23 hlt34 hlt45
  set Vc : ℕ :=
    (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) * (d₄ - d₃) * (d₅ - d₄) * (d₅ - d₃) *
      (d₄ * d₅ - d₁ * d₂)
  have hprod_assoc : d₁ * d₂ * d₃ * d₄ * d₅ ≤ n * Vc := by
    dsimp [Vc]; simpa [Nat.mul_assoc] using hprod
  have hprodR : (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) ≤ (n : ℝ) * (Vc : ℝ) := by
    have hcast : ((d₁ * d₂ * d₃ * d₄ * d₅ : ℕ) : ℝ) ≤ ((n * Vc : ℕ) : ℝ) := by
      exact_mod_cast hprod_assoc
    push_cast at hcast; exact hcast
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hs_pos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hs_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := rpow_half_sq n
  have h12_gt : (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith [hm1.2.1, hm2.2.1]
  have h34_gt : (n : ℝ) < (d₃ : ℝ) * (d₄ : ℝ) := by nlinarith [hm3.2.1, hm4.2.1]
  have h1234_gt : (n : ℝ) * (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) := by
    nlinarith [h12_gt, h34_gt]
  have h12345_gt : (n : ℝ) * ((n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) <
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) := by
    nlinarith [h1234_gt, hm5.2.1]
  have hmul_lt : (n : ℝ) * ((n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) < (n : ℝ) * (Vc : ℝ) :=
    lt_of_lt_of_le h12345_gt hprodR
  exact lt_of_mul_lt_mul_left hmul_lt (le_of_lt hn_pos)

/-- For any strictly increasing 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` of divisors of `n`,
the complementary quotients drop by at least `4`: `n / d₅ + 4 ≤ n / d₁`. -/
theorem five_tuple_quotient_drop_ge_four_of_lt
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    n / d₅ + 4 ≤ n / d₁ := by
  have hstep : ∀ a b : ℕ, a ∈ Nat.divisors n → b ∈ Nat.divisors n → a < b → n / b + 1 ≤ n / a := by
    intro a b ha hb hab
    have hde_a : (a : ℝ) * (n / a : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have hde_b : (b : ℝ) * (n / b : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hb).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors ha
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hb
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hid : (a : ℝ) * (b : ℝ) * ((n / a : ℕ) - (n / b : ℕ)) = (n : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      linear_combination (b : ℝ) * hde_a - (a : ℝ) * hde_b
    have hprod_pos : 0 < (n : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      have : 0 < (b : ℝ) - (a : ℝ) := by linarith
      positivity
    have hab_pos : 0 < (a : ℝ) * (b : ℝ) := by positivity
    have hdiff_pos : 0 < ((n / a : ℕ) : ℝ) - ((n / b : ℕ) : ℝ) :=
      (mul_pos_iff_of_pos_left hab_pos).mp (hid.symm ▸ hprod_pos)
    have hlt_q : ((n / b : ℕ) : ℝ) < ((n / a : ℕ) : ℝ) := by linarith
    have hlt_nat : n / b < n / a := by exact_mod_cast hlt_q
    omega
  have h12 := hstep d₁ d₂ hd₁ hd₂ hlt12
  have h23 := hstep d₂ d₃ hd₂ hd₃ hlt23
  have h34 := hstep d₃ d₄ hd₃ hd₄ hlt34
  have h45 := hstep d₄ d₅ hd₄ hd₅ hlt45
  omega

/-- For any strictly increasing 5-tuple `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅` of divisors of `n`,
the total divisor span is at least `8`: `d₁ + 8 ≤ d₅`. -/
theorem five_tuple_divisor_span_ge_eight_of_ge_sqrt
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    d₁ + 8 ≤ d₅ := by
  have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hs₃ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₃ : ℝ) := by
    have : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
    linarith
  have hs₄ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₄ : ℝ) := by
    have : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
    linarith
  have hsum12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have hsum23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hd₂ hd₃ hs₂ hlt23
  have hsum34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hd₃ hd₄ hs₃ hlt34
  have hsum45 := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hd₄ hd₅ hs₄ hlt45
  have hquot := five_tuple_quotient_drop_ge_four_of_lt n d₁ d₂ d₃ d₄ d₅
    hd₁ hd₂ hd₃ hd₄ hd₅ hlt12 hlt23 hlt34 hlt45
  omega

/-- Universal divisor-ratio product bound across a 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` dividing `n`:
`4 * d₁ * d₅ ≤ n * (d₅ - d₁)`. -/
theorem four_mul_first_last_le_mul_span_of_five_divisors
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    4 * d₁ * d₅ ≤ n * (d₅ - d₁) := by
  have hq := five_tuple_quotient_drop_ge_four_of_lt n d₁ d₂ d₃ d₄ d₅ hd₁ hd₂ hd₃ hd₄ hd₅
    hlt12 hlt23 hlt34 hlt45
  have hde₁ : (d₁ : ℝ) * (n / d₁ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₁).1
  have hde₅ : (d₅ : ℝ) * (n / d₅ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₅).1
  have hid : (d₁ : ℝ) * (d₅ : ℝ) * ((n / d₁ : ℕ) - (n / d₅ : ℕ)) = (n : ℝ) * ((d₅ : ℝ) - (d₁ : ℝ)) := by
    linear_combination (d₅ : ℝ) * hde₁ - (d₁ : ℝ) * hde₅
  have hqR : (4 : ℝ) ≤ ((n / d₁ : ℕ) : ℝ) - ((n / d₅ : ℕ) : ℝ) := by
    have : ((n / d₅ + 4 : ℕ) : ℝ) ≤ ((n / d₁ : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast at this; linarith
  have hprod_nonneg : 0 ≤ (d₁ : ℝ) * (d₅ : ℝ) := by positivity
  have hmul_le :
      (d₁ : ℝ) * (d₅ : ℝ) * 4 ≤ (d₁ : ℝ) * (d₅ : ℝ) * (((n / d₁ : ℕ) : ℝ) - ((n / d₅ : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hqR hprod_nonneg
  have hleR : 4 * (d₁ : ℝ) * (d₅ : ℝ) ≤ (n : ℝ) * ((d₅ : ℝ) - (d₁ : ℝ)) := by
    linarith [hmul_le, hid]
  have hle15 : d₁ ≤ d₅ := le_of_lt (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 hlt45))
  have hcast : ((4 * d₁ * d₅ : ℕ) : ℝ) ≤ ((n * (d₅ - d₁) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle15]
    exact hleR
  exact_mod_cast hcast

/-- Relative divisor-ratio upper bound on `Erdos886Divisors n ε C`: for any `d₁, d₂` in
`Erdos886Divisors n ε C` with `C ≥ 0`, `(d₂ : ℝ) - (d₁ : ℝ) < C * (d₁ : ℝ) * (n : ℝ) ^ (-ε)`. -/
theorem divisor_ratio_sub_one_lt_mul_rpow_neg_eps_of_mem_erdos886Divisors
    (n d₁ d₂ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C) :
    (d₂ : ℝ) - (d₁ : ℝ) < C * (d₁ : ℝ) * (n : ℝ) ^ (-ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hrpow_split : (n : ℝ) ^ (1 / 2 - ε) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-ε) := by
    have hexp : (1 / 2 - ε : ℝ) = (1 / 2 : ℝ) + (-ε) := by ring
    rw [hexp, Real.rpow_add hn_pos]
  have hneg_pos : 0 ≤ (n : ℝ) ^ (-ε) := Real.rpow_nonneg (le_of_lt hn_pos) _
  have h1 : (d₂ : ℝ) - (d₁ : ℝ) < C * (n : ℝ) ^ (1 / 2 - ε) := by linarith [hm1.2.1, hm2.2.2]
  rw [hrpow_split] at h1
  have h2 : C * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-ε)) ≤ C * (d₁ : ℝ) * (n : ℝ) ^ (-ε) := by
    have : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-ε) ≤ (d₁ : ℝ) * (n : ℝ) ^ (-ε) :=
      mul_le_mul_of_nonneg_right (le_of_lt hm1.2.1) hneg_pos
    have hmul := mul_le_mul_of_nonneg_left this hC
    linarith
  linarith

/-- On any 5-tuple `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅` of divisors of `n` with minimal
adjacent complementary-sum steps `s_{i+1} = s_i + 1` (`i = 1,2,3,4`), strict concavity of
divisor gaps forces `d₅ - d₄ ≥ 2`, `d₄ - d₃ ≥ 3`, `d₃ - d₂ ≥ 4`, and `d₂ - d₁ ≥ 5`. -/
theorem five_tuple_first_step_ge_five_of_minimal_sum_steps
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅)
    (hstep12 : d₂ + n / d₂ = d₁ + n / d₁ + 1)
    (hstep23 : d₃ + n / d₃ = d₂ + n / d₂ + 1)
    (hstep34 : d₄ + n / d₄ = d₃ + n / d₃ + 1)
    (hstep45 : d₅ + n / d₅ = d₄ + n / d₄ + 1) :
    2 ≤ d₅ - d₄ ∧ 3 ≤ d₄ - d₃ ∧ 4 ≤ d₃ - d₂ ∧ 5 ≤ d₂ - d₁ := by
  have hconc : ∀ a b c : ℕ, a ∈ Nat.divisors n → b ∈ Nat.divisors n → c ∈ Nat.divisors n →
      a < b → b < c → b + n / b = a + n / a + 1 → c + n / c = b + n / b + 1 → c - b + 1 ≤ b - a := by
    intro a b c ha hb hc hab hbc hsab hsbc
    have h1 := complementary_sum_diff_product_identity n a b ha hb
    have h2 := complementary_sum_diff_product_identity n b c hb hc
    have hv :
        (a : ℝ) * (b : ℝ) * (c : ℝ) *
          (((b : ℝ) - (a : ℝ)) * (((c : ℝ) + (n / c : ℕ)) - ((b : ℝ) + (n / b : ℕ))) -
            ((c : ℝ) - (b : ℝ)) * (((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)))) =
          (n : ℝ) * ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ)) := by
      linear_combination (a : ℝ) * ((b : ℝ) - (a : ℝ)) * h2 - (c : ℝ) * ((c : ℝ) - (b : ℝ)) * h1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors ha
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hb
    have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hc
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hbcR : (b : ℝ) < (c : ℝ) := by exact_mod_cast hbc
    have hrhs_pos : 0 < (n : ℝ) * ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ)) := by
      have : 0 < (b : ℝ) - (a : ℝ) := by linarith
      have : 0 < (c : ℝ) - (b : ℝ) := by linarith
      have : 0 < (c : ℝ) - (a : ℝ) := by linarith
      positivity
    have hprod_pos : 0 < (a : ℝ) * (b : ℝ) * (c : ℝ) := by positivity
    have hsabR : ((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)) = 1 := by
      have hcast : ((b + n / b : ℕ) : ℝ) = ((a + n / a + 1 : ℕ) : ℝ) := by exact_mod_cast hsab
      push_cast at hcast; linarith
    have hsbcR : ((c : ℝ) + (n / c : ℕ)) - ((b : ℝ) + (n / b : ℕ)) = 1 := by
      have hcast : ((c + n / c : ℕ) : ℝ) = ((b + n / b + 1 : ℕ) : ℝ) := by exact_mod_cast hsbc
      push_cast at hcast; linarith
    have hΔ_pos :
        0 < ((b : ℝ) - (a : ℝ)) * (((c : ℝ) + (n / c : ℕ)) - ((b : ℝ) + (n / b : ℕ))) -
          ((c : ℝ) - (b : ℝ)) * (((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ))) :=
      (mul_pos_iff_of_pos_left hprod_pos).mp (hv.symm ▸ hrhs_pos)
    have hdiff_pos : 0 < ((b : ℝ) - (a : ℝ)) - ((c : ℝ) - (b : ℝ)) := by
      rw [hsabR, hsbcR] at hΔ_pos
      linarith
    have hlt_natR : ((c - b : ℕ) : ℝ) < ((b - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hbc), Nat.cast_sub (le_of_lt hab)]
      linarith
    have hlt_nat : c - b < b - a := by exact_mod_cast hlt_natR
    omega
  have hc123 := hconc d₁ d₂ d₃ hd₁ hd₂ hd₃ hlt12 hlt23 hstep12 hstep23
  have hc234 := hconc d₂ d₃ d₄ hd₂ hd₃ hd₄ hlt23 hlt34 hstep23 hstep34
  have hc345 := hconc d₃ d₄ d₅ hd₃ hd₄ hd₅ hlt34 hlt45 hstep34 hstep45
  have hq45 : n / d₅ + 1 ≤ n / d₄ := by
    have hde₄ : (d₄ : ℝ) * (n / d₄ : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₄).1
    have hde₅ : (d₅ : ℝ) * (n / d₅ : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₅).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₄).2
    have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
    have hd₅_pos : (0 : ℝ) < (d₅ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₅
    have h45R : (d₄ : ℝ) < (d₅ : ℝ) := by exact_mod_cast hlt45
    have hid : (d₄ : ℝ) * (d₅ : ℝ) * ((n / d₄ : ℕ) - (n / d₅ : ℕ)) = (n : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) := by
      linear_combination (d₅ : ℝ) * hde₄ - (d₄ : ℝ) * hde₅
    have hprod_pos : 0 < (n : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) := by
      have : 0 < (d₅ : ℝ) - (d₄ : ℝ) := by linarith
      positivity
    have hd45_pos : 0 < (d₄ : ℝ) * (d₅ : ℝ) := by positivity
    have hdiff_pos : 0 < ((n / d₄ : ℕ) : ℝ) - ((n / d₅ : ℕ) : ℝ) :=
      (mul_pos_iff_of_pos_left hd45_pos).mp (hid.symm ▸ hprod_pos)
    have hlt_q : ((n / d₅ : ℕ) : ℝ) < ((n / d₄ : ℕ) : ℝ) := by linarith
    have hlt_nat : n / d₅ < n / d₄ := by exact_mod_cast hlt_q
    omega
  omega

/-- Under minimal adjacent Ruzsa complementary-sum steps `s_{i+1} = s_i + 1` (`i = 1,2,3,4`)
for divisors `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅` of `n`, the total 5-tuple span is at least `14`. -/
theorem five_tuple_divisor_span_ge_fourteen_of_minimal_sum_steps
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅)
    (hstep12 : d₂ + n / d₂ = d₁ + n / d₁ + 1)
    (hstep23 : d₃ + n / d₃ = d₂ + n / d₂ + 1)
    (hstep34 : d₄ + n / d₄ = d₃ + n / d₃ + 1)
    (hstep45 : d₅ + n / d₅ = d₄ + n / d₄ + 1) :
    d₁ + 14 ≤ d₅ := by
  have hsteps := five_tuple_first_step_ge_five_of_minimal_sum_steps n d₁ d₂ d₃ d₄ d₅
    hd₁ hd₂ hd₃ hd₄ hd₅ hs₁ hlt12 hlt23 hlt34 hlt45 hstep12 hstep23 hstep34 hstep45
  omega

/-! ## Section 16: Telescoping 5-Tuple Ruzsa Complementary-Sum Span Bounds & $1/8 \le \varepsilon < 1/6$ Thresholds -/

/-- Exact telescoping Ruzsa complementary-sum span decomposition across any 5-tuple:
`(d₂ - d₁)*(s₅ - s₁) = Δ₁₂₃ + Δ₁₂₃₄ + Δ₁₂₄₅ + (d₅ - d₁)*(s₂ - s₁)`. -/
theorem ruzsa_five_tuple_span_bambah_chowla_decomposition
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      ((d₅ : ℝ) - (d₁ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
  ring

/-- Universal 5-tuple Ruzsa span inequality for divisors `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅` of `n`:
`(d₅ - d₁) + 3 ≤ (d₂ - d₁) * ((d₅ + n/d₅) - (d₁ + n/d₁))`. -/
theorem five_tuple_span_add_three_le_first_gap_mul_ruzsa_span
    (n d₁ d₂ d₃ d₄ d₅ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    (d₅ - d₁) + 3 ≤ (d₂ - d₁) * ((d₅ + n / d₅) - (d₁ + n / d₁)) := by
  have hbc : ∀ c d : ℕ, c ∈ Nat.divisors n → d ∈ Nat.divisors n → d₂ ≤ c → c < d →
      ((d : ℝ) - (c : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 1 ≤
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d : ℝ) + (n / d : ℕ)) - ((c : ℝ) + (n / c : ℕ))) := by
    intro c d hc hd hle2c hcd
    have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
    have hcd_id := complementary_sum_diff_product_identity n c d hc hd
    have hv :
        (d₁ : ℝ) * (d₂ : ℝ) * (c : ℝ) * (d : ℝ) *
          (((d₂ : ℝ) - (d₁ : ℝ)) * (((d : ℝ) + (n / d : ℕ)) - ((c : ℝ) + (n / c : ℕ))) -
            ((d : ℝ) - (c : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
          (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d : ℝ) - (c : ℝ)) * ((c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
      linear_combination (d₁ : ℝ) * (d₂ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * hcd_id -
        (c : ℝ) * (d : ℝ) * ((d : ℝ) - (c : ℝ)) * h12
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
    have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
    have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
    have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hc
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have h12R : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    have h2cR : (d₂ : ℝ) ≤ (c : ℝ) := by exact_mod_cast hle2c
    have hcdR : (c : ℝ) < (d : ℝ) := by exact_mod_cast hcd
    have hrhs_pos :
        0 < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d : ℝ) - (c : ℝ)) * ((c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
      have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
      have : 0 < (d : ℝ) - (c : ℝ) := by linarith
      have : 0 < (c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith
      positivity
    have hprod_pos : 0 < (d₁ : ℝ) * (d₂ : ℝ) * (c : ℝ) * (d : ℝ) := by positivity
    set q₁ : ℕ := n / d₁
    set q₂ : ℕ := n / d₂
    set qc : ℕ := n / c
    set qd : ℕ := n / d
    set z : ℤ :=
      ((d₂ : ℤ) - (d₁ : ℤ)) * (((d : ℤ) + (qd : ℤ)) - ((c : ℤ) + (qc : ℤ))) -
        ((d : ℤ) - (c : ℤ)) * (((d₂ : ℤ) + (q₂ : ℤ)) - ((d₁ : ℤ) + (q₁ : ℤ)))
    have hz_eq :
        (z : ℝ) =
          ((d₂ : ℝ) - (d₁ : ℝ)) * (((d : ℝ) + (qd : ℝ)) - ((c : ℝ) + (qc : ℝ))) -
            ((d : ℝ) - (c : ℝ)) * (((d₂ : ℝ) + (q₂ : ℝ)) - ((d₁ : ℝ) + (q₁ : ℝ))) := by
      dsimp [z]; push_cast; ring
    have hv_z :
        (d₁ : ℝ) * (d₂ : ℝ) * (c : ℝ) * (d : ℝ) * (z : ℝ) =
          (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d : ℝ) - (c : ℝ)) * ((c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
      rw [hz_eq]; exact hv
    have hzR_pos : (0 : ℝ) < (z : ℝ) :=
      (mul_pos_iff_of_pos_left hprod_pos).mp (hv_z.symm ▸ hrhs_pos)
    have hz_pos : 0 < z := by exact_mod_cast hzR_pos
    have hz_ge : (1 : ℤ) ≤ z := hz_pos
    have hzR_ge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge
    linarith [hz_eq, hzR_ge]
  have hd123 := hbc d₂ d₃ hd₂ hd₃ (le_refl d₂) hlt23
  have hd1234 := hbc d₃ d₄ hd₃ hd₄ (le_of_lt hlt23) hlt34
  have hd1245 := hbc d₄ d₅ hd₄ hd₅ (le_of_lt (lt_trans hlt23 hlt34)) hlt45
  have hdecomp := ruzsa_five_tuple_span_bambah_chowla_decomposition n d₁ d₂ d₃ d₄ d₅
  have hs12_nat := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have hs12R : (1 : ℝ) ≤ ((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have : ((d₁ + n / d₁ + 1 : ℕ) : ℝ) ≤ ((d₂ + n / d₂ : ℕ) : ℝ) := by exact_mod_cast hs12_nat
    push_cast at this; linarith
  have hle15 : d₁ ≤ d₅ := le_of_lt (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 hlt45))
  have h15_nonneg : 0 ≤ (d₅ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) ≤ (d₅ : ℝ) := by exact_mod_cast hle15
    linarith
  have hmul15 :
      ((d₅ : ℝ) - (d₁ : ℝ)) * 1 ≤
        ((d₅ : ℝ) - (d₁ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) :=
    mul_le_mul_of_nonneg_left hs12R h15_nonneg
  have hleR :
      ((d₅ : ℝ) - (d₁ : ℝ)) + 3 ≤
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
    linarith [hd123, hd1234, hd1245, hdecomp, hmul15]
  have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hs₃ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₃ : ℝ) := by
    have : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
    linarith
  have hs₄ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₄ : ℝ) := by
    have : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
    linarith
  have hs23_nat := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hd₂ hd₃ hs₂ hlt23
  have hs34_nat := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hd₃ hd₄ hs₃ hlt34
  have hs45_nat := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hd₄ hd₅ hs₄ hlt45
  have hs15_le : d₁ + n / d₁ ≤ d₅ + n / d₅ := by omega
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hcast :
      (((d₅ - d₁) + 3 : ℕ) : ℝ) ≤
        (((d₂ - d₁) * ((d₅ + n / d₅) - (d₁ + n / d₁)) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle15, Nat.cast_sub hle12, Nat.cast_sub hs15_le]
    exact hleR
  exact_mod_cast hcast

/-- For any strictly increasing 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` in `Erdos886Divisors n ε C`
with `C ≥ 0`, `(d₅ - d₁) + 3 < (d₂ - d₁) * C^2 * n^(1/2 - 2 * ε)`. -/
theorem five_tuple_span_add_three_lt_first_gap_mul_sq_rpow_of_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    ((d₅ : ℝ) - (d₁ : ℝ)) + 3 < ((d₂ : ℝ) - (d₁ : ℝ)) * C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hle := five_tuple_span_add_three_le_first_gap_mul_ruzsa_span n d₁ d₂ d₃ d₄ d₅
    hm1.1 hm2.1 hm3.1 hm4.1 hm5.1 (le_of_lt hm1.2.1) hlt12 hlt23 hlt34 hlt45
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₅ ε C hC hd₁ hd₅
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hm2.1 hm3.1 (le_of_lt hm2.2.1) hlt23
  have hs34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hm3.1 hm4.1 (le_of_lt hm3.2.1) hlt34
  have hs45 := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hm4.1 hm5.1 (le_of_lt hm4.2.1) hlt45
  have hs15_le : d₁ + n / d₁ ≤ d₅ + n / d₅ := by omega
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle15 : d₁ ≤ d₅ := le_of_lt (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 hlt45))
  have hleR :
      ((d₅ : ℝ) - (d₁ : ℝ)) + 3 ≤
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
    have hcast :
        (((d₅ - d₁) + 3 : ℕ) : ℝ) ≤
          (((d₂ - d₁) * ((d₅ + n / d₅) - (d₁ + n / d₁)) : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast [Nat.cast_sub hle15, Nat.cast_sub hle12, Nat.cast_sub hs15_le] at hcast
    exact hcast
  have h12_pos : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hmul_lt :
      ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) <
        ((d₂ : ℝ) - (d₁ : ℝ)) * (C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε)) :=
    mul_lt_mul_of_pos_left hspan h12_pos
  linarith [hleR, hmul_lt]

/-- Any strictly increasing 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` in `Erdos886Divisors n ε C`
with `C ≥ 0` forces `4 < C^2 * n^(1/2 - 2 * ε)`. -/
theorem four_lt_sq_mul_rpow_of_five_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    4 < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hm2.1 hm3.1 (le_of_lt hm2.2.1) hlt23
  have hs34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hm3.1 hm4.1 (le_of_lt hm3.2.1) hlt34
  have hs45 := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hm4.1 hm5.1 (le_of_lt hm4.2.1) hlt45
  have hstep : d₁ + n / d₁ + 4 ≤ d₅ + n / d₅ := by omega
  have hstepR : (4 : ℝ) ≤ ((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 4 : ℕ) : ℝ) ≤ ((d₅ + n / d₅ : ℕ) : ℝ) := by exact_mod_cast hstep
    push_cast at hcast; linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₅ ε C hC hd₁ hd₅
  linarith

/-- If a 5-tuple `d₁ < d₂ < d₃ < d₄ < d₅` in `Erdos886Divisors n ε C` with `C ≥ 0` has
a non-decreasing middle divisor gap `d₃ - d₂ ≤ d₄ - d₃`, then `5 < C^2 * n^(1/2 - 2 * ε)`. -/
theorem five_lt_sq_mul_rpow_of_five_mem_erdos886Divisors_of_middle_gap_le
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅)
    (hgap : d₃ - d₂ ≤ d₄ - d₃) :
    5 < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hm2.1 hm3.1 (le_of_lt hm2.2.1) hlt23
  have hs34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hm3.1 hm4.1 (le_of_lt hm3.2.1) hlt34
  have hs45 := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hm4.1 hm5.1 (le_of_lt hm4.2.1) hlt45
  have h23_id := complementary_sum_diff_product_identity n d₂ d₃ hm2.1 hm3.1
  have h34_id := complementary_sum_diff_product_identity n d₃ d₄ hm3.1 hm4.1
  have hv :
      (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) *
        (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
          ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) =
        (n : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) := by
    linear_combination (d₂ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h34_id - (d₄ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * h23_id
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hm2.1
  have hd₃_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hm3.1
  have hd₄_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hm4.1
  have h23R : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
  have h34R : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
  have hrhs_pos : 0 < (n : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) := by
    have : 0 < (d₃ : ℝ) - (d₂ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₃ : ℝ) := by linarith
    have : 0 < (d₄ : ℝ) - (d₂ : ℝ) := by linarith
    positivity
  have hprod_pos : 0 < (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) := by positivity
  have hΔ_pos :
      0 < ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) :=
    (mul_pos_iff_of_pos_left hprod_pos).mp (hv.symm ▸ hrhs_pos)
  have hgapR : (d₃ : ℝ) - (d₂ : ℝ) ≤ (d₄ : ℝ) - (d₃ : ℝ) := by
    have hcast : ((d₃ - d₂ : ℕ) : ℝ) ≤ ((d₄ - d₃ : ℕ) : ℝ) := by exact_mod_cast hgap
    rw [Nat.cast_sub (le_of_lt hlt23), Nat.cast_sub (le_of_lt hlt34)] at hcast
    exact hcast
  have hs23_nonneg : 0 ≤ ((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)) := by
    have hcast : ((d₂ + n / d₂ + 1 : ℕ) : ℝ) ≤ ((d₃ + n / d₃ : ℕ) : ℝ) := by exact_mod_cast hs23
    push_cast at hcast; linarith
  have hmul_gap :
      ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) ≤
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) :=
    mul_le_mul_of_nonneg_right hgapR hs23_nonneg
  have h23_pos : 0 < (d₃ : ℝ) - (d₂ : ℝ) := by linarith
  have hmul_step_lt :
      ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) <
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) := by
    linarith [hΔ_pos, hmul_gap]
  have hlt_stepR :
      ((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)) <
        ((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)) :=
    lt_of_mul_lt_mul_left hmul_step_lt (le_of_lt h23_pos)
  have hlt_step : (d₃ + n / d₃) - (d₂ + n / d₂) < (d₄ + n / d₄) - (d₃ + n / d₃) := by
    have hcast : (((d₃ + n / d₃) - (d₂ + n / d₂) : ℕ) : ℝ) < (((d₄ + n / d₄) - (d₃ + n / d₃) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; exact hlt_stepR
    exact_mod_cast hcast
  have hstep5 : d₁ + n / d₁ + 5 ≤ d₅ + n / d₅ := by omega
  have hstep5R : (5 : ℝ) ≤ ((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 5 : ℕ) : ℝ) ≤ ((d₅ + n / d₅ : ℕ) : ℝ) := by exact_mod_cast hstep5
    push_cast at hcast; linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₅ ε C hC hd₁ hd₅
  linarith

/-- Explicit 5-tuple threshold for `1/6 ≤ ε`: if `d₁ < d₂ < d₃ < d₄ < d₅` belong to
`Erdos886Divisors n ε 1` with `1 / 6 ≤ ε`, then `4096 < n` (since `4^6 = 4096`). -/
theorem gt_4096_of_five_mem_erdos886Divisors_of_sixth_le
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) (ε : ℝ) (hε : 1 / 6 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1) (hd₂ : d₂ ∈ Erdos886Divisors n ε 1)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε 1) (hd₄ : d₄ ∈ Erdos886Divisors n ε 1)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε 1)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    4096 < n := by
  have h4 := four_lt_sq_mul_rpow_of_five_mem_erdos886Divisors n d₁ d₂ d₃ d₄ d₅ ε 1 (by norm_num)
    hd₁ hd₂ hd₃ hd₄ hd₅ hlt12 hlt23 hlt34 hlt45
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁).1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4_lt : (4 : ℝ) < (n : ℝ) ^ (1 / 6 : ℝ) := by linarith
  by_contra hle
  have hn_le : (n : ℝ) ≤ 4096 := by
    have : n ≤ 4096 := by omega
    exact_mod_cast this
  have hrpow_le : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (4096 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by norm_num)
  have h4096 : (4096 : ℝ) ^ (1 / 6 : ℝ) = 4 := by
    have h_eq : (4096 : ℝ) = (4 : ℝ) ^ (6 : ℝ) := by norm_num
    rw [h_eq, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-- Explicit 5-tuple threshold for `1/8 ≤ ε`: if `d₁ < d₂ < d₃ < d₄ < d₅` belong to
`Erdos886Divisors n ε 1` with `1 / 8 ≤ ε`, then `256 < n` (since `4^4 = 256`). -/
theorem gt_256_of_five_mem_erdos886Divisors_of_eighth_le
    (n d₁ d₂ d₃ d₄ d₅ : ℕ) (ε : ℝ) (hε : 1 / 8 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1) (hd₂ : d₂ ∈ Erdos886Divisors n ε 1)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε 1) (hd₄ : d₄ ∈ Erdos886Divisors n ε 1)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε 1)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) :
    256 < n := by
  have h4 := four_lt_sq_mul_rpow_of_five_mem_erdos886Divisors n d₁ d₂ d₃ d₄ d₅ ε 1 (by norm_num)
    hd₁ hd₂ hd₃ hd₄ hd₅ hlt12 hlt23 hlt34 hlt45
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁).1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4_lt : (4 : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
  by_contra hle
  have hn_le : (n : ℝ) ≤ 256 := by
    have : n ≤ 256 := by omega
    exact_mod_cast this
  have hrpow_le : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (256 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by norm_num)
  have h256 : (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
    have h_eq : (256 : ℝ) = (4 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h_eq, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-! ## Section 17: Direct Conditional Reductions for `erdos_886` & Variants, Plus Controls -/

/-- Direct conditional reduction of the open conjecture `erdos_886`: if for every
`0 < ε < 1/4` there is an eventual upper bound `B ≥ 0` on pairwise Ruzsa complementary-sum
differences across `Erdos886Divisors n ε 1`, then `(Erdos886Divisors n ε 1).card` is
eventually bounded for all `ε > 0`. -/
theorem erdos_886_of_eventual_complementary_sum_span_bound
    (hspan : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1,
          ((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)) ≤ B) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K := by
  intro ε hε
  by_cases hq : 1 / 4 ≤ ε
  · exact erdos_886_of_quarter_le ε hq
  · have hq' : ε < 1 / 4 := lt_of_not_ge hq
    rcases hspan ε hε hq' with ⟨B, hB, hev⟩
    refine ⟨⌊B⌋₊ + 1, hev.mono (fun n hn => ?_)⟩
    have hreal : ((Erdos886Divisors n ε 1).card : ℝ) ≤ 1 + B := by
      apply card_nat_finset_le_of_strictMonoOn_image_diff
        (Erdos886Divisors n ε 1) (fun d => d + n / d)
      · intro a ha b hb hlt
        have ha_mem := (mem_erdos886Divisors_iff n a ε 1).mp ha
        have hb_mem := (mem_erdos886Divisors_iff n b ε 1).mp hb
        exact complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt
      · exact hB
      · intro a ha b hb
        have h := hn a ha b hb
        push_cast; linarith
    rcases (Erdos886Divisors n ε 1).eq_empty_or_nonempty with hempty | hne
    · simp [hempty]
    · have hcard_pos : 1 ≤ (Erdos886Divisors n ε 1).card := Finset.card_pos.mpr hne
      have hsub_le : ((Erdos886Divisors n ε 1).card - 1 : ℕ) ≤ ⌊B⌋₊ := by
        apply Nat.le_floor
        have hcast : (((Erdos886Divisors n ε 1).card - 1 : ℕ) : ℝ) =
            ((Erdos886Divisors n ε 1).card : ℝ) - 1 := by
          rw [Nat.cast_sub hcard_pos, Nat.cast_one]
        linarith
      omega

/-- Direct conditional reduction of `erdos_886` via eventual integer Ruzsa span exclusion:
if for every `0 < ε < 1/4` there is `K : ℕ` such that eventually no two elements of
`Erdos886Divisors n ε 1` have complementary-sum difference exceeding `K`, then the full
`erdos_886` conjecture holds for all `ε > 0`. -/
theorem erdos_886_of_eventual_nat_complementary_sum_gap_exclusion
    (hexcl : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ K : ℕ, ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1,
          (b + n / b) - (a + n / a) ≤ K) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K := by
  apply erdos_886_of_eventual_complementary_sum_span_bound
  intro ε hε hq
  rcases hexcl ε hε hq with ⟨K, hev⟩
  refine ⟨(K : ℝ), Nat.cast_nonneg K, hev.mono (fun n hn a ha b hb => ?_)⟩
  have hnat := hn a ha b hb
  by_cases hle : a + n / a ≤ b + n / b
  · have hcast : (((b + n / b) - (a + n / a) : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_sub hle] at hcast
    push_cast at hcast
    linarith
  · have hlt : b + n / b < a + n / a := lt_of_not_ge hle
    have hltR : ((b + n / b : ℕ) : ℝ) < ((a + n / a : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at hltR
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith

/-- Unified verification of both solved Erdős-Rosenfeld [ErRo97] variants matching the
exact target statements `erdos_886.variants.rosenfeld_bound` and
`erdos_886.variants.rosenfeld_infinite` in `FormalConjectures/ErdosProblems/886.lean`. -/
theorem erdos_886_variants_rosenfeld_combined :
    (∀ C > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (((Nat.divisors n).filter (fun (d : ℕ) =>
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
        ≤ 1 + C ^ 2) ∧
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card} :=
  ⟨erdos_886_rosenfeld_bound, erdos_886_rosenfeld_infinite⟩

/-- Negative control / sharp finite 5-tuple exclusions: for all `n ≤ 4096` and `1/6 ≤ ε`,
`(Erdos886Divisors n ε 1).card ≤ 4`; and for all `n ≤ 256` and `1/8 ≤ ε`,
`(Erdos886Divisors n ε 1).card ≤ 4`. -/
theorem negative_control_card_le_four_of_le_4096_of_sixth_le_and_le_256_of_eighth_le :
    (∀ n : ℕ, n ≤ 4096 → ∀ ε : ℝ, 1 / 6 ≤ ε → (Erdos886Divisors n ε 1).card ≤ 4) ∧
    (∀ n : ℕ, n ≤ 256 → ∀ ε : ℝ, 1 / 8 ≤ ε → (Erdos886Divisors n ε 1).card ≤ 4) := by
  have h_card_le : ∀ n k : ℕ, ∀ ε : ℝ, (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (k : ℝ) →
      (Erdos886Divisors n ε 1).card ≤ k := by
    intro n k ε hle
    by_cases hne : (Erdos886Divisors n ε 1).Nonempty
    · set s := Erdos886Divisors n ε 1
      let f : ℕ → ℕ := fun d => d + n / d
      have hmono : ∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b := by
        intro a ha b hb hlt
        have ha_mem := (mem_erdos886Divisors_iff n a ε 1).mp ha
        have hb_mem := (mem_erdos886Divisors_iff n b ε 1).mp hb
        exact complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt
      have hmin_mem : s.min' hne ∈ s := Finset.min'_mem s hne
      have hmax_mem : s.max' hne ∈ s := Finset.max'_mem s hne
      have hle_Elem : ∀ x ∈ s, f (s.min' hne) ≤ f x ∧ f x ≤ f (s.max' hne) := by
        intro x hx
        constructor
        · rcases lt_or_eq_of_le (Finset.min'_le s x hx) with hlt | heq
          · exact le_of_lt (hmono _ hmin_mem _ hx hlt)
          · rw [heq]
        · rcases lt_or_eq_of_le (Finset.le_max' s x hx) with hlt | heq
          · exact le_of_lt (hmono _ hx _ hmax_mem hlt)
          · rw [heq]
      have hle_span : (s.card : ℝ) ≤ 1 + ((f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ)) := by
        apply card_nat_finset_le_of_strictMonoOn_image_diff s f hmono
          ((f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ))
        · have h1 : (f (s.min' hne) : ℝ) ≤ (f (s.max' hne) : ℝ) := by
            exact_mod_cast (hle_Elem (s.max' hne) hmax_mem).1
          linarith
        · intro a ha b hb
          have ha_le : (f (s.min' hne) : ℝ) ≤ (f a : ℝ) := by exact_mod_cast (hle_Elem a ha).1
          have hb_le : (f b : ℝ) ≤ (f (s.max' hne) : ℝ) := by exact_mod_cast (hle_Elem b hb).2
          linarith
      have hlt_span : (f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ) < 1 ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
        have h := complementary_sum_span_lt_of_mem_erdos886Divisors n (s.min' hne) (s.max' hne)
          ε 1 (by norm_num) hmin_mem hmax_mem
        dsimp [f]; push_cast; linarith
      have hlt_k : (s.card : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hlt_nat : s.card < k + 1 := by exact_mod_cast hlt_k
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le k
  constructor
  · intro n hn ε hε
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [erdos886Divisors_zero]
    · apply h_card_le n 4 ε
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hn4096 : (n : ℝ) ≤ 4096 := by exact_mod_cast hn
      have hrpow4096 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (4096 : ℝ) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn4096 (by norm_num)
      have h4096 : (4096 : ℝ) ^ (1 / 6 : ℝ) = 4 := by
        have h_eq : (4096 : ℝ) = (4 : ℝ) ^ (6 : ℝ) := by norm_num
        rw [h_eq, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
  · intro n hn ε hε
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [erdos886Divisors_zero]
    · apply h_card_le n 4 ε
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hn256 : (n : ℝ) ≤ 256 := by exact_mod_cast hn
      have hrpow256 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (256 : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn256 (by norm_num)
      have h256 : (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
        have h_eq : (256 : ℝ) = (4 : ℝ) ^ (4 : ℝ) := by norm_num
        rw [h_eq, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith

/-- Positive control at `n = 36960` (the first 5-divisor witness at `ε = 1/8, C = 1`, with
divisors `210 < 220 < 224 < 231 < 240` and complementary sums `386 < 388 < 389 < 391 < 394`):
verifies exact evaluations `Δ₁₂₃ = 2`, `Δ₂₃₄ = 1`, `Δ₃₄₅ = 3`, `Δ₁₂₄₅ = 12`,
`(224 - 220)*(231 - 224)*Δ₁₂₄₅ = 336`, and `Δᶜᵒᵘᵖˡᵉᵈ₁₂₃₄₅ = 336`. -/
theorem positive_control_witness_36960_five_tuple_determinants :
    (((220 : ℝ) - (210 : ℝ)) * (((224 : ℝ) + (36960 / 224 : ℕ)) - ((220 : ℝ) + (36960 / 220 : ℕ))) -
      ((224 : ℝ) - (220 : ℝ)) * (((220 : ℝ) + (36960 / 220 : ℕ)) - ((210 : ℝ) + (36960 / 210 : ℕ)))) = 2 ∧
    (((224 : ℝ) - (220 : ℝ)) * (((231 : ℝ) + (36960 / 231 : ℕ)) - ((224 : ℝ) + (36960 / 224 : ℕ))) -
      ((231 : ℝ) - (224 : ℝ)) * (((224 : ℝ) + (36960 / 224 : ℕ)) - ((220 : ℝ) + (36960 / 220 : ℕ)))) = 1 ∧
    (((231 : ℝ) - (224 : ℝ)) * (((240 : ℝ) + (36960 / 240 : ℕ)) - ((231 : ℝ) + (36960 / 231 : ℕ))) -
      ((240 : ℝ) - (231 : ℝ)) * (((231 : ℝ) + (36960 / 231 : ℕ)) - ((224 : ℝ) + (36960 / 224 : ℕ)))) = 3 ∧
    (((220 : ℝ) - (210 : ℝ)) * (((240 : ℝ) + (36960 / 240 : ℕ)) - ((231 : ℝ) + (36960 / 231 : ℕ))) -
      ((240 : ℝ) - (231 : ℝ)) * (((220 : ℝ) + (36960 / 220 : ℕ)) - ((210 : ℝ) + (36960 / 210 : ℕ)))) = 12 ∧
    ((210 : ℝ) * (220 : ℝ) * (224 : ℝ) * (231 : ℝ) * (240 : ℝ) * (336 : ℝ) =
      (36960 : ℝ) * ((220 : ℝ) - (210 : ℝ)) * ((224 : ℝ) - (220 : ℝ)) * ((224 : ℝ) - (210 : ℝ)) *
        ((231 : ℝ) - (224 : ℝ)) * ((240 : ℝ) - (231 : ℝ)) * ((240 : ℝ) - (224 : ℝ)) *
        ((231 : ℝ) * (240 : ℝ) - (210 : ℝ) * (220 : ℝ))) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩


end Erdos886

