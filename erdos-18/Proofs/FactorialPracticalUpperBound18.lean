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

public import Mathlib

@[expose] public section

variable {M : Type*} [AddCommMonoid M]

def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

@[gcongr]
theorem subsetSums_mono {A B : Set M} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B :=
  fun _ ⟨C, hC⟩ => ⟨C, hC.1.trans h, hC.2⟩

namespace Nat

def IsPractical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → m ∈ subsetSums n.divisors

end Nat

open Filter Asymptotics Real

namespace Erdos18

/-- For a practical number $n$, $h(n)$ is the maximum over all $1 ≤ m ≤ n$ of
the minimum number of divisors of $n$ needed to represent $m$ as a sum of
distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/- ### Examples for `practicalH` -/

/-- $h(1) = 1$: we need the single divisor {1} to represent 1. -/
theorem practicalH_one : practicalH 1 = 1 := by
  norm_num [subsetSums, practicalH]

/-- $h(2) = 1$: divisors are {1, 2}, each of m=1,2 needs only 1 divisor. -/
theorem practicalH_two : practicalH 2 = 1 := by
  simp only [practicalH, (by decide : Finset.Icc 1 2 = ({1, 2} : Finset ℕ)),
    (by decide : Nat.divisors 2 = ({1, 2} : Finset ℕ)), Finset.sup_insert, Finset.sup_singleton]
  have h1 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 1 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{1}, by simp, rfl, {1}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {1}, by simp, rfl, {1}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  have h2 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 2 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{2}, by simp, rfl, {2}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {2}, by simp, rfl, {2}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  simp [h1, h2]

/-- $h(6) = 2$: divisors are {1, 2, 3, 6}. The hardest m to represent is
m=4 or m=5, each requiring 2 divisors: 4=1+3, 5=2+3. -/
theorem practicalH_six : practicalH 6 = 2 := by
  have hdiv : Nat.divisors 6 = ({1, 2, 3, 6} : Finset ℕ) := by decide
  apply le_antisymm
  · -- practicalH 6 ≤ 2 : each m in [1,6] is a sum of at most two divisors of 6.
    apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    interval_cases m
    · exact Nat.sInf_le ⟨{1, 2}, by rw [hdiv]; decide, by decide, {1}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2}, by rw [hdiv]; decide, by decide, {2}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2}, by rw [hdiv]; decide, by decide, {1, 2}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 3}, by rw [hdiv]; decide, by decide, {1, 3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{2, 3}, by rw [hdiv]; decide, by decide, {2, 3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 6}, by rw [hdiv]; decide, by decide, {6}, by simp, by decide⟩
  · -- 2 ≤ practicalH 6, witnessed by m = 4 (which needs two divisors: 4 = 1 + 3).
    have h4 : (4 : ℕ) ∈ Finset.Icc 1 6 := by decide
    refine le_trans ?_ (Finset.le_sup h4)
    apply le_csInf
    · exact ⟨2, {1, 3}, by rw [hdiv]; decide, by decide, {1, 3}, by simp, by decide⟩
    · rintro k ⟨D, hDsub, hDcard, B, hBsub, hBsum⟩
      by_contra! hk
      interval_cases k
      · -- D.card = 0 : D = ∅, so B = ∅ and the sum is 0 ≠ 4.
        rw [Finset.card_eq_zero] at hDcard
        subst hDcard
        rw [Finset.coe_empty, Set.subset_empty_iff, Finset.coe_eq_empty] at hBsub
        subst hBsub
        simp at hBsum
      · -- D.card = 1 : D = {d} with d ∣ 6, so the sum is 0 or d, neither equal to 4.
        rw [Finset.card_eq_one] at hDcard
        obtain ⟨d, rfl⟩ := hDcard
        have hd : d ∈ Nat.divisors 6 := hDsub (by simp)
        rw [hdiv] at hd
        rw [Finset.coe_subset, Finset.subset_singleton_iff] at hBsub
        fin_cases hd <;>
          rcases hBsub with h | h <;> subst h <;> simp at hBsum

/-- $h(12) = 3$: divisors are {1, 2, 3, 4, 6, 12}. The hardest m is
m=11, requiring 3 divisors: 11=1+4+6. -/
theorem practicalH_twelve : practicalH 12 = 3 := by
  have hdiv : Nat.divisors 12 = ({1, 2, 3, 4, 6, 12} : Finset ℕ) := by decide
  apply le_antisymm
  · -- practicalH 12 ≤ 3 : each m in [1,12] is a sum of at most three divisors of 12.
    apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    interval_cases m
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {1}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {2}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {4}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 4}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {1, 2, 3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{2, 4, 6}, by rw [hdiv]; decide, by decide, {2, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{3, 4, 6}, by rw [hdiv]; decide, by decide, {3, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{4, 6, 12}, by rw [hdiv]; decide, by decide, {4, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 4, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{2, 4, 6}, by rw [hdiv]; decide, by decide, {2, 4, 6}, by simp, by decide⟩
  · -- 3 ≤ practicalH 12, witnessed by m = 11 (needs three divisors: 11 = 1 + 4 + 6).
    have h11 : (11 : ℕ) ∈ Finset.Icc 1 12 := by decide
    refine le_trans ?_ (Finset.le_sup h11)
    apply le_csInf
    · exact ⟨3, {1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 4, 6}, by simp, by decide⟩
    · rintro k ⟨D, hDsub, hDcard, B, hBsub, hBsum⟩
      by_contra! hk
      interval_cases k
      · rw [Finset.card_eq_zero] at hDcard
        subst hDcard
        rw [Finset.coe_empty, Set.subset_empty_iff, Finset.coe_eq_empty] at hBsub
        subst hBsub
        simp at hBsum
      · rw [Finset.card_eq_one] at hDcard
        obtain ⟨d, rfl⟩ := hDcard
        have hd : d ∈ Nat.divisors 12 := hDsub (by simp)
        rw [hdiv] at hd
        rw [Finset.coe_subset, Finset.subset_singleton_iff] at hBsub
        fin_cases hd <;> rcases hBsub with h | h <;> subst h <;> simp at hBsum
      · rw [Finset.card_eq_two] at hDcard
        obtain ⟨a, b, hab, rfl⟩ := hDcard
        have ha : a ∈ Nat.divisors 12 := hDsub (by simp)
        have hb : b ∈ Nat.divisors 12 := hDsub (by simp)
        rw [hdiv] at ha hb
        have hBp : B ⊆ ({a, b} : Finset ℕ) := Finset.coe_subset.mp hBsub
        have key : ∀ S ∈ ({a, b} : Finset ℕ).powerset, S.sum (fun x => x) ≠ 11 := by
          fin_cases ha <;> fin_cases hb <;> decide
        exact key B (Finset.mem_powerset.mpr hBp) hBsum.symm

/-- For any practical number $n$, $h(n)$ ≤ number of divisors of $n$. -/
theorem practicalH_le_divisors (n : ℕ) (hn : Nat.IsPractical n) :
    practicalH n ≤ n.divisors.card := by
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  exact fun m ⟨_, hm⟩ => Nat.sInf_le ⟨n.divisors, Finset.Subset.refl _, rfl, hn m hm⟩

lemma e18_rep : ∀ n, 2 ≤ n → ∀ m, 1 ≤ m → m ≤ n.factorial →
    ∃ B : Finset ℕ, B ⊆ n.factorial.divisors ∧ B.card ≤ n - 1 ∧ m = ∑ i ∈ B, i := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro m hm1 hm2
    refine ⟨{m}, ?_, by simp, by simp⟩
    simp only [Finset.singleton_subset_iff, Nat.mem_divisors]
    refine ⟨?_, by simp [Nat.factorial]⟩
    have : m = 1 ∨ m = 2 := by simp [Nat.factorial] at hm2; omega
    rcases this with rfl | rfl <;> decide
  | succ n hn ih =>
    intro m hm1 hm2
    have hfpos : 0 < (n + 1).factorial := Nat.factorial_pos _
    set a := m / (n + 1)
    set b := m % (n + 1)
    have hm : m = (n + 1) * a + b := (Nat.div_add_mod m (n + 1)).symm
    have hb : b < n + 1 := Nat.mod_lt _ (by omega)
    have hbdvd : b ≠ 0 → b ∣ (n + 1).factorial := fun hb0 =>
      Nat.dvd_factorial (Nat.pos_of_ne_zero hb0) hb.le
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · refine ⟨{m}, ?_, by simp; omega, by simp⟩
      have hmb : m = b := by rw [hm, ha0]; ring
      have : b ≠ 0 := by omega
      simp only [Finset.singleton_subset_iff, Nat.mem_divisors]
      exact ⟨hmb ▸ hbdvd this, hfpos.ne'⟩
    · have ha2 : a ≤ n.factorial := by
        rw [Nat.factorial_succ] at hm2
        exact Nat.div_le_of_le_mul hm2
      obtain ⟨Ba, hBa, hBac, hBas⟩ := ih a ha0 ha2
      let Bs := Ba.image (fun d => (n + 1) * d)
      have hBsdisj : ∀ d ∈ Bs, b < d := by
        intro d hd
        obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
        have : 1 ≤ d' := Nat.pos_of_mem_divisors (hBa hd')
        nlinarith
      have hBs_sub : Bs ⊆ (n + 1).factorial.divisors := by
        intro d hd
        obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
        have hd'' := Nat.mem_divisors.mp (hBa hd')
        rw [Nat.mem_divisors]
        refine ⟨?_, hfpos.ne'⟩
        rw [Nat.factorial_succ]; exact Nat.mul_dvd_mul_left _ hd''.1
      have hBs_card : Bs.card = Ba.card :=
        Finset.card_image_of_injective _ (fun x y h => by simpa using h)
      have hBs_sum : ∑ i ∈ Bs, i = (n + 1) * a := by
        rw [Finset.sum_image (fun x _ y _ h => by simpa using h), ← Finset.mul_sum, ← hBas]
      by_cases hb0 : b = 0
      · refine ⟨Bs, hBs_sub, by omega, by rw [hBs_sum, hm, hb0, add_zero]⟩
      · have hbnot : b ∉ Bs := fun h => lt_irrefl b (hBsdisj b h)
        refine ⟨insert b Bs, Finset.insert_subset ?_ hBs_sub, ?_, ?_⟩
        · rw [Nat.mem_divisors]; exact ⟨hbdvd hb0, hfpos.ne'⟩
        · rw [Finset.card_insert_of_notMem hbnot]; omega
        · rw [Finset.sum_insert hbnot, hBs_sum, hm]; ring

theorem e18_main : ∀ᶠ n : ℕ in Filter.atTop, practicalH (Nat.factorial n) < n := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have h : practicalH n.factorial ≤ n - 1 := by
    apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨B, hB, hBc, hBs⟩ := e18_rep n hn m hm.1 hm.2
    exact (Nat.sInf_le (show B.card ∈ {k | ∃ D : Finset ℕ, D ⊆ n.factorial.divisors ∧ D.card = k ∧
      m ∈ subsetSums (D : Set ℕ)} from ⟨B, hB, rfl, B, subset_refl _, hBs⟩)).trans hBc
  omega

/--
**Erdős's Theorem.**
Erdős proved that $h(n!) < n$ for all $n \ge 1$.
-/
theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n := by
  exact e18_main


theorem factorial_isPractical (n : ℕ) : Nat.IsPractical n.factorial := by
  induction n with
  | zero =>
    intro m hm; simp at hm; interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ n ih =>
    intro m hm
    by_cases hle : m ≤ n.factorial
    · exact subsetSums_mono (by exact_mod_cast (Nat.divisors_subset_of_dvd
        (Nat.factorial_ne_zero _) (Nat.factorial_dvd_factorial n.le_succ))) (ih m hle)
    · push Not at hle; rw [Nat.factorial_succ] at hm
      set q := m / (n + 1); set r := m % (n + 1)
      have h_div : m = (n + 1) * q + r := (Nat.div_add_mod m (n + 1)).symm
      have h_r_lt : r < n + 1 := Nat.mod_lt m (Nat.succ_pos n)
      obtain ⟨B, hB_sub, hB_sum⟩ := ih q (Nat.div_le_of_le_mul (by linarith))
      have hdvd : ∀ d ∈ B, d * (n + 1) ∈ (n + 1).factorial.divisors := fun d hd => by
        refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
        rw [mul_comm, Nat.factorial_succ]
        exact mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors (by exact_mod_cast hB_sub hd))
      have hB'_sum : (B.image (· * (n + 1))).sum id = (n + 1) * q := by
        rw [Finset.sum_image (fun a _ b _ h => mul_right_cancel₀ (by omega) h)]
        simp [Finset.mul_sum, mul_comm, hB_sum]
      by_cases hr : r = 0
      · rw [show m = (B.image (· * (n + 1))).sum id from by rw [hB'_sum]; omega]
        exact ⟨_, fun x hx => by
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx; exact hdvd d hd, rfl⟩
      · have h_disj : Disjoint (B.image (· * (n + 1))) {r} := by
          rw [Finset.disjoint_singleton_right, Finset.mem_image]; rintro ⟨d, hd, hdr⟩
          have : 0 < d := Nat.pos_of_dvd_of_pos
            (Nat.dvd_of_mem_divisors (by exact_mod_cast hB_sub hd)) (Nat.factorial_pos n)
          have := le_mul_of_one_le_left (Nat.zero_le (n + 1)) this
          omega
        rw [show m = (B.image (· * (n + 1)) ∪ {r}).sum id from by
          rw [Finset.sum_union h_disj, Finset.sum_singleton, hB'_sum, id_eq]; exact h_div]
        exact ⟨_, fun x hx => by
          rcases Finset.mem_union.mp hx with h | h
          · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h; exact hdvd d hd
          · rw [Finset.mem_singleton.mp h]; exact Nat.mem_divisors.mpr
              ⟨(Nat.dvd_factorial (by omega) (by omega)).trans
                (Nat.factorial_dvd_factorial n.le_succ), Nat.factorial_ne_zero _⟩, rfl⟩

end Erdos18
