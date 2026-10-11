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

public import ModularInverseThresholds1180

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise Combinatorics.Additive
open Filter Topology Real Finset

namespace Erdos1180

/-!
# Additive-Energy Bilinear Covering and Asymmetric Prime-Block Bounds for Erdős #1180

This module proves Glibichuk's 8-fold bilinear covering theorem over `ZMod p` via additive energy
and Cauchy–Davenport, constructs prime-reciprocal fraction sets by induction on the block count,
establishes the master
asymmetric two-block bound `CAsymptotic ε ≤ 8 * k₁ * k₂`, and derives:
- the symmetric bound `CAsymptotic ε ≤ 8 * k ^ 2` for `k * ε > 1`,
- the `(1, k)` linear staircase bound `CAsymptotic ε ≤ 8 * k` for `k < (2 * k - 1) * ε`
  (giving `CAsymptotic ε ≤ 16` for `ε > 2 / 3` and `CAsymptotic ε ≤ 24` for `ε > 3 / 5`),
- the asymmetric staircase bound `CAsymptotic ε ≤ 8 * k * (k + 1)` for `(2 * k + 1) * ε > 2`
  (giving `CAsymptotic ε ≤ 16` for all `ε > 2 / 3`),
- the all-`ε` discrete bound `CAsymptotic ε ≤ 8 * (⌊ε⁻¹⌋₊ + 1) ^ 2` and the sharp asymptotic
  bound `CAsymptotic ε ≤ (8 + η) * ε⁻¹ ^ 2` as `ε → 0⁺`,
- the uniform bound `CAsymptotic ε ≤ 32 * ε⁻¹ ^ 2` on `(0, 1]`, and
- the resolutions of `erdos_1180`, `variants.glibichuk`, `variants.shparlinski`,
  `variants.lower_bound`, and `¬ Erdos1180OptimalConjecture`.
-/

/-! ## 1. Multiplicative and Additive Closure of `invSet` -/

theorem admissibleDenom_mul {δ₁ δ₂ : ℝ} {p m n : ℕ} (hp : 1 ≤ p)
    (hm : AdmissibleDenom δ₁ p m) (hn : AdmissibleDenom δ₂ p n) :
    AdmissibleDenom (δ₁ + δ₂) p (m * n) := by
  refine ⟨Nat.mul_pos hm.1 hn.1, ?_, hm.2.2.mul_left hn.2.2⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Nat.cast_mul, Real.rpow_add hp0]
  exact mul_le_mul hm.2.1 hn.2.1 (Nat.cast_nonneg n) (Real.rpow_nonneg hp0.le δ₁)

theorem invSet_mul_subset_invSet_add {δ₁ δ₂ : ℝ} {p : ℕ} (hp : p.Prime) :
    invSet δ₁ p * invSet δ₂ p ⊆ invSet (δ₁ + δ₂) p := by
  have : Fact p.Prime := ⟨hp⟩
  intro z hz
  rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
  obtain ⟨m, hm, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp ha
  obtain ⟨n, hn, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp hb
  rw [mem_invSet_iff_exists_admissibleDenom]
  refine ⟨m * n, admissibleDenom_mul hp.one_le hm hn, ?_⟩
  rw [Nat.cast_mul, mul_inv_rev, mul_comm]

theorem invSet_mono_eps {δ ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hδε : δ ≤ ε) :
    invSet δ p ⊆ invSet ε p := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp hz
  exact mem_invSet_iff_exists_admissibleDenom.mpr ⟨n, admissibleDenom_mono_eps hδε hp hn, rfl⟩

theorem add_subset_add {p : ℕ} {A₁ A₂ B₁ B₂ : Finset (ZMod p)}
    (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : A₁ + A₂ ⊆ B₁ + B₂ := by
  intro z hz
  rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, rfl⟩
  exact Finset.add_mem_add (h₁ ha) (h₂ hb)

theorem mul_subset_mul {p : ℕ} {A₁ A₂ B₁ B₂ : Finset (ZMod p)}
    (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : A₁ * A₂ ⊆ B₁ * B₂ := by
  intro z hz
  rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
  exact Finset.mul_mem_mul (h₁ ha) (h₂ hb)

theorem nsmul_subset_nsmul {p : ℕ} {A B : Finset (ZMod p)} (h : A ⊆ B) :
    ∀ k : ℕ, k • A ⊆ k • B
  | 0 => by simp
  | k + 1 => by
      rw [succ_nsmul, succ_nsmul]
      exact add_subset_add (nsmul_subset_nsmul h k) h

theorem singleton_mul_nsmul_subset {p : ℕ} {x : ZMod p} {S T : Finset (ZMod p)} (hx : x ∈ S) :
    ∀ k : ℕ, ({x} : Finset (ZMod p)) * (k • T) ⊆ k • (S * T)
  | 0 => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, _, b, hb, rfl⟩
      rw [zero_nsmul, Finset.mem_zero] at hb
      subst hb; simp
  | k + 1 => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
      rw [Finset.mem_singleton] at ha; subst ha
      rw [succ_nsmul, Finset.mem_add] at hb
      rcases hb with ⟨u, hu, v, hv, rfl⟩
      rw [mul_add, succ_nsmul]
      exact Finset.add_mem_add
        (singleton_mul_nsmul_subset hx k (Finset.mul_mem_mul (Finset.mem_singleton_self a) hu))
        (Finset.mul_mem_mul hx hv)

theorem nsmul_mul_nsmul_subset {p : ℕ} (S T : Finset (ZMod p)) :
    ∀ k₁ k₂ : ℕ, (k₁ • S) * (k₂ • T) ⊆ (k₁ * k₂) • (S * T)
  | 0, _ => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, ha, _, _, rfl⟩
      rw [zero_nsmul, Finset.mem_zero] at ha
      subst ha; simp
  | k₁ + 1, k₂ => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
      rw [succ_nsmul, Finset.mem_add] at ha
      rcases ha with ⟨u, hu, x, hx, rfl⟩
      rw [add_mul, add_mul, one_mul, add_nsmul]
      exact Finset.add_mem_add
        (nsmul_mul_nsmul_subset S T k₁ k₂ (Finset.mul_mem_mul hu hb))
        (singleton_mul_nsmul_subset hx k₂ (Finset.mul_mem_mul (Finset.mem_singleton_self x) hb))

/-! ## 2. Additive-Energy Unit-Dilate Bound and 8-Fold Bilinear Cover -/

section AdditiveEnergyCover
variable {p : ℕ}

theorem add_self_eq_univ_of_lt_two_mul_card [NeZero p] (hp : p.Prime)
    {S : Finset (ZMod p)} (hS : p < 2 * S.card) : S + S = univ := by
  have hne : S.Nonempty := card_pos.mp (by omega)
  have hcd := ZMod.cauchy_davenport hp hne hne
  apply eq_univ_of_card
  apply le_antisymm (card_le_univ _)
  rw [ZMod.card]
  exact (by omega : p ≤ min p (S.card + S.card - 1)).trans hcd

theorem zero_mem_add_self_of_lt_two_mul_card [NeZero p] (hp : p.Prime)
    {S : Finset (ZMod p)} (hS : p < 2 * S.card) : (0 : ZMod p) ∈ S + S := by
  rw [add_self_eq_univ_of_lt_two_mul_card hp hS]
  exact mem_univ 0

theorem card_sq_mul_card_sq_le_addEnergy (u : (ZMod p)ˣ) (U V : Finset (ZMod p)) :
    U.card ^ 2 * V.card ^ 2 ≤ (U + u • V).card * E[U, u • V] := by
  simpa [card_smul_finset] using le_card_add_mul_addEnergy U (u • V)

theorem addEnergy_unit_smul_eq (u : (ZMod p)ˣ) (U V : Finset (ZMod p)) :
    E[U, u • V] =
      #{w ∈ (U ×ˢ U) ×ˢ (V ×ˢ V) |
        w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2} := by
  classical
  unfold Finset.addEnergy
  let e : (ZMod p × ZMod p) × (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) × (ZMod p × ZMod p) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (MulAction.toPerm u) (MulAction.toPerm u))
  refine (card_equiv e ?_).symm
  rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  simp only [mem_filter, mem_product, e, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map,
    MulAction.toPerm_apply, smul_mem_smul_finset_iff]
  rfl

theorem addEnergy_neg_unit_smul (u : (ZMod p)ˣ) (U V : Finset (ZMod p)) :
    E[U, (-u) • V] = E[U, u • V] := by
  classical
  rw [addEnergy_unit_smul_eq, addEnergy_unit_smul_eq]
  refine card_equiv (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)) ?_
  rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  simp only [mem_filter, mem_product, Equiv.prodCongr_apply, Equiv.refl_apply,
    Equiv.prodComm_apply, Prod.map, Prod.fst_swap, Prod.snd_swap, Units.val_neg, neg_mul]
  refine and_congr (and_congr_right' and_comm) ?_
  constructor <;> intro h <;> linear_combination h

theorem unit_eq_div_of_linear_eq [Fact p.Prime] {u : (ZMod p)ˣ} {x₁ x₂ y₁ y₂ : ZMod p}
    (hy : y₁ ≠ y₂) (h : x₁ + (u : ZMod p) * y₁ = x₂ + (u : ZMod p) * y₂) :
    (u : ZMod p) = (x₂ - x₁) / (y₁ - y₂) :=
  (eq_div_iff (sub_ne_zero.mpr hy)).mpr (by linear_combination h)

theorem sum_units_addEnergy_le [NeZero p] (hp : p.Prime) (U V : Finset (ZMod p)) :
    (∑ u : (ZMod p)ˣ, E[U, u • V]) ≤
      (p - 1) * (U.card * V.card) + U.card ^ 2 * V.card ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Q := (U ×ˢ U) ×ˢ (V ×ˢ V)
  have hswap : (∑ u : (ZMod p)ˣ, E[U, u • V]) =
      ∑ w ∈ Q, #{u : (ZMod p)ˣ | w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2} := by
    simp_rw [addEnergy_unit_smul_eq, card_filter]
    exact sum_comm
  rw [hswap, ← sum_filter_add_sum_filter_not Q (fun w ↦ w ∈ U.diag ×ˢ V.diag)]
  have hsub : Q.filter (fun w ↦ w ∈ U.diag ×ˢ V.diag) ⊆ U.diag ×ˢ V.diag :=
    fun _ hw ↦ (mem_filter.mp hw).2
  have hdiag : (∑ w ∈ Q.filter (fun w ↦ w ∈ U.diag ×ˢ V.diag),
      #{u : (ZMod p)ˣ | w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2}) ≤
      (p - 1) * (U.card * V.card) := by
    calc
      _ ≤ ∑ _w ∈ Q.filter (fun w ↦ w ∈ U.diag ×ˢ V.diag), Fintype.card (ZMod p)ˣ :=
        sum_le_sum fun w _ ↦ card_le_univ _
      _ ≤ (U.diag ×ˢ V.diag).card * Fintype.card (ZMod p)ˣ := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_le_card hsub)
      _ = (p - 1) * (U.card * V.card) := by
        simp [ZMod.card_units_eq_totient, Nat.totient_prime hp, mul_comm]
  have hoff : (∑ w ∈ Q.filter (fun w ↦ w ∉ U.diag ×ˢ V.diag),
      #{u : (ZMod p)ˣ | w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2}) ≤
      U.card ^ 2 * V.card ^ 2 := by
    calc
      _ ≤ ∑ _w ∈ Q.filter (fun w ↦ w ∉ U.diag ×ˢ V.diag), 1 := by
        refine sum_le_sum fun w hw ↦ card_le_one.mpr fun u₁ hu₁ u₂ hu₂ ↦ ?_
        rcases mem_filter.mp hw with ⟨hwQ, hnot⟩
        rcases mem_product.mp hwQ with ⟨hxU, hyV⟩
        have eq₁ : w.1.1 + (u₁ : ZMod p) * w.2.1 = w.1.2 + (u₁ : ZMod p) * w.2.2 := (mem_filter.mp hu₁).2
        have eq₂ : w.1.1 + (u₂ : ZMod p) * w.2.1 = w.1.2 + (u₂ : ZMod p) * w.2.2 := (mem_filter.mp hu₂).2
        have hy : w.2.1 ≠ w.2.2 := by
          intro hy
          apply hnot
          rw [mem_product, mem_diag, mem_diag]
          refine ⟨⟨(mem_product.mp hxU).1, by linear_combination eq₁ - (u₁ : ZMod p) * hy⟩,
            ⟨(mem_product.mp hyV).1, hy⟩⟩
        exact Units.ext ((unit_eq_div_of_linear_eq hy eq₁).trans (unit_eq_div_of_linear_eq hy eq₂).symm)
      _ ≤ Q.card := by simp [card_filter_le]
      _ = U.card ^ 2 * V.card ^ 2 := by simp [Q, sq]
  exact add_le_add hdiag hoff

theorem exists_unit_smul_both_gt_half [NeZero p] (hp : p.Prime) (hp2 : 2 < p)
    (U V : Finset (ZMod p)) (hprod : p < U.card * V.card) :
    ∃ u : (ZMod p)ˣ, p < 2 * (U + u • V).card ∧ p < 2 * (U + (-u) • V).card := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcard_u : (univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hne : (univ : Finset (ZMod p)ˣ).Nonempty := card_pos.mp (by omega)
  have hsum : (∑ u : (ZMod p)ˣ, (p - 1) * E[U, u • V]) ≤
      ∑ _u : (ZMod p)ˣ, ((p - 1) * (U.card * V.card) + U.card ^ 2 * V.card ^ 2) := by
    rw [← mul_sum, sum_const, hcard_u, smul_eq_mul]
    exact Nat.mul_le_mul_left (p - 1) (sum_units_addEnergy_le hp U V)
  obtain ⟨u, _, hu⟩ := exists_le_of_sum_le hne hsum
  have hhalf : ∀ w : (ZMod p)ˣ,
      (p - 1) * E[U, w • V] ≤ (p - 1) * (U.card * V.card) + U.card ^ 2 * V.card ^ 2 →
        p < 2 * (U + w • V).card := by
    intro w hw
    by_contra hle
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    have hle1 : 2 * (U + w • V).card ≤ p - 1 := by omega
    have hcs := card_sq_mul_card_sq_le_addEnergy w U V
    have hmul : 2 * (U.card ^ 2 * V.card ^ 2) ≤ (p - 1) * E[U, w • V] := by
      calc
        2 * (U.card ^ 2 * V.card ^ 2) ≤ 2 * ((U + w • V).card * E[U, w • V]) :=
          Nat.mul_le_mul_left 2 hcs
        _ = (2 * (U + w • V).card) * E[U, w • V] := by ring
        _ ≤ (p - 1) * E[U, w • V] := Nat.mul_le_mul_right _ hle1
    have hsq : (U.card * V.card) ^ 2 = U.card ^ 2 * V.card ^ 2 := by ring
    nlinarith
  refine ⟨u, hhalf u hu, hhalf (-u) ?_⟩
  rwa [addEnergy_neg_unit_smul]

theorem unit_smul_subset_two_nsmul_mul_left (w : (ZMod p)ˣ) (U V : Finset (ZMod p))
    {y₁ y₂ : ZMod p} (hy₁ : y₁ ∈ V) (hy₂ : y₂ ∈ V) (hw : (w : ZMod p) = y₁ + y₂) :
    w • U ⊆ (2 : ℕ) • (U * V) := by
  intro z hz
  rcases mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  change (w : ZMod p) * x ∈ (2 : ℕ) • (U * V)
  rw [hw, add_mul, mul_comm y₁ x, mul_comm y₂ x, two_nsmul]
  exact add_mem_add (mul_mem_mul hx hy₁) (mul_mem_mul hx hy₂)

theorem unit_smul_subset_two_nsmul_mul_right (w : (ZMod p)ˣ) (U V : Finset (ZMod p))
    {x₁ x₂ : ZMod p} (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U) (hw : (w : ZMod p) = x₁ + x₂) :
    w • V ⊆ (2 : ℕ) • (U * V) := by
  intro z hz
  rcases mem_smul_finset.mp hz with ⟨y, hy, rfl⟩
  change (w : ZMod p) * y ∈ (2 : ℕ) • (U * V)
  rw [hw, add_mul, two_nsmul]
  exact add_mem_add (mul_mem_mul hx₁ hy) (mul_mem_mul hx₂ hy)

theorem val_mul_neg_eq_add_of_sum_eq_zero (w u : (ZMod p)ˣ) {x₁ x₂ y₁ y₂ : ZMod p}
    (hw : (w : ZMod p) = y₁ + y₂) (hsum0 : (x₁ + u • y₁) + (x₂ + u • y₂) = 0) :
    ((w * -u : (ZMod p)ˣ) : ZMod p) = x₁ + x₂ := by
  simp only [Units.val_mul, Units.val_neg, hw]
  simp only [Units.smul_def, smul_eq_mul] at hsum0
  linear_combination -hsum0

/-- **Glibichuk's 8-fold bilinear covering theorem**: for any odd prime `p > 2` and subsets
`U, V ⊆ ZMod p` with `p < U.card * V.card` and `∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ + y₂ ≠ 0`,
`(8 : ℕ) • (U * V) = univ`. -/
theorem eight_nsmul_mul_eq_univ [NeZero p] (hp : p.Prime) (hp2 : 2 < p)
    (U V : Finset (ZMod p)) (hprod : p < U.card * V.card)
    (hanti : ∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ + y₂ ≠ 0) :
    (8 : ℕ) • (U * V) = univ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu_pos, hu_neg⟩ := exists_unit_smul_both_gt_half hp hp2 U V hprod
  have h0 := zero_mem_add_self_of_lt_two_mul_card hp hu_pos
  rcases mem_add.mp h0 with ⟨a₁, ha₁, a₂, ha₂, hsum0⟩
  rcases mem_add.mp ha₁ with ⟨x₁, hx₁, z₁, hz₁, rfl⟩
  rcases mem_add.mp ha₂ with ⟨x₂, hx₂, z₂, hz₂, rfl⟩
  rcases mem_smul_finset.mp hz₁ with ⟨y₁, hy₁, rfl⟩
  rcases mem_smul_finset.mp hz₂ with ⟨y₂, hy₂, rfl⟩
  let w : (ZMod p)ˣ := Units.mk0 (y₁ + y₂) (hanti y₁ hy₁ y₂ hy₂)
  have hsub4 : w • (U + (-u) • V) ⊆ (4 : ℕ) • (U * V) := by
    rw [smul_add, ← mul_smul,
      show (4 : ℕ) • (U * V) = (2 : ℕ) • (U * V) + (2 : ℕ) • (U * V) by rw [← add_nsmul]]
    exact add_subset_add
      (unit_smul_subset_two_nsmul_mul_left w U V hy₁ hy₂ rfl)
      (unit_smul_subset_two_nsmul_mul_right (w * -u) U V hx₁ hx₂
        (val_mul_neg_eq_add_of_sum_eq_zero w u rfl hsum0))
  have hcard4 : p < 2 * ((4 : ℕ) • (U * V)).card := by
    have hle := card_le_card hsub4
    rw [card_smul_finset] at hle
    exact lt_of_lt_of_le hu_neg (Nat.mul_le_mul_left 2 hle)
  rw [show (8 : ℕ) • (U * V) = (4 : ℕ) • (U * V) + (4 : ℕ) • (U * V) by rw [← add_nsmul]]
  exact add_self_eq_univ_of_lt_two_mul_card hp hcard4

end AdditiveEnergyCover

/-! ## 3. Inductive Prime-Reciprocal Fraction Sets (`IsFracStage`) -/

section InductiveFractionStages

def extFrac (wq : (ℕ × ℕ) × ℕ) : ℕ × ℕ :=
  (wq.1.1 * wq.2 + wq.1.2, wq.1.2 * wq.2)

def evalFrac (p : ℕ) (w : ℕ × ℕ) : ZMod p :=
  (w.1 : ZMod p) * (w.2 : ZMod p)⁻¹

theorem extFrac_cross_eq_imp {P S Q : Finset ℕ} {F : Finset (ℕ × ℕ)}
    (hP_prime : ∀ q ∈ P, q.Prime)
    (hQ_sub : Q ⊆ P \ S)
    (hF_not_dvd : ∀ w ∈ F, ∀ r ∈ P \ S, ¬ r ∣ w.2)
    (hF_cross : ∀ w₁ ∈ F, ∀ w₂ ∈ F, w₁.1 * w₂.2 = w₂.1 * w₁.2 → w₁ = w₂)
    {wq₁ wq₂ : (ℕ × ℕ) × ℕ} (h₁ : wq₁ ∈ F ×ˢ Q) (h₂ : wq₂ ∈ F ×ˢ Q)
    (hcross : (extFrac wq₁).1 * (extFrac wq₂).2 = (extFrac wq₂).1 * (extFrac wq₁).2) :
    wq₁ = wq₂ := by
  rcases wq₁ with ⟨⟨a₁, b₁⟩, q₁⟩
  rcases wq₂ with ⟨⟨a₂, b₂⟩, q₂⟩
  rcases mem_product.mp h₁ with ⟨hw₁, hq₁Q⟩
  rcases mem_product.mp h₂ with ⟨hw₂, hq₂Q⟩
  dsimp [extFrac] at hcross
  have hq₁_sdiff : q₁ ∈ P \ S := hQ_sub hq₁Q
  have hq₂_sdiff : q₂ ∈ P \ S := hQ_sub hq₂Q
  have hq₁_prime : q₁.Prime := hP_prime q₁ (mem_sdiff.mp hq₁_sdiff).1
  have hq₂_prime : q₂.Prime := hP_prime q₂ (mem_sdiff.mp hq₂_sdiff).1
  have hnot_b₁ : ¬ q₁ ∣ b₁ := hF_not_dvd (a₁, b₁) hw₁ q₁ hq₁_sdiff
  have hnot_b₂ : ¬ q₁ ∣ b₂ := hF_not_dvd (a₂, b₂) hw₂ q₁ hq₁_sdiff
  have hdvd_rhs : q₁ ∣ (a₂ * q₂ + b₂) * (b₁ * q₁) :=
    ⟨(a₂ * q₂ + b₂) * b₁, by ring⟩
  rw [← hcross] at hdvd_rhs
  have hdvd_sum : q₁ ∣ q₁ * (a₁ * b₂ * q₂) + b₁ * b₂ * q₂ := by
    convert hdvd_rhs using 1; ring
  have hdvd_prod : q₁ ∣ b₁ * b₂ * q₂ :=
    (Nat.dvd_add_right ⟨a₁ * b₂ * q₂, rfl⟩).mp hdvd_sum
  have hdvd_q₂ : q₁ ∣ q₂ := by
    rcases hq₁_prime.dvd_mul.mp hdvd_prod with h12 | hq₂
    · rcases hq₁_prime.dvd_mul.mp h12 with hb₁ | hb₂
      · exact (hnot_b₁ hb₁).elim
      · exact (hnot_b₂ hb₂).elim
    · exact hq₂
  have hq_eq : q₁ = q₂ := (Nat.prime_dvd_prime_iff_eq hq₁_prime hq₂_prime).mp hdvd_q₂
  subst hq_eq
  have hq_pos : 0 < q₁ := hq₁_prime.pos
  have hsq_pos : 0 < q₁ * q₁ := Nat.mul_pos hq_pos hq_pos
  have hab_eq : a₁ * b₂ = a₂ * b₁ := by nlinarith
  have hw_eq : (a₁, b₁) = (a₂, b₂) := hF_cross (a₁, b₁) hw₁ (a₂, b₂) hw₂ hab_eq
  exact Prod.ext hw_eq rfl

def IsFracStage (p : ℕ) (δ : ℝ) (H L : ℕ) (P : Finset ℕ) (k : ℕ)
    (F : Finset (ℕ × ℕ)) (S : Finset ℕ) : Prop :=
  S ⊆ P ∧
  S.card = k * L ∧
  F.card = L ^ k ∧
  (∀ w ∈ F,
    (1 ≤ k → 1 ≤ w.1) ∧
    w.1 ≤ k * H ^ (k - 1) ∧
    1 ≤ w.2 ∧
    w.2 ≤ H ^ k ∧
    w.2.Coprime p ∧
    evalFrac p w ∈ k • invSet δ p ∧
    (∀ r ∈ P \ S, ¬ r ∣ w.2)) ∧
  (∀ w₁ ∈ F, ∀ w₂ ∈ F, w₁.1 * w₂.2 = w₂.1 * w₁.2 → w₁ = w₂)

theorem exists_fracStage {p H L : ℕ} {δ : ℝ} (hp : p.Prime)
    (P : Finset ℕ) (hP_prime : ∀ q ∈ P, q.Prime) (hP_le : ∀ q ∈ P, q ≤ H)
    (hHp : H < p) (hHδ : (H : ℝ) ≤ (p : ℝ) ^ δ) :
    ∀ k : ℕ, k * L ≤ P.card → ∃ F S, IsFracStage p δ H L P k F S
  | 0, _ => by
      refine ⟨{(0, 1)}, ∅, empty_subset P, by simp, by simp, ?_, ?_⟩
      · intro w hw
        rw [mem_singleton] at hw; subst hw
        refine ⟨by omega, by simp, le_rfl, by simp, Nat.coprime_one_left p, ?_, ?_⟩
        · simp [evalFrac]
        · intro r hr
          exact (hP_prime r (mem_sdiff.mp hr).1).not_dvd_one
      · intro w₁ hw₁ w₂ hw₂ _
        rw [mem_singleton] at hw₁ hw₂
        exact hw₁.trans hw₂.symm
  | k + 1, hkL => by
      classical
      have hkL_add : k * L + L ≤ P.card := by simpa [add_mul] using hkL
      have hkL' : k * L ≤ P.card := by omega
      obtain ⟨F, S, hS_sub, hS_card, hF_card, hF_mem, hF_cross⟩ :=
        exists_fracStage hp P hP_prime hP_le hHp hHδ k hkL'
      have hL_le : L ≤ (P \ S).card := by
        rw [card_sdiff_of_subset hS_sub, hS_card]
        omega
      obtain ⟨Q, hQ_sub, hQ_card⟩ := exists_subset_card_eq hL_le
      let F' := (F ×ˢ Q).image extFrac
      let S' := S ∪ Q
      have hdisj : Disjoint S Q :=
        disjoint_left.mpr fun x hxS hxQ ↦ (mem_sdiff.mp (hQ_sub hxQ)).2 hxS
      have hnot_dvd : ∀ w ∈ F, ∀ r ∈ P \ S, ¬ r ∣ w.2 :=
        fun w hw ↦ (hF_mem w hw).2.2.2.2.2.2
      have hinj : Set.InjOn extFrac ↑(F ×ˢ Q) := by
        intro wq₁ h₁ wq₂ h₂ heq
        apply extFrac_cross_eq_imp hP_prime hQ_sub hnot_dvd hF_cross h₁ h₂
        rw [heq]
      refine ⟨F', S', union_subset hS_sub (hQ_sub.trans sdiff_subset), ?_, ?_, ?_, ?_⟩
      · rw [card_union_of_disjoint hdisj, hS_card, hQ_card]; ring
      · rw [card_image_of_injOn hinj, card_product, hF_card, hQ_card, pow_succ]
      · intro z hz
        rcases mem_image.mp hz with ⟨⟨⟨a, b⟩, q⟩, hwq, rfl⟩
        rcases mem_product.mp hwq with ⟨hab, hqQ⟩
        rcases hF_mem (a, b) hab with ⟨_, ha_le, hb1, hb_le, hb_cop, heval, hnd⟩
        have hqP : q ∈ P := (mem_sdiff.mp (hQ_sub hqQ)).1
        have hq_prime : q.Prime := hP_prime q hqP
        have hq_le : q ≤ H := hP_le q hqP
        have hq_cop : q.Coprime p := by
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          exact Nat.not_dvd_of_pos_of_lt hq_prime.pos (lt_of_le_of_lt hq_le hHp)
        dsimp [extFrac]
        refine ⟨fun _ ↦ by omega, ?_, Nat.mul_pos hb1 hq_prime.pos, ?_, hb_cop.mul_left hq_cop, ?_, ?_⟩
        · by_cases hk0 : k = 0
          · subst hk0
            have ha0 : a = 0 := by simpa using ha_le
            have hb_eq1 : b = 1 := by
              have : b ≤ 1 := by simpa using hb_le
              omega
            subst ha0 hb_eq1; simp
          · have hpow : H ^ (k - 1) * H = H ^ k := by
              rw [← pow_succ]; congr 1; omega
            calc
              a * q + b ≤ (k * H ^ (k - 1)) * H + H ^ k :=
                Nat.add_le_add (Nat.mul_le_mul ha_le hq_le) hb_le
              _ = k * (H ^ (k - 1) * H) + H ^ k := by ring
              _ = (k + 1) * H ^ k := by rw [hpow]; ring
        · rw [pow_succ]
          exact Nat.mul_le_mul hb_le hq_le
        · have : Fact p.Prime := ⟨hp⟩
          have hb_ne : (b : ZMod p) ≠ 0 := by
            rw [ne_eq, ZMod.natCast_eq_zero_iff]
            exact fun hdvd ↦ Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdvd dvd_rfl hb_cop
          have hq_ne : (q : ZMod p) ≠ 0 := by
            rw [ne_eq, ZMod.natCast_eq_zero_iff]
            exact Nat.not_dvd_of_pos_of_lt hq_prime.pos (lt_of_le_of_lt hq_le hHp)
          have hfeq : evalFrac p (a * q + b, b * q) = evalFrac p (a, b) + (q : ZMod p)⁻¹ := by
            dsimp [evalFrac]
            push_cast
            field_simp [hb_ne, hq_ne]
          rw [hfeq, succ_nsmul]
          refine add_mem_add heval ?_
          rw [mem_invSet_iff_exists_admissibleDenom]
          exact ⟨q, ⟨hq_prime.one_le, (Nat.cast_le.mpr hq_le).trans hHδ, hq_cop⟩, rfl⟩
        · intro r hr
          have hr_sdiff : r ∈ P \ S := mem_sdiff.mpr ⟨(mem_sdiff.mp hr).1,
            fun hxS ↦ (mem_sdiff.mp hr).2 (mem_union_left Q hxS)⟩
          have hr_not_Q : r ∉ Q := fun hxQ ↦ (mem_sdiff.mp hr).2 (mem_union_right S hxQ)
          have hr_prime : r.Prime := hP_prime r (mem_sdiff.mp hr).1
          intro hdvd
          rcases hr_prime.dvd_mul.mp hdvd with hrb | hrq
          · exact hnd r hr_sdiff hrb
          · have hr_eq_q : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hrq
            exact hr_not_Q (hr_eq_q ▸ hqQ)
      · intro z₁ hz₁ z₂ hz₂ hcross
        rcases mem_image.mp hz₁ with ⟨wq₁, h₁, rfl⟩
        rcases mem_image.mp hz₂ with ⟨wq₂, h₂, rfl⟩
        rw [extFrac_cross_eq_imp hP_prime hQ_sub hnot_dvd hF_cross h₁ h₂ hcross]

theorem evalFrac_finset_of_isFracStage {p H L k : ℕ} {δ : ℝ} {F : Finset (ℕ × ℕ)} {P₀ S : Finset ℕ}
    [NeZero p] (hp : p.Prime) (hk : 1 ≤ k) (hclear : 2 * k * H ^ (2 * k - 1) < p)
    (hstage : IsFracStage p δ H L P₀ k F S) :
    (F.image (evalFrac p)) ⊆ k • invSet δ p ∧
    (F.image (evalFrac p)).card = L ^ k ∧
    (∀ y₁ ∈ F.image (evalFrac p), ∀ y₂ ∈ F.image (evalFrac p), y₁ + y₂ ≠ 0) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hstage with ⟨_, _, hF_card, hF_mem, hF_cross⟩
  have h2k : 2 * k * H ^ (2 * k - 1) = k * H ^ (2 * k - 1) + k * H ^ (2 * k - 1) := by ring
  have hcross_bound : ∀ w₁ ∈ F, ∀ w₂ ∈ F,
      1 ≤ w₁.1 * w₂.2 ∧ w₁.1 * w₂.2 ≤ k * H ^ (2 * k - 1) ∧ (w₁.2 : ZMod p) ≠ 0 := by
    intro w₁ hw₁ w₂ hw₂
    rcases hF_mem w₁ hw₁ with ⟨ha₁, ha₁_le, _, _, hb₁_cop, _, _⟩
    rcases hF_mem w₂ hw₂ with ⟨_, _, hb₂, hb₂_le, _, _, _⟩
    refine ⟨Nat.mul_pos (ha₁ hk) hb₂, ?_, ?_⟩
    · calc
        w₁.1 * w₂.2 ≤ (k * H ^ (k - 1)) * H ^ k := Nat.mul_le_mul ha₁_le hb₂_le
        _ = k * H ^ (2 * k - 1) := by rw [mul_assoc, ← pow_add]; congr 2; omega
    · rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact fun hdvd ↦ Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdvd dvd_rfl hb₁_cop
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases mem_image.mp hz with ⟨w, hw, rfl⟩
    exact (hF_mem w hw).2.2.2.2.2.1
  · have hinj : Set.InjOn (evalFrac p) ↑F := by
      intro w₁ hw₁ w₂ hw₂ heq
      rcases hcross_bound w₁ hw₁ w₂ hw₂ with ⟨_, hle₁, hb₁_ne⟩
      rcases hcross_bound w₂ hw₂ w₁ hw₁ with ⟨_, hle₂, hb₂_ne⟩
      have hcast : ((w₁.1 * w₂.2 : ℕ) : ZMod p) = ((w₂.1 * w₁.2 : ℕ) : ZMod p) := by
        dsimp [evalFrac] at heq
        push_cast
        exact (div_eq_div_iff hb₁_ne hb₂_ne).mp (by simpa [div_eq_mul_inv] using heq)
      have hval := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
      exact hF_cross w₁ hw₁ w₂ hw₂ hval
    rw [card_image_of_injOn hinj, hF_card]
  · intro y₁ hy₁ y₂ hy₂ hsum0
    rcases mem_image.mp hy₁ with ⟨w₁, hw₁, rfl⟩
    rcases mem_image.mp hy₂ with ⟨w₂, hw₂, rfl⟩
    rcases hcross_bound w₁ hw₁ w₂ hw₂ with ⟨hpos₁, hle₁, hb₁_ne⟩
    rcases hcross_bound w₂ hw₂ w₁ hw₁ with ⟨_, hle₂, hb₂_ne⟩
    have hcast : ((w₁.1 * w₂.2 + w₂.1 * w₁.2 : ℕ) : ZMod p) = 0 := by
      dsimp [evalFrac] at hsum0
      push_cast
      have hdiv : (w₁.1 : ZMod p) / (w₁.2 : ZMod p) + (w₂.1 : ZMod p) / (w₂.2 : ZMod p) = 0 := by
        simpa [div_eq_mul_inv] using hsum0
      rw [div_add_div _ _ hb₁_ne hb₂_ne, div_eq_zero_iff] at hdiv
      have hnum := hdiv.resolve_right (mul_ne_zero hb₁_ne hb₂_ne)
      linear_combination hnum
    have hval := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
    omega

end InductiveFractionStages

/-! ## 4. Pointwise Prime-Supply Bounds and Master Asymmetric `(k₁, k₂)` Bilinear Covering -/

theorem log_le_rpow_div {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    Real.log x ≤ x ^ r / r := by
  have h1 : Real.log (x ^ r) ≤ x ^ r - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx r)
  rw [Real.log_rpow hx] at h1
  rw [le_div_iff₀ hr, mul_comm]
  linarith

theorem pointwise_primeCounting_lower {n : ℕ} {t : ℝ} (hn : 2 ≤ n) (ht1 : t < 1) :
    (1 - t) * Real.log 2 * (n : ℝ) ^ t - 2 ≤ (Nat.primeCounting n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlog_succ : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
    have hle : (n : ℝ) + 1 ≤ (n : ℝ) ^ (2 : ℕ) := by
      have : n + 1 ≤ n ^ 2 := by nlinarith
      exact_mod_cast this
    calc
      Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ (2 : ℕ)) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have hlog_rpow : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 - t) / (1 - t) :=
    log_le_rpow_div hn_pos (sub_pos.mpr ht1)
  have hdiv : (1 - t) * Real.log 2 * (n : ℝ) ^ t ≤ (n : ℝ) * Real.log 2 / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hlog_pos]
    have hrpow : (n : ℝ) ^ t * (n : ℝ) ^ (1 - t) = (n : ℝ) := by
      rw [← Real.rpow_add hn_pos]; ring_nf; exact Real.rpow_one (n : ℝ)
    have hmul := mul_le_mul_of_nonneg_left hlog_rpow
      (by positivity : 0 ≤ (1 - t) * Real.log 2 * (n : ℝ) ^ t)
    calc
      (1 - t) * Real.log 2 * (n : ℝ) ^ t * Real.log (n : ℝ)
        ≤ (1 - t) * Real.log 2 * (n : ℝ) ^ t * ((n : ℝ) ^ (1 - t) / (1 - t)) := hmul
      _ = Real.log 2 * ((n : ℝ) ^ t * (n : ℝ) ^ (1 - t)) := by
          have hne : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
          field_simp [hne]
      _ = (n : ℝ) * Real.log 2 := by rw [hrpow, mul_comm]
  have hcheb := Chebyshev.pi_ge n
  have hstep : (n : ℝ) * Real.log 2 / Real.log (n : ℝ) - 2 ≤
      ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) := by
    rw [sub_div]
    have : Real.log ((n : ℝ) + 1) / Real.log (n : ℝ) ≤ 2 :=
      (div_le_iff₀ hlog_pos).mpr hlog_succ
    linarith
  linarith

theorem rpow_gt_const_atTop {r : ℝ} (hr : 0 < r) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ r := by
  let M : ℝ := (max 1 C) ^ r⁻¹
  filter_upwards [eventually_gt_atTop ⌊M⌋₊] with n hn
  have hM_lt : M < (n : ℝ) := Nat.lt_of_floor_lt hn
  have hM_nonneg : 0 ≤ M := by dsimp [M]; positivity
  have hrpow : (max 1 C) = M ^ r := by
    dsimp [M]
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hr.ne', Real.rpow_one]
  calc
    C ≤ max 1 C := le_max_right 1 C
    _ = M ^ r := hrpow
    _ < (n : ℝ) ^ r := Real.rpow_lt_rpow hM_nonneg hM_lt hr

theorem mul_rpow_lt_rpow_atTop {a b C : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  filter_upwards [rpow_gt_const_atTop (sub_pos.mpr hab) C, eventually_gt_atTop 0] with n hn hnpos
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hnpos
  calc
    C * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hn (Real.rpow_pos_of_pos hn_pos a)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hn_pos]; congr 1; ring

theorem eventually_ceil_block_admissible {k : ℕ} {δ γ : ℝ}
    (hγ : 0 < γ) (hγδ : γ < δ) (hδ1 : δ < 1)
    (hclear : ((2 * k - 1 : ℕ) : ℝ) * δ < 1) :
    ∀ᶠ n : ℕ in atTop,
      ⌊(n : ℝ) ^ δ⌋₊ < n ∧
      2 * k * ⌊(n : ℝ) ^ δ⌋₊ ^ (2 * k - 1) < n ∧
      k * ⌈(n : ℝ) ^ γ⌉₊ ≤ (Nat.primesLE ⌊(n : ℝ) ^ δ⌋₊).card := by
  have hδ : 0 < δ := lt_trans hγ hγδ
  let t : ℝ := (γ + δ) / (2 * δ)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have h1t : 0 < 1 - t := by
    have : 1 - t = (δ - γ) / (2 * δ) := by dsimp [t]; field_simp [hδ.ne']; ring
    rw [this]; exact div_pos (sub_pos.mpr hγδ) (by positivity)
  have ht1 : t < 1 := sub_pos.mp h1t
  have hδt : δ * t = (γ + δ) / 2 := by dsimp [t]; field_simp [hδ.ne']
  have hγ_lt : γ < δ * t := by linarith
  let c₀ : ℝ := (1 - t) * Real.log 2 / (2 : ℝ) ^ t
  have hc₀ : 0 < c₀ := by dsimp [c₀]; have := Real.log_pos one_lt_two; positivity
  have h1 := mul_rpow_lt_rpow_atTop (C := 1) hδ1
  have h2 := mul_rpow_lt_rpow_atTop (C := (2 * k : ℝ))
    (a := δ * (2 * k - 1 : ℕ)) (b := 1) (by simpa [mul_comm] using hclear)
  have h3 := rpow_gt_const_atTop hδ 2
  have h4 := mul_rpow_lt_rpow_atTop (C := (2 * (k : ℝ) + 2) / c₀) hγ_lt
  filter_upwards [h1, h2, h3, h4, eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4 hnpos
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hfl_δ : (⌊(n : ℝ) ^ δ⌋₊ : ℝ) ≤ (n : ℝ) ^ δ := Nat.floor_le (by positivity)
  have hcl_γ : (⌈(n : ℝ) ^ γ⌉₊ : ℝ) ≤ (n : ℝ) ^ γ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  refine ⟨?_, ?_, ?_⟩
  · have : (⌊(n : ℝ) ^ δ⌋₊ : ℝ) < (n : ℝ) := hfl_δ.trans_lt (by simpa using hn1)
    exact_mod_cast this
  · have hpow_le : (⌊(n : ℝ) ^ δ⌋₊ : ℝ) ^ (2 * k - 1) ≤ (n : ℝ) ^ (δ * (2 * k - 1 : ℕ)) := by
      rw [Real.rpow_mul hn_pos.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) hfl_δ _
    have hlt_n : (2 * k : ℝ) * (⌊(n : ℝ) ^ δ⌋₊ : ℝ) ^ (2 * k - 1) < (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hpow_le (by positivity : (0 : ℝ) ≤ 2 * k)
      exact (hmul.trans_lt hn2).trans_eq (Real.rpow_one (n : ℝ))
    exact_mod_cast hlt_n
  · have hH2 : 2 ≤ ⌊(n : ℝ) ^ δ⌋₊ := Nat.le_floor hn3.le
    have hcheb := pointwise_primeCounting_lower hH2 ht1
    have hsub1 : (n : ℝ) ^ δ - 1 < (⌊(n : ℝ) ^ δ⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hlow : (n : ℝ) ^ δ / 2 ≤ (⌊(n : ℝ) ^ δ⌋₊ : ℝ) := by linarith
    have hlow_t : ((n : ℝ) ^ δ / 2) ^ t ≤ (⌊(n : ℝ) ^ δ⌋₊ : ℝ) ^ t :=
      Real.rpow_le_rpow (by positivity) hlow ht0.le
    have hc₀_mul : c₀ * (n : ℝ) ^ (δ * t) ≤ (1 - t) * Real.log 2 * (⌊(n : ℝ) ^ δ⌋₊ : ℝ) ^ t := by
      have hid : c₀ * (n : ℝ) ^ (δ * t) = (1 - t) * Real.log 2 * ((n : ℝ) ^ δ / 2) ^ t := by
        dsimp [c₀]
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn_pos.le]
        ring
      rw [hid]
      have : 0 ≤ (1 - t) * Real.log 2 := by have := Real.log_pos one_lt_two; positivity
      exact mul_le_mul_of_nonneg_left hlow_t this
    have h1_γ : (1 : ℝ) ≤ (n : ℝ) ^ γ := Real.one_le_rpow (by exact_mod_cast hnpos) hγ.le
    rw [div_mul_eq_mul_div, div_lt_iff₀ hc₀] at hn4
    have hreal : ((k * ⌈(n : ℝ) ^ γ⌉₊ : ℕ) : ℝ) ≤ Nat.primeCounting ⌊(n : ℝ) ^ δ⌋₊ := by
      calc
        ((k * ⌈(n : ℝ) ^ γ⌉₊ : ℕ) : ℝ) = (k : ℝ) * (⌈(n : ℝ) ^ γ⌉₊ : ℝ) := by push_cast; ring
        _ ≤ (k : ℝ) * ((n : ℝ) ^ γ + 1) := by gcongr
        _ ≤ 2 * (k : ℝ) * (n : ℝ) ^ γ := by nlinarith
        _ ≤ (Nat.primeCounting ⌊(n : ℝ) ^ δ⌋₊ : ℝ) := by linarith
    rw [Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast hreal

theorem exists_ceil_block_finset {k p : ℕ} {δ γ : ℝ} [NeZero p]
    (hp : p.Prime) (hk : 1 ≤ k)
    (hready : ⌊(p : ℝ) ^ δ⌋₊ < p ∧
      2 * k * ⌊(p : ℝ) ^ δ⌋₊ ^ (2 * k - 1) < p ∧
      k * ⌈(p : ℝ) ^ γ⌉₊ ≤ (Nat.primesLE ⌊(p : ℝ) ^ δ⌋₊).card) :
    ∃ U : Finset (ZMod p),
      U ⊆ k • invSet δ p ∧
      U.card = ⌈(p : ℝ) ^ γ⌉₊ ^ k ∧
      ∀ y₁ ∈ U, ∀ y₂ ∈ U, y₁ + y₂ ≠ 0 := by
  rcases hready with ⟨hHlt, hclear, hsupply⟩
  have hHδ : (⌊(p : ℝ) ^ δ⌋₊ : ℝ) ≤ (p : ℝ) ^ δ := Nat.floor_le (by positivity)
  obtain ⟨F, S, hstage⟩ := exists_fracStage hp (Nat.primesLE ⌊(p : ℝ) ^ δ⌋₊)
    (fun _ hq ↦ Nat.prime_of_mem_primesLE hq)
    (fun _ hq ↦ Nat.le_of_mem_primesLE hq) hHlt hHδ k hsupply
  exact ⟨F.image (evalFrac p), evalFrac_finset_of_isFracStage hp hk hclear hstage⟩

theorem lt_ceil_rpow_pow_mul {k₁ k₂ n : ℕ} {γ₁ γ₂ : ℝ}
    (hn : 2 ≤ n) (hsum : 1 < (k₁ : ℝ) * γ₁ + (k₂ : ℝ) * γ₂) :
    n < ⌈(n : ℝ) ^ γ₁⌉₊ ^ k₁ * ⌈(n : ℝ) ^ γ₂⌉₊ ^ k₂ := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by positivity
  have hlt : (n : ℝ) < (n : ℝ) ^ ((k₁ : ℝ) * γ₁ + (k₂ : ℝ) * γ₂) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hn1 hsum
  have hpow_eq : (n : ℝ) ^ ((k₁ : ℝ) * γ₁ + (k₂ : ℝ) * γ₂) =
      ((n : ℝ) ^ γ₁) ^ k₁ * ((n : ℝ) ^ γ₂) ^ k₂ := by
    rw [Real.rpow_add hn0, mul_comm (k₁ : ℝ), mul_comm (k₂ : ℝ),
      Real.rpow_mul hn0.le, Real.rpow_mul hn0.le, Real.rpow_natCast, Real.rpow_natCast]
  have hle₁ : ((n : ℝ) ^ γ₁) ^ k₁ ≤ (⌈(n : ℝ) ^ γ₁⌉₊ : ℝ) ^ k₁ :=
    pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) k₁
  have hle₂ : ((n : ℝ) ^ γ₂) ^ k₂ ≤ (⌈(n : ℝ) ^ γ₂⌉₊ : ℝ) ^ k₂ :=
    pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) k₂
  have hmul : ((n : ℝ) ^ γ₁) ^ k₁ * ((n : ℝ) ^ γ₂) ^ k₂ ≤
      (⌈(n : ℝ) ^ γ₁⌉₊ : ℝ) ^ k₁ * (⌈(n : ℝ) ^ γ₂⌉₊ : ℝ) ^ k₂ :=
    mul_le_mul hle₁ hle₂ (by positivity) (by positivity)
  have hreal : (n : ℝ) < ((⌈(n : ℝ) ^ γ₁⌉₊ ^ k₁ * ⌈(n : ℝ) ^ γ₂⌉₊ ^ k₂ : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast hreal

/-- **Master asymmetric two-block bilinear covering theorem**: whenever `k₁, k₂ ≥ 1` and
`δ₁, δ₂ > 0` satisfy `(2k₁ - 1)δ₁ < 1`, `(2k₂ - 1)δ₂ < 1`, `δ₁ + δ₂ ≤ ε`, and
`1 < k₁ δ₁ + k₂ δ₂`, we have `8 * k₁ * k₂ ∈ AsymptoticBoundSet ε`. -/
theorem eight_mul_mul_mem_asymptoticBoundSet {ε δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hclear₁ : ((2 * k₁ - 1 : ℕ) : ℝ) * δ₁ < 1)
    (hclear₂ : ((2 * k₂ - 1 : ℕ) : ℝ) * δ₂ < 1)
    (hsum_le : δ₁ + δ₂ ≤ ε)
    (hgrow : 1 < (k₁ : ℝ) * δ₁ + (k₂ : ℝ) * δ₂) :
    8 * k₁ * k₂ ∈ AsymptoticBoundSet ε := by
  let S : ℝ := (k₁ : ℝ) * δ₁ + (k₂ : ℝ) * δ₂
  have hS_pos : 0 < S := lt_trans zero_lt_one hgrow
  let r : ℝ := (1 + S) / (2 * S)
  have hr_pos : 0 < r := div_pos (by linarith) (by linarith)
  have hr_lt_one : r < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let γ₁ : ℝ := r * δ₁
  let γ₂ : ℝ := r * δ₂
  have hγ₁_pos : 0 < γ₁ := mul_pos hr_pos hδ₁
  have hγ₂_pos : 0 < γ₂ := mul_pos hr_pos hδ₂
  have hγ₁_lt : γ₁ < δ₁ := by dsimp [γ₁]; nlinarith
  have hγ₂_lt : γ₂ < δ₂ := by dsimp [γ₂]; nlinarith
  have hδ₁_lt_one : δ₁ < 1 := by
    have : (1 : ℝ) ≤ ((2 * k₁ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k₁ - 1)
    nlinarith
  have hδ₂_lt_one : δ₂ < 1 := by
    have : (1 : ℝ) ≤ ((2 * k₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k₂ - 1)
    nlinarith
  have hγ_grow : 1 < (k₁ : ℝ) * γ₁ + (k₂ : ℝ) * γ₂ := by
    have hid : (k₁ : ℝ) * γ₁ + (k₂ : ℝ) * γ₂ = (1 + S) / 2 := by
      dsimp [γ₁, γ₂, r, S]; field_simp [hS_pos.ne']
    linarith
  have hev := (eventually_gt_atTop 2).and
    ((eventually_ceil_block_admissible hγ₁_pos hγ₁_lt hδ₁_lt_one hclear₁).and
      (eventually_ceil_block_admissible hγ₂_pos hγ₂_lt hδ₂_lt_one hclear₂))
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.1 hev
  refine ⟨P₀, fun p hpP₀ hp a ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases hP₀ p hpP₀ with ⟨hp2, hready₁, hready₂⟩
  obtain ⟨U₁, hU₁_sub, hU₁_card, _⟩ := exists_ceil_block_finset hp hk₁ hready₁
  obtain ⟨U₂, hU₂_sub, hU₂_card, hU₂_anti⟩ := exists_ceil_block_finset hp hk₂ hready₂
  have hprod : p < U₁.card * U₂.card := by
    rw [hU₁_card, hU₂_card]
    exact lt_ceil_rpow_pow_mul hp.two_le hγ_grow
  have hcover : (8 : ℕ) • (U₁ * U₂) = univ :=
    eight_nsmul_mul_eq_univ hp hp2 U₁ U₂ hprod hU₂_anti
  have hsub : (8 : ℕ) • (U₁ * U₂) ⊆ (8 * k₁ * k₂) • invSet ε p := by
    calc
      (8 : ℕ) • (U₁ * U₂)
        ⊆ (8 : ℕ) • ((k₁ • invSet δ₁ p) * (k₂ • invSet δ₂ p)) :=
          nsmul_subset_nsmul (mul_subset_mul hU₁_sub hU₂_sub) 8
      _ ⊆ (8 : ℕ) • ((k₁ * k₂) • (invSet δ₁ p * invSet δ₂ p)) :=
          nsmul_subset_nsmul (nsmul_mul_nsmul_subset _ _ k₁ k₂) 8
      _ ⊆ (8 : ℕ) • ((k₁ * k₂) • invSet (δ₁ + δ₂) p) :=
          nsmul_subset_nsmul (nsmul_subset_nsmul (invSet_mul_subset_invSet_add hp) (k₁ * k₂)) 8
      _ ⊆ (8 : ℕ) • ((k₁ * k₂) • invSet ε p) :=
          nsmul_subset_nsmul (nsmul_subset_nsmul (invSet_mono_eps hp.one_le hsum_le) (k₁ * k₂)) 8
      _ = (8 * k₁ * k₂) • invSet ε p := by rw [← mul_nsmul', mul_assoc]
  have ha : a ∈ (8 * k₁ * k₂) • invSet ε p := hsub (by rw [hcover]; exact mem_univ a)
  obtain ⟨s, hcard, hrep⟩ := exists_represents_card_eq_of_mem_nsmul_invSet (8 * k₁ * k₂) ha
  exact ⟨s, hcard.le, hrep⟩

theorem CAsymptotic_le_eight_mul_mul {ε δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hclear₁ : ((2 * k₁ - 1 : ℕ) : ℝ) * δ₁ < 1)
    (hclear₂ : ((2 * k₂ - 1 : ℕ) : ℝ) * δ₂ < 1)
    (hsum_le : δ₁ + δ₂ ≤ ε)
    (hgrow : 1 < (k₁ : ℝ) * δ₁ + (k₂ : ℝ) * δ₂) :
    CAsymptotic ε ≤ 8 * k₁ * k₂ :=
  Nat.sInf_le (eight_mul_mul_mem_asymptoticBoundSet hk₁ hk₂ hδ₁ hδ₂ hclear₁ hclear₂ hsum_le hgrow)

/-! ## 5. Symmetric `8 k²`, Asymmetric `8 k (k + 1)`, Discrete `8 (⌊ε⁻¹⌋₊ + 1)²`, and `(8 + η) ε⁻²` Bounds -/

theorem exists_symmetric_delta_of_one_lt_mul {ε : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 1 ≤ k) (hkε : 1 < (k : ℝ) * ε) :
    ∃ δ : ℝ,
      0 < δ ∧
      ((2 * k - 1 : ℕ) : ℝ) * δ < 1 ∧
      δ + δ ≤ ε ∧
      1 < (k : ℝ) * δ + (k : ℝ) * δ := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hdiv : 1 / (2 * (k : ℝ)) < ε / 2 := by
    rw [div_lt_div_iff₀ (by positivity) zero_lt_two]; linarith
  let η : ℝ := min (ε / 2 - 1 / (2 * (k : ℝ))) (1 / (4 * (k : ℝ) ^ 2))
  have hη_pos : 0 < η := lt_min (sub_pos.mpr hdiv) (by positivity)
  have hη_sub : η ≤ ε / 2 - 1 / (2 * (k : ℝ)) := min_le_left _ _
  have hη_inv : η ≤ 1 / (4 * (k : ℝ) ^ 2) := min_le_right _ _
  have hη_mul : 4 * (k : ℝ) ^ 2 * η ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hη_inv (by positivity : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2)
    rwa [mul_one_div_cancel (by positivity)] at this
  let δ : ℝ := 1 / (2 * (k : ℝ)) + η
  refine ⟨δ, by dsimp [δ]; positivity, ?_, by dsimp [δ]; linarith, ?_⟩
  · have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; push_cast; ring
    rw [hcast]
    have hid : 2 * (k : ℝ) * ((2 * (k : ℝ) - 1) * δ) =
        2 * (k : ℝ) - 1 + 2 * (k : ℝ) * (2 * (k : ℝ) - 1) * η := by
      dsimp [δ]; field_simp [hk_pos.ne']
    nlinarith
  · have hid : (k : ℝ) * δ + (k : ℝ) * δ = 1 + 2 * (k : ℝ) * η := by
      dsimp [δ]; field_simp [hk_pos.ne']; ring
    nlinarith

theorem eight_mul_sq_mem_asymptoticBoundSet_of_one_lt_mul {ε : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 1 ≤ k) (hkε : 1 < (k : ℝ) * ε) :
    8 * k ^ 2 ∈ AsymptoticBoundSet ε := by
  obtain ⟨δ, hδ_pos, hclear, hsum, hgrow⟩ := exists_symmetric_delta_of_one_lt_mul hε hk hkε
  have hmem := eight_mul_mul_mem_asymptoticBoundSet (ε := ε) hk hk hδ_pos hδ_pos hclear hclear hsum hgrow
  rwa [show 8 * k * k = 8 * k ^ 2 by ring] at hmem

theorem CAsymptotic_le_eight_mul_sq_of_one_lt_mul {ε : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 1 ≤ k) (hkε : 1 < (k : ℝ) * ε) :
    CAsymptotic ε ≤ 8 * k ^ 2 :=
  Nat.sInf_le (eight_mul_sq_mem_asymptoticBoundSet_of_one_lt_mul hε hk hkε)

theorem exists_asymmetric_deltas_of_two_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : 2 < (2 * (k : ℝ) + 1) * ε) :
    ∃ δ₁ δ₂ : ℝ,
      0 < δ₁ ∧ 0 < δ₂ ∧
      ((2 * k - 1 : ℕ) : ℝ) * δ₁ < 1 ∧
      ((2 * (k + 1) - 1 : ℕ) : ℝ) * δ₂ < 1 ∧
      δ₁ + δ₂ ≤ ε ∧
      1 < (k : ℝ) * δ₁ + ((k + 1 : ℕ) : ℝ) * δ₂ := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let m : ℝ := 2 * (k : ℝ) + 1
  have hm_pos : 0 < m := by dsimp [m]; linarith
  have hdiv : 2 / m < ε := (div_lt_iff₀ hm_pos).mpr (by dsimp [m]; linarith)
  let η : ℝ := min (ε - 2 / m) (1 / m ^ 2)
  have hη_pos : 0 < η := lt_min (sub_pos.mpr hdiv) (by positivity)
  have hη_le_sub : η ≤ ε - 2 / m := min_le_left _ _
  have hη_le_inv : η ≤ 1 / m ^ 2 := min_le_right _ _
  let δ₁ : ℝ := 1 / m + (3 / 2) * η
  let δ₂ : ℝ := 1 / m - (1 / 2) * η
  have hη_mul : η * m ^ 2 ≤ 1 := (le_div_iff₀ (by positivity)).mp hη_le_inv
  have hδ₁_pos : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hδ₂_pos : 0 < δ₂ := by
    have : (1 / 2) * η * m ^ 2 < m := by dsimp [m]; nlinarith
    have : (1 / 2) * η < 1 / m := by
      rw [lt_div_iff₀ hm_pos]
      nlinarith
    dsimp [δ₂]; linarith
  have hδ₁_clear : ((2 * k - 1 : ℕ) : ℝ) * δ₁ < 1 := by
    have hcast : ((2 * k - 1 : ℕ) : ℝ) = m - 2 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; dsimp [m]; push_cast; ring
    rw [hcast]
    have hid : ((m - 2) * δ₁) * m ^ 2 = (m - 2) * m + (3 / 2) * (m - 2) * (η * m ^ 2) := by
      dsimp [δ₁]; field_simp [hm_pos.ne']
    have hlt : ((m - 2) * δ₁) * m ^ 2 < 1 * m ^ 2 := by dsimp [m] at hid ⊢; nlinarith
    exact lt_of_mul_lt_mul_right hlt (by positivity)
  have hδ₂_clear : ((2 * (k + 1) - 1 : ℕ) : ℝ) * δ₂ < 1 := by
    have hcast : ((2 * (k + 1) - 1 : ℕ) : ℝ) = m := by
      have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [this]; dsimp [m]; push_cast; ring
    rw [hcast]
    have hid : m * δ₂ = 1 - (1 / 2) * η * m := by dsimp [δ₂]; field_simp [hm_pos.ne']
    nlinarith
  have hsum : δ₁ + δ₂ ≤ ε := by
    have : δ₁ + δ₂ = 2 / m + η := by dsimp [δ₁, δ₂]; ring
    linarith
  have hgrow : 1 < (k : ℝ) * δ₁ + ((k + 1 : ℕ) : ℝ) * δ₂ := by
    push_cast
    have hid : (k : ℝ) * δ₁ + ((k : ℝ) + 1) * δ₂ = 1 + ((2 * (k : ℝ) - 1) / 2) * η := by
      dsimp [δ₁, δ₂, m]; field_simp [hm_pos.ne']; ring
    nlinarith
  exact ⟨δ₁, δ₂, hδ₁_pos, hδ₂_pos, hδ₁_clear, hδ₂_clear, hsum, hgrow⟩

theorem eight_mul_succ_mem_asymptoticBoundSet_of_two_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : 2 < (2 * (k : ℝ) + 1) * ε) :
    8 * k * (k + 1) ∈ AsymptoticBoundSet ε := by
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hclear₁, hclear₂, hsum, hgrow⟩ :=
    exists_asymmetric_deltas_of_two_lt_mul hk hkε
  exact eight_mul_mul_mem_asymptoticBoundSet hk (by omega) hδ₁ hδ₂ hclear₁ hclear₂ hsum hgrow

/-- **Asymmetric `(k, k + 1)` staircase bound**: for every `k ≥ 1` and `(2k + 1) ε > 2`,
`CAsymptotic ε ≤ 8 * k * (k + 1)`. -/
theorem CAsymptotic_le_eight_mul_succ_of_two_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : 2 < (2 * (k : ℝ) + 1) * ε) :
    CAsymptotic ε ≤ 8 * k * (k + 1) :=
  Nat.sInf_le (eight_mul_succ_mem_asymptoticBoundSet_of_two_lt_mul hk hkε)

theorem exists_one_k_deltas_of_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hkε : (k : ℝ) < (2 * (k : ℝ) - 1) * ε) (hε1 : ε < 1) :
    ∃ δ₁ δ₂ : ℝ,
      0 < δ₁ ∧ 0 < δ₂ ∧
      ((2 * 1 - 1 : ℕ) : ℝ) * δ₁ < 1 ∧
      ((2 * k - 1 : ℕ) : ℝ) * δ₂ < 1 ∧
      δ₁ + δ₂ ≤ ε ∧
      1 < (1 : ℝ) * δ₁ + (k : ℝ) * δ₂ := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have h2k1_pos : (0 : ℝ) < 2 * (k : ℝ) - 1 := by linarith
  let L : ℝ := (1 - ε) / ((k : ℝ) - 1)
  let U : ℝ := 1 / (2 * (k : ℝ) - 1)
  have hL_pos : 0 < L := div_pos (by linarith) hkm1_pos
  have hLU : L < U := by
    dsimp [L, U]
    rw [div_lt_div_iff₀ hkm1_pos h2k1_pos]
    nlinarith
  let δ₂ : ℝ := (L + U) / 2
  let δ₁ : ℝ := ε - δ₂
  have hL_lt : L < δ₂ := by dsimp [δ₂]; linarith
  have hδ₂_lt : δ₂ < U := by dsimp [δ₂]; linarith
  have hδ₂_pos : 0 < δ₂ := lt_trans hL_pos hL_lt
  have hU_lt_ε : U < ε := (div_lt_iff₀ h2k1_pos).mpr (by linarith)
  have hδ₁_pos : 0 < δ₁ := by dsimp [δ₁]; linarith
  refine ⟨δ₁, δ₂, hδ₁_pos, hδ₂_pos, ?_, ?_, by dsimp [δ₁]; linarith, ?_⟩
  · push_cast; dsimp [δ₁]; linarith
  · have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; push_cast; ring
    have hmul : δ₂ * (2 * (k : ℝ) - 1) < 1 := (lt_div_iff₀ h2k1_pos).mp hδ₂_lt
    rw [hcast]; linarith
  · have hmul : 1 - ε < δ₂ * ((k : ℝ) - 1) := (div_lt_iff₀ hkm1_pos).mp hL_lt
    dsimp [δ₁]; linarith

/-- **Asymmetric `(1, k)` linear staircase bound**: for every `k ≥ 1` and `k < (2k - 1) ε`,
`CAsymptotic ε ≤ 8 * k`. -/
theorem CAsymptotic_le_eight_mul_of_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : (k : ℝ) < (2 * (k : ℝ) - 1) * ε) :
    CAsymptotic ε ≤ 8 * k := by
  by_cases hε1 : 1 ≤ ε
  · rw [CAsymptotic_eq_one_of_one_le hε1]; omega
  · push Not at hε1
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk_eq : k = 1 := by omega
      subst hk_eq; norm_num at hkε; linarith
    obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hclear₁, hclear₂, hsum, hgrow⟩ :=
      exists_one_k_deltas_of_lt_mul hk2 hkε hε1
    have h := CAsymptotic_le_eight_mul_mul le_rfl hk hδ₁ hδ₂ hclear₁ hclear₂ hsum (by simpa using hgrow)
    simpa using h

/-- **Sub-32 bound on `(2/3, ∞)`**: for every `ε > 2 / 3`, `CAsymptotic ε ≤ 16`. -/
theorem CAsymptotic_le_sixteen_of_two_thirds_lt {ε : ℝ} (hε : 2 / 3 < ε) :
    CAsymptotic ε ≤ 16 := by
  have h := CAsymptotic_le_eight_mul_of_lt_mul (ε := ε) (k := 2) (by omega) (by push_cast; linarith)
  simpa using h

/-- **Discrete all-`ε` Glibichuk bound**: for every `ε > 0`,
`CAsymptotic ε ≤ 8 * (⌊ε⁻¹⌋₊ + 1) ^ 2`. -/
theorem CAsymptotic_le_eight_mul_floor_inv_add_one_sq {ε : ℝ} (hε : 0 < ε) :
    CAsymptotic ε ≤ 8 * (⌊ε⁻¹⌋₊ + 1) ^ 2 := by
  let k : ℕ := ⌊ε⁻¹⌋₊ + 1
  have hk1 : 1 ≤ k := by omega
  have hlt_k : ε⁻¹ < (k : ℝ) := by dsimp [k]; push_cast; exact Nat.lt_floor_add_one (ε⁻¹)
  have hkε : 1 < (k : ℝ) * ε := (inv_lt_iff_one_lt_mul₀ hε).mp hlt_k
  exact CAsymptotic_le_eight_mul_sq_of_one_lt_mul hε hk1 hkε

/-- **Sharp asymptotic `(8 + o(1)) ε⁻²` Glibichuk bound**: for every `η > 0`, eventually as
`ε → 0⁺`, `(CAsymptotic ε : ℝ) ≤ (8 + η) * ε⁻¹ ^ 2`. -/
theorem eventually_CAsymptotic_le_eight_add_mul_inv_sq {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (CAsymptotic ε : ℝ) ≤ (8 + η) * ε⁻¹ ^ 2 := by
  let r : ℝ := min 1 (η / 24)
  have hr_pos : 0 < r := lt_min zero_lt_one (by positivity)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr_pos] with ε hball hε0
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε0] at hball
  have hε1 : ε ≤ 1 := hball.le.trans (min_le_left _ _)
  have hε_eta : ε ≤ η / 24 := hball.le.trans (min_le_right _ _)
  have hinv1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).mpr hε1
  have h24 : 24 * ε⁻¹ ≤ η * ε⁻¹ ^ 2 := by
    have h1 : 24 * ε ≤ η := by linarith
    have h2 : (24 * ε) * ε⁻¹ ^ 2 ≤ η * ε⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (24 * ε) * ε⁻¹ ^ 2 = 24 * ε⁻¹ := by
      rw [sq, ← mul_assoc, mul_assoc 24 ε ε⁻¹, mul_inv_cancel₀ hε0.ne', mul_one]
    linarith
  have hfl : (⌊ε⁻¹⌋₊ : ℝ) ≤ ε⁻¹ := Nat.floor_le (by positivity)
  have hdisc : (CAsymptotic ε : ℝ) ≤ 8 * ((⌊ε⁻¹⌋₊ : ℝ) + 1) ^ 2 := by
    exact_mod_cast CAsymptotic_le_eight_mul_floor_inv_add_one_sq hε0
  calc
    (CAsymptotic ε : ℝ) ≤ 8 * ((⌊ε⁻¹⌋₊ : ℝ) + 1) ^ 2 := hdisc
    _ ≤ 8 * (ε⁻¹ + 1) ^ 2 := by gcongr
    _ = 8 * ε⁻¹ ^ 2 + 16 * ε⁻¹ + 8 := by ring
    _ ≤ 8 * ε⁻¹ ^ 2 + 24 * ε⁻¹ := by linarith
    _ ≤ (8 + η) * ε⁻¹ ^ 2 := by linarith

theorem CAsymptotic_le_thirty_two_mul_inv_sq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (CAsymptotic ε : ℝ) ≤ 32 * ε⁻¹ ^ 2 := by
  have hdisc : (CAsymptotic ε : ℝ) ≤ 8 * ((⌊ε⁻¹⌋₊ : ℝ) + 1) ^ 2 := by
    exact_mod_cast CAsymptotic_le_eight_mul_floor_inv_add_one_sq hε0
  have hinv1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).mpr hε1
  have hfl : (⌊ε⁻¹⌋₊ : ℝ) ≤ ε⁻¹ := Nat.floor_le (by positivity)
  calc
    (CAsymptotic ε : ℝ) ≤ 8 * ((⌊ε⁻¹⌋₊ : ℝ) + 1) ^ 2 := hdisc
    _ ≤ 8 * (2 * ε⁻¹) ^ 2 := by gcongr; linarith
    _ = 32 * ε⁻¹ ^ 2 := by ring

theorem asymptoticBoundSet_nonempty {ε : ℝ} (hε : 0 < ε) :
    (AsymptoticBoundSet ε).Nonempty := by
  let k : ℕ := ⌊ε⁻¹⌋₊ + 1
  have hk1 : 1 ≤ k := by omega
  have hlt_k : ε⁻¹ < (k : ℝ) := by dsimp [k]; push_cast; exact Nat.lt_floor_add_one (ε⁻¹)
  have hkε : 1 < (k : ℝ) * ε := (inv_lt_iff_one_lt_mul₀ hε).mp hlt_k
  exact ⟨8 * k ^ 2, eight_mul_sq_mem_asymptoticBoundSet_of_one_lt_mul hε hk1 hkε⟩

theorem CAsymptotic_mem_asymptoticBoundSet {ε : ℝ} (hε : 0 < ε) :
    CAsymptotic ε ∈ AsymptoticBoundSet ε :=
  Nat.sInf_mem (asymptoticBoundSet_nonempty hε)

theorem erdos_1180_glibichuk :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 2 ∧ Represents ε p a s := by
  refine ⟨32, fun ε hε0 hε1 ↦ ?_⟩
  obtain ⟨P, hP⟩ := CAsymptotic_mem_asymptoticBoundSet hε0
  have hbound := CAsymptotic_le_thirty_two_mul_inv_sq hε0 hε1
  refine ⟨P, fun p hpP hp a ↦ ?_⟩
  obtain ⟨s, hcard, hrep⟩ := hP p hpP hp a
  exact ⟨s, (Nat.cast_le.mpr hcard).trans hbound, hrep⟩

theorem erdos_1180_shparlinski :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 3 ∧ Represents ε p a s := by
  refine ⟨32, fun ε hε0 hε1 ↦ ?_⟩
  obtain ⟨P, hP⟩ := CAsymptotic_mem_asymptoticBoundSet hε0
  have hbound := CAsymptotic_le_thirty_two_mul_inv_sq hε0 hε1
  have hinv1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).mpr hε1
  have hpow : ε⁻¹ ^ 2 ≤ ε⁻¹ ^ 3 := by nlinarith
  refine ⟨P, fun p hpP hp a ↦ ?_⟩
  obtain ⟨s, hcard, hrep⟩ := hP p hpP hp a
  refine ⟨s, ?_, hrep⟩
  calc
    (s.card : ℝ) ≤ (CAsymptotic ε : ℝ) := by exact_mod_cast hcard
    _ ≤ 32 * ε⁻¹ ^ 2 := hbound
    _ ≤ 32 * ε⁻¹ ^ 3 := by linarith

theorem uniformBoundSet_nonempty {ε : ℝ} (hε : 0 < ε) :
    (UniformBoundSet ε).Nonempty := by
  obtain ⟨P, hP⟩ := CAsymptotic_mem_asymptoticBoundSet hε
  refine ⟨max (CAsymptotic ε) P, fun p hp a ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hlarge : P ≤ p
  · obtain ⟨s, hcard, hrep⟩ := hP p hlarge hp a
    exact ⟨s, hcard.trans (le_max_left _ _), hrep⟩
  · obtain ⟨hrep, hcard⟩ := represents_val_replicate_one hp.one_le hε.le a
    have hpP : p - 1 ≤ P := by omega
    exact ⟨Multiset.replicate a.val 1, hcard.trans (hpP.trans (le_max_right _ _)), hrep⟩

theorem erdos_1180_multiset :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s :=
  fun _ hε ↦ uniformBoundSet_nonempty hε

theorem two_rpow_inv_le_four_mul_C {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ^ (ε⁻¹) ≤ 4 * (C ε : ℝ) :=
  two_rpow_inv_le_four_mul_C_of_nonempty hε (uniformBoundSet_nonempty hε)

theorem erdos_1180_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → K * ε⁻¹ ≤ (C ε : ℝ) :=
  erdos_1180_lower_bound_of_nonempty (fun _ hε _ ↦ uniformBoundSet_nonempty hε)

theorem four_mul_sq_lt_two_pow (n : ℕ) (hn : 9 ≤ n) : 4 * n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
      calc
        4 * (n + 1) ^ 2 < 2 * (4 * n ^ 2) := by nlinarith
        _ < 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_left ih zero_lt_two
        _ = 2 ^ (n + 1) := by rw [pow_succ']

theorem not_erdos1180OptimalConjecture_of_nonempty
    (hne : ∀ ε : ℝ, 0 < ε → (UniformBoundSet ε).Nonempty) :
    ¬ Erdos1180OptimalConjecture := by
  intro hopt
  have hev := hopt 1 zero_lt_one
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr0, hr⟩ := hev
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
  let n : ℕ := m + 9
  have hn9 : 9 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  let ε : ℝ := (n : ℝ)⁻¹
  have hε0 : 0 < ε := inv_pos.mpr hnpos
  have hrm : 1 / r < n := hm.trans (by dsimp [n]; exact_mod_cast (by omega : m < m + 9))
  have hεr : ε < r := by
    dsimp [ε]; rw [← one_div]
    exact (div_lt_iff₀ hnpos).mpr ((div_lt_iff₀ hr0).mp hrm |>.trans_eq (mul_comm (n : ℝ) r))
  have hdist : dist ε 0 < r := by rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact hεr
  have hCle : (C ε : ℝ) ≤ ε⁻¹ ^ (1 + (1 : ℝ)) := hr hdist hε0
  have hlow : (2 : ℝ) ^ (ε⁻¹) ≤ 4 * (C ε : ℝ) :=
    two_rpow_inv_le_four_mul_C_of_nonempty hε0 (hne ε hε0)
  have hinv : ε⁻¹ = (n : ℝ) := inv_inv (n : ℝ)
  rw [hinv] at hCle hlow
  have hpow2 : (n : ℝ) ^ (1 + (1 : ℝ)) = (n : ℝ) ^ (2 : ℕ) := by
    rw [show (1 : ℝ) + 1 = 2 by ring, Real.rpow_two]
  rw [hpow2] at hCle
  rw [Real.rpow_natCast] at hlow
  have hcomb : ((2 ^ n : ℕ) : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) := by push_cast; linarith
  exact Nat.not_le_of_gt (four_mul_sq_lt_two_pow n hn9) (Nat.cast_le.mp hcomb)

theorem not_erdos1180OptimalConjecture : ¬ Erdos1180OptimalConjecture :=
  not_erdos1180OptimalConjecture_of_nonempty (fun _ hε ↦ uniformBoundSet_nonempty hε)

end Erdos1180
