module

public import Mathlib


@[expose] public section

/-!
# Exact-size finite averaging for sparse cuts

The weights may have either sign. A minimum-weight subset of a prescribed
natural cardinality has average weight at most the ambient average. The
exchange proof gives a deterministic finite averaging bridge.
-/

namespace Erdos546

open Finset
open scoped Classical BigOperators

variable {V : Type*}

theorem exists_subset_card_weight_mean_le (s : Finset V) (w : V → ℝ)
    (k : ℕ) (hk : k ≤ s.card) :
    ∃ T : Finset V, T ⊆ s ∧ T.card = k ∧
      (s.card : ℝ) * (∑ x ∈ T, w x) ≤ (k : ℝ) * (∑ x ∈ s, w x) := by
  classical
  obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq hk
  have hp : (s.powersetCard k).Nonempty :=
    ⟨T₀, Finset.mem_powersetCard.mpr ⟨hT₀sub, hT₀card⟩⟩
  obtain ⟨T, hTmem, hminimal⟩ :=
    (s.powersetCard k).exists_min_image (fun U => ∑ x ∈ U, w x) hp
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
  have hweights : ∀ x ∈ T, ∀ y ∈ s \ T, w x ≤ w y := by
    intro x hx y hy
    obtain ⟨hys, hyT⟩ := Finset.mem_sdiff.mp hy
    let T' := insert y (T.erase x)
    have hyerase : y ∉ T.erase x := fun h => hyT (Finset.mem_of_mem_erase h)
    have hT'sub : T' ⊆ s := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hys
      · exact hTsub (Finset.mem_of_mem_erase hz)
    have hT'card : T'.card = k := by
      rw [Finset.card_insert_of_notMem hyerase, Finset.card_erase_of_mem hx]
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have hbound := hminimal T' (Finset.mem_powersetCard.mpr ⟨hT'sub, hT'card⟩)
    dsimp only [T'] at hbound
    rw [Finset.sum_insert hyerase] at hbound
    have hsum := Finset.sum_erase_add T w hx
    linarith
  have hcompare : ((s \ T).card : ℝ) * (∑ x ∈ T, w x) ≤
      (T.card : ℝ) * (∑ y ∈ s \ T, w y) := by
    calc
      ((s \ T).card : ℝ) * (∑ x ∈ T, w x) =
          ∑ x ∈ T, ∑ _y ∈ s \ T, w x := by
        rw [Finset.mul_sum]
        simp [mul_comm]
      _ ≤ ∑ _x ∈ T, ∑ y ∈ s \ T, w y := by
        apply Finset.sum_le_sum
        intro x hx
        exact Finset.sum_le_sum (fun y hy => hweights x hx y hy)
      _ = (T.card : ℝ) * (∑ y ∈ s \ T, w y) := by simp
  have hcard : T.card + (s \ T).card = s.card := by
    rw [Finset.card_sdiff_of_subset hTsub]
    omega
  have hcardreal : (T.card : ℝ) + (s \ T).card = s.card := by exact_mod_cast hcard
  have hsum : (∑ x ∈ s \ T, w x) + (∑ x ∈ T, w x) = ∑ x ∈ s, w x := by
    exact Finset.sum_sdiff hTsub
  refine ⟨T, hTsub, hTcard, ?_⟩
  rw [← hTcard, ← hcardreal, ← hsum]
  nlinarith only [hcompare]

theorem mean_cut_count (H : SimpleGraph V) (X Y : Finset V) :
    (H.interedges X Y).card = ∑ x ∈ X, (Y.filter fun y => H.Adj x y).card := by
  classical
  simp only [SimpleGraph.interedges_def, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

theorem mean_cut_count_symm (H : SimpleGraph V) (X Y : Finset V) :
    (H.interedges X Y).card = (H.interedges Y X).card := by
  classical
  have := H.symm
  exact Rel.card_interedges_comm X Y

/-- Every finite sparse cut has a sparse equal-size subcut at every prescribed
size no greater than either side. The input and output are exact graph counts.
The disjointness assumption is not needed for averaging; when supplied it is
inherited by the returned subsets. -/
theorem exists_equal_sparse_subcut (H : SimpleGraph V) (X Y : Finset V)
    (ε : ℝ) (k : ℕ) (hkX : k ≤ X.card) (hkY : k ≤ Y.card)
    (hsparse : ((H.interedges X Y).card : ℝ) ≤ ε * X.card * Y.card) :
    ∃ X' Y' : Finset V, X' ⊆ X ∧ Y' ⊆ Y ∧ X'.card = k ∧ Y'.card = k ∧
      ((H.interedges X' Y').card : ℝ) ≤ ε * (k : ℝ)^2 := by
  classical
  by_cases hk : k = 0
  · subst k
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp⟩
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast lt_of_lt_of_le hkpos hkX
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast lt_of_lt_of_le hkpos hkY
  obtain ⟨X', hXsub, hXcard, hXmean⟩ := exists_subset_card_weight_mean_le X
    (fun x => ((Y.filter fun y => H.Adj x y).card : ℝ)) k hkX
  rw [← Nat.cast_sum, ← mean_cut_count H X' Y,
    ← Nat.cast_sum, ← mean_cut_count H X Y] at hXmean
  have hfirst : ((H.interedges X' Y).card : ℝ) ≤ ε * k * Y.card := by
    apply (mul_le_mul_iff_right₀ hXpos).mp
    have hmult := mul_le_mul_of_nonneg_left hsparse (show (0 : ℝ) ≤ k by positivity)
    nlinarith only [hXmean, hmult]
  obtain ⟨Y', hYsub, hYcard, hYmean⟩ := exists_subset_card_weight_mean_le Y
    (fun y => ((X'.filter fun x => H.Adj y x).card : ℝ)) k hkY
  rw [← Nat.cast_sum, ← mean_cut_count H Y' X',
    ← Nat.cast_sum, ← mean_cut_count H Y X',
    mean_cut_count_symm H Y' X', mean_cut_count_symm H Y X'] at hYmean
  refine ⟨X', Y', hXsub, hYsub, hXcard, hYcard, ?_⟩
  apply (mul_le_mul_iff_right₀ hYpos).mp
  have hmult := mul_le_mul_of_nonneg_left hfirst (show (0 : ℝ) ≤ k by positivity)
  nlinarith only [hYmean, hmult]

#print axioms exists_subset_card_weight_mean_le
#print axioms exists_equal_sparse_subcut

end Erdos546
