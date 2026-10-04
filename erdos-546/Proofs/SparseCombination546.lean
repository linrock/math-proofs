module

public import Mathlib


@[expose] public section

/-!
# Sparse-cut cleaning for the Fox--Sudakov combination argument

These lemmas establish the two degree-cleaning steps needed before combining
two recursively constructed sparse families. Arbitrary refinement of a sparse
cut need not remain sparse. The second cleaning depends on the actual first
refinement `A`, and its conclusion permits every subsequent refinement `B`.

The depth induction then yields an exact-size sparse subset from hereditary
sparse cuts. Its hypothesis still has to be supplied by the embedding lemma
before it can contribute to the complete Ramsey bound.
-/

namespace Erdos546

open Finset
open scoped BigOperators
open scoped Classical

variable {V : Type*}

/-- Vertices whose nonnegative weight is at most the stated threshold occupy
at least half the finite set, provided the average weight is at most half
the threshold. This includes a zero threshold and an empty ambient set. -/
theorem half_card_filter_weight_le (s : Finset V) (w : V → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hw : ∀ x ∈ s, 0 ≤ w x)
    (hsum : 2 * (∑ x ∈ s, w x) ≤ T * s.card) :
    s.card ≤ 2 * (s.filter fun x => w x ≤ T).card := by
  classical
  let good := s.filter fun x => w x ≤ T
  let bad := s.filter fun x => ¬ w x ≤ T
  have hcard : good.card + bad.card = s.card :=
    Finset.card_filter_add_card_filter_not (fun x => w x ≤ T)
  dsimp only [good] at hcard
  by_contra hn
  have hbad : 0 < bad.card := by omega
  have hb : bad.Nonempty := Finset.card_pos.mp hbad
  have hlt : T * bad.card < ∑ x ∈ bad, w x := by
    calc
      T * bad.card = ∑ _x ∈ bad, T := by simp [mul_comm]
      _ < ∑ x ∈ bad, w x := Finset.sum_lt_sum_of_nonempty hb (by
        intro x hx
        exact lt_of_not_ge (Finset.mem_filter.mp hx).2)
  have hle : (∑ x ∈ bad, w x) ≤ ∑ x ∈ s, w x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun x hx _ => hw x hx)
  have hlarge : (s.card : ℝ) ≤ 2 * bad.card := by exact_mod_cast (show s.card ≤ 2 * bad.card by omega)
  have hmul := mul_le_mul_of_nonneg_left hlarge hT
  nlinarith

/-- The number of neighbors of `x` in the finite reservoir `Y`. -/
noncomputable def cutNeighborCount (H : SimpleGraph V) (Y : Finset V) (x : V) : ℕ :=
  (Y.filter fun y => H.Adj x y).card

/-- The oriented cut count is the sum of the degrees into the second set. -/
theorem card_interedges_eq_sum_cutNeighborCount (H : SimpleGraph V)
    (X Y : Finset V) :
    (H.interedges X Y).card = ∑ x ∈ X, cutNeighborCount H Y x := by
  classical
  simp only [SimpleGraph.interedges_def, cutNeighborCount, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

/-- Double counting the cut, using symmetry of graph adjacency. -/
theorem card_interedges_symm (H : SimpleGraph V) (X Y : Finset V) :
    (H.interedges X Y).card = (H.interedges Y X).card := by
  classical
  have := H.symm
  exact Rel.card_interedges_comm X Y

/-- A pointwise degree bound gives an average cut bound. -/
theorem card_interedges_le_of_cutNeighborCount_le (H : SimpleGraph V)
    (X Y : Finset V) (T : ℝ)
    (hdeg : ∀ x ∈ X, (cutNeighborCount H Y x : ℝ) ≤ T) :
    ((H.interedges X Y).card : ℝ) ≤ T * X.card := by
  classical
  rw [card_interedges_eq_sum_cutNeighborCount, Nat.cast_sum]
  calc
    (∑ x ∈ X, (cutNeighborCount H Y x : ℝ)) ≤ ∑ _x ∈ X, T :=
      Finset.sum_le_sum hdeg
    _ = T * X.card := by simp [mul_comm]

/-- First cleaning: a cut of density at most `δ/4` has a half-sized first
side whose every vertex has degree at most `δ |Y| / 2` into the other side. -/
theorem sparse_cut_first_clean (H : SimpleGraph V) (X Y : Finset V) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hsparse : ((H.interedges X Y).card : ℝ) ≤ δ / 4 * X.card * Y.card) :
    ∃ X₁ : Finset V, X₁ ⊆ X ∧ X.card ≤ 2 * X₁.card ∧
      ∀ x ∈ X₁, (cutNeighborCount H Y x : ℝ) ≤ δ / 2 * Y.card := by
  classical
  refine ⟨X.filter fun x => (cutNeighborCount H Y x : ℝ) ≤ δ / 2 * Y.card,
    Finset.filter_subset _ _, ?_, ?_⟩
  · apply half_card_filter_weight_le
    · positivity
    · intro x hx; positivity
    · rw [← Nat.cast_sum, ← card_interedges_eq_sum_cutNeighborCount]
      nlinarith
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

/-- Second cleaning after the first family has been chosen: the retained
half of `Y` has degree at most `δ |A|` into that actual family union `A`. -/
theorem sparse_cut_second_clean (H : SimpleGraph V) (A Y : Finset V) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hdeg : ∀ x ∈ A, (cutNeighborCount H Y x : ℝ) ≤ δ / 2 * Y.card) :
    ∃ Y₁ : Finset V, Y₁ ⊆ Y ∧ Y.card ≤ 2 * Y₁.card ∧
      ∀ y ∈ Y₁, (cutNeighborCount H A y : ℝ) ≤ δ * A.card := by
  classical
  have havg := card_interedges_le_of_cutNeighborCount_le H A Y (δ / 2 * Y.card) hdeg
  rw [card_interedges_symm H A Y] at havg
  refine ⟨Y.filter fun y => (cutNeighborCount H A y : ℝ) ≤ δ * A.card,
    Finset.filter_subset _ _, ?_, ?_⟩
  · apply half_card_filter_weight_le
    · positivity
    · intro y hy; positivity
    · rw [← Nat.cast_sum, ← card_interedges_eq_sum_cutNeighborCount]
      nlinarith
  · intro y hy
    exact (Finset.mem_filter.mp hy).2

/-- The robust two-cleaning interface. It allows the first recursively
constructed family to have any union `A ⊆ X₁`, and the second family to have
any union `B ⊆ Y₁`. Their aggregate cross density stays at most `δ`.
The choice of `Y₁` must take place after `A` is chosen. -/
theorem sparse_cut_two_clean (H : SimpleGraph V) (X Y : Finset V) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hsparse : ((H.interedges X Y).card : ℝ) ≤ δ / 4 * X.card * Y.card) :
    ∃ X₁ : Finset V, X₁ ⊆ X ∧ X.card ≤ 2 * X₁.card ∧
      ∀ A : Finset V, A ⊆ X₁ →
      ∃ Y₁ : Finset V, Y₁ ⊆ Y ∧ Y.card ≤ 2 * Y₁.card ∧
        ∀ B : Finset V, B ⊆ Y₁ →
          ((H.interedges A B).card : ℝ) ≤ δ * A.card * B.card := by
  classical
  obtain ⟨X₁, hXsub, hXcard, hXdeg⟩ := sparse_cut_first_clean H X Y δ hδ hsparse
  refine ⟨X₁, hXsub, hXcard, ?_⟩
  intro A hAsub
  obtain ⟨Y₁, hYsub, hYcard, hYdeg⟩ := sparse_cut_second_clean H A Y δ hδ
    (fun x hx => hXdeg x (hAsub hx))
  refine ⟨Y₁, hYsub, hYcard, ?_⟩
  intro B hBsub
  have hbound := card_interedges_le_of_cutNeighborCount_le H B A (δ * A.card)
    (fun y hy => hYdeg y (hBsub hy))
  simpa only [card_interedges_symm H B A] using hbound

/-- Exact double counting for the union of two disjoint vertex sets. -/
theorem card_interedges_union_self (H : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) :
    (H.interedges (A ∪ B) (A ∪ B)).card =
      (H.interedges A A).card + (H.interedges B B).card +
        2 * (H.interedges A B).card := by
  classical
  have hleft (C : Finset V) :
      (H.interedges (A ∪ B) C).card =
        (H.interedges A C).card + (H.interedges B C).card := by
    have heq : H.interedges (A ∪ B) C = H.interedges A C ∪ H.interedges B C := by
      ext e
      simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
      tauto
    rw [heq, Finset.card_union_of_disjoint (H.interedges_disjoint_left hAB C)]
  have hright (C : Finset V) :
      (H.interedges C (A ∪ B)).card =
        (H.interedges C A).card + (H.interedges C B).card := by
    have heq : H.interedges C (A ∪ B) = H.interedges C A ∪ H.interedges C B := by
      ext e
      simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
      tauto
    rw [heq, Finset.card_union_of_disjoint (H.interedges_disjoint_right C hAB)]
  rw [hleft, hright, hright, card_interedges_symm H B A]
  omega

/-- A fully rounded sparse-subset consequence of a hereditary sparse-cut
hypothesis. At depth `h` the result has exactly `2^h * q` vertices. Each
cleaning loses at most a factor two, so `(2*r)^h * q` input vertices suffice.
Its oriented internal edge density is at most `δ + 2^(-h)` when `q > 0`.

The hereditary premise is a graph statement about actual disjoint cuts, not
a recurrence assumption. It is the input supplied by the bounded-degree
embedding contrapositive in the full Sudakov proof. -/
theorem sparse_subset_of_hereditary_cuts (H : SimpleGraph V) (r q : ℕ) (δ : ℝ)
    (hr : 1 ≤ r) (_hq : 0 < q) (hδ : 0 ≤ δ)
    (hsplit : ∀ S : Finset V, r * q ≤ S.card →
      ∃ X Y : Finset V, X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧
        S.card ≤ r * X.card ∧ S.card ≤ r * Y.card ∧
        ((H.interedges X Y).card : ℝ) ≤ δ / 4 * X.card * Y.card) :
    ∀ (h : ℕ) (S : Finset V), (2 * r)^h * q ≤ S.card →
      ∃ U : Finset V, U ⊆ S ∧ U.card = 2^h * q ∧
        ((H.interedges U U).card : ℝ) ≤
          δ * (U.card : ℝ)^2 + (2^h : ℕ) * (q : ℝ)^2 := by
  classical
  intro h
  induction h with
  | zero =>
    intro S hsize
    obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq (by simpa using hsize)
    refine ⟨U, hUsub, by simpa using hUcard, ?_⟩
    have hcount : ((H.interedges U U).card : ℝ) ≤ (U.card : ℝ)^2 := by
      rw [pow_two]
      exact_mod_cast H.card_interedges_le_mul U U
    have hnonneg : 0 ≤ δ * (U.card : ℝ)^2 := by positivity
    simp only [pow_zero, Nat.cast_one, one_mul]
    rw [hUcard] at hcount hnonneg ⊢
    nlinarith
  | succ h ih =>
    intro S hsize
    let L : ℕ := (2 * r)^h * q
    have hbase : 0 < 2 * r := by omega
    have hpow : 1 ≤ (2 * r)^h := Nat.succ_le_of_lt (pow_pos hbase h)
    have hqL : q ≤ L := by
      simpa [L] using Nat.mul_le_mul_right q hpow
    have hsize' : 2 * r * L ≤ S.card := by
      simpa [L, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsize
    have hsplitSize : r * q ≤ S.card := by
      have h1 := Nat.mul_le_mul_left r hqL
      nlinarith
    obtain ⟨X, Y, hXS, hYS, hXY, hXrelative, hYrelative, hsparse⟩ := hsplit S hsplitSize
    obtain ⟨X₁, hXsub, hXhalf, hclean⟩ := sparse_cut_two_clean H X Y δ hδ hsparse
    have hLX : L ≤ X₁.card := by
      have hmult := Nat.mul_le_mul_left r hXhalf
      nlinarith
    obtain ⟨A, hAX₁, hAcard, hAedges⟩ := ih X₁ hLX
    obtain ⟨Y₁, hYsub, hYhalf, hcross⟩ := hclean A hAX₁
    have hLY : L ≤ Y₁.card := by
      have hmult := Nat.mul_le_mul_left r hYhalf
      nlinarith
    obtain ⟨B, hBY₁, hBcard, hBedges⟩ := ih Y₁ hLY
    have hAB : Disjoint A B := hXY.mono (hAX₁.trans hXsub) (hBY₁.trans hYsub)
    have hABcard : (A ∪ B).card = 2^(h+1) * q := by
      rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard, pow_succ]
      ring
    refine ⟨A ∪ B, Finset.union_subset ((hAX₁.trans hXsub).trans hXS)
      ((hBY₁.trans hYsub).trans hYS), hABcard, ?_⟩
    have hcrossBound := hcross B hBY₁
    rw [card_interedges_union_self H A B hAB]
    push_cast
    rw [Finset.card_union_of_disjoint hAB]
    push_cast
    simp only [pow_succ]
    push_cast at hAedges hBedges
    simp only [pow_zero]
    nlinarith

/-- The normalized graph-density form of the rounded depth theorem. -/
theorem sparse_subset_density_of_hereditary_cuts (H : SimpleGraph V)
    (r q h : ℕ) (δ : ℝ) (hr : 1 ≤ r) (hq : 0 < q) (hδ : 0 ≤ δ)
    (hsplit : ∀ S : Finset V, r * q ≤ S.card →
      ∃ X Y : Finset V, X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧
        S.card ≤ r * X.card ∧ S.card ≤ r * Y.card ∧
        ((H.interedges X Y).card : ℝ) ≤ δ / 4 * X.card * Y.card)
    (S : Finset V) (hsize : (2 * r)^h * q ≤ S.card) :
    ∃ U : Finset V, U ⊆ S ∧ U.card = 2^h * q ∧
      (H.edgeDensity U U : ℝ) ≤ δ + 1 / (2^h : ℝ) := by
  classical
  obtain ⟨U, hUsub, hUcard, hcount⟩ :=
    sparse_subset_of_hereditary_cuts H r q δ hr hq hδ hsplit h S hsize
  refine ⟨U, hUsub, hUcard, ?_⟩
  have hscalar : δ * (U.card : ℝ)^2 + (2^h : ℕ) * (q : ℝ)^2 =
      (δ + 1 / (2^h : ℝ)) * (U.card : ℝ)^2 := by
    rw [hUcard]
    push_cast
    have hp : (2^h : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hscalar] at hcount
  have hUpos : (0 : ℝ) < U.card := by
    rw [hUcard]
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) h) hq
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  apply (div_le_iff₀ (mul_pos hUpos hUpos)).mpr
  simpa only [pow_two] using hcount

#print axioms half_card_filter_weight_le
#print axioms card_interedges_eq_sum_cutNeighborCount
#print axioms sparse_cut_two_clean
#print axioms sparse_subset_of_hereditary_cuts
#print axioms sparse_subset_density_of_hereditary_cuts

end Erdos546
