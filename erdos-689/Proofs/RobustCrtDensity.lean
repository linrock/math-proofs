module

public import Mathlib

@[expose] public section


open Finset
open scoped BigOperators

namespace Erdos689

/-- The actual Chinese-remainder equivalence on units, for any pair of
coprime moduli. -/
noncomputable def coprimeUnitsCrtEquiv (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits

/-- Fixing one unit coordinate in a two-factor CRT product leaves exactly the
units of the other modulus. -/
noncomputable def coprimeUnitsCrtFiberEquiv (m n : ℕ) (h : m.Coprime n)
    (u : (ZMod m)ˣ) :
    {x : (ZMod (m * n))ˣ // (coprimeUnitsCrtEquiv m n h x).1 = u} ≃
      (ZMod n)ˣ where
  toFun x := (coprimeUnitsCrtEquiv m n h x.1).2
  invFun v := ⟨(coprimeUnitsCrtEquiv m n h).symm (u, v), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply (coprimeUnitsCrtEquiv m n h).injective
    simp only [MulEquiv.apply_symm_apply]
    exact Prod.ext x.2.symm rfl
  right_inv v := by simp

/-- Every fixed unit residue has precisely `φ(n)` lifts modulo `m*n`.
This is the exact uniform-fiber CRT count needed for switched-prime
independence. -/
theorem coprime_units_crt_fiber_card (m n : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] (u : (ZMod m)ˣ) :
    Fintype.card
      {x : (ZMod (m * n))ˣ // (coprimeUnitsCrtEquiv m n h x).1 = u} =
      n.totient := by
  rw [Fintype.card_congr (coprimeUnitsCrtFiberEquiv m n h u),
    ZMod.card_units_eq_totient]

section FiniteProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate vectors avoiding their one distinguished hit at every
coordinate. -/
noncomputable def noHitVectors (U : ι → Finset ℕ) (a : ι → ℕ) :
    Finset (ι → ℕ) :=
  Fintype.piFinset fun i => (U i).erase (a i)

/-- The coordinate vectors hitting exactly at the distinguished coordinate. -/
noncomputable def oneHitVectors (U : ι → Finset ℕ) (a : ι → ℕ) (i : ι) :
    Finset (ι → ℕ) :=
  Fintype.piFinset
    (Function.update (fun j => (U j).erase (a j)) i {a i})

/-- The finite-product zero-hit count is the exact product of coordinate
cardinalities diminished by one. -/
theorem no_hit_vectors_card (U : ι → Finset ℕ) (a : ι → ℕ)
    (ha : ∀ i, a i ∈ U i) :
    (noHitVectors U a).card = ∏ i : ι, ((U i).card - 1) := by
  classical
  rw [noHitVectors, Fintype.card_piFinset]
  apply Fintype.prod_congr
  intro i
  exact Finset.card_erase_of_mem (ha i)

/-- Fixing the unique hit at coordinate `i` leaves exactly one deleted choice
at every other coordinate. -/
theorem one_hit_vectors_card (U : ι → Finset ℕ) (a : ι → ℕ)
    (ha : ∀ i, a i ∈ U i) (i : ι) :
    (oneHitVectors U a i).card =
      ∏ j ∈ (Finset.univ.erase i), ((U j).card - 1) := by
  classical
  rw [oneHitVectors, Fintype.card_piFinset]
  calc
    (∏ j : ι, (Function.update (fun k => (U k).erase (a k)) i {a i} j).card) =
        ∏ j : ι,
          Function.update (fun k => ((U k).erase (a k)).card) i 1 j := by
            apply Fintype.prod_congr
            intro j
            by_cases hji : j = i <;> simp [hji]
    _ = ∏ j ∈ (Finset.univ.erase i), ((U j).card - 1) := by
      rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
      simp only [one_mul, Finset.sdiff_singleton_eq_erase]
      apply Finset.prod_congr rfl
      intro j hj
      exact Finset.card_erase_of_mem (ha j)

/-- Vectors with fewer than two distinguished hits are covered by the
zero-hit vector set and the exact-one-hit vector sets. -/
theorem low_hit_vectors_subset (U : ι → Finset ℕ) (a : ι → ℕ) :
    (Fintype.piFinset U).filter
        (fun f => ((Finset.univ.filter fun i : ι => f i = a i).card < 2)) ⊆
      noHitVectors U a ∪ Finset.univ.biUnion (oneHitVectors U a) := by
  classical
  intro f hf
  have hU : ∀ i, f i ∈ U i := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1
  have hcard : (Finset.univ.filter fun i : ι => f i = a i).card ≤ 1 :=
    Nat.lt_succ_iff.mp (Finset.mem_filter.mp hf).2
  by_cases hhit : ∃ i : ι, f i = a i
  · obtain ⟨i, hi⟩ := hhit
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hi
    · have hne : f j ≠ a j := by
        intro hj
        apply hji
        apply (Finset.card_le_one.mp hcard) j
        · simp [hj]
        · simp [hi]
      simp [hji, hne, hU j]
  · apply Finset.mem_union_left
    apply Fintype.mem_piFinset.mpr
    intro i
    have hne : f i ≠ a i := fun hi => hhit ⟨i, hi⟩
    simp [hne, hU i]

/-- Exact finite-product union bound for the event that at most one of the
independent switched-prime coordinates hits its designated residue. -/
theorem low_hit_vectors_card_le (U : ι → Finset ℕ) (a : ι → ℕ)
    (ha : ∀ i, a i ∈ U i) :
    ((Fintype.piFinset U).filter
      (fun f => ((Finset.univ.filter fun i : ι => f i = a i).card < 2))).card ≤
      (∏ i : ι, ((U i).card - 1)) +
        ∑ i : ι, ∏ j ∈ (Finset.univ.erase i), ((U j).card - 1) := by
  calc
    _ ≤ (noHitVectors U a ∪ Finset.univ.biUnion (oneHitVectors U a)).card :=
      Finset.card_le_card (low_hit_vectors_subset U a)
    _ ≤ (noHitVectors U a).card +
        (Finset.univ.biUnion (oneHitVectors U a)).card :=
      Finset.card_union_le _ _
    _ ≤ (noHitVectors U a).card +
        ∑ i : ι, (oneHitVectors U a i).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _
    _ = _ := by
      rw [no_hit_vectors_card U a ha]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact one_hit_vectors_card U a ha i

/-- Simultaneous union bound over arbitrarily many offsets. The distinguished
hit residue may vary with both the offset and the switched-prime coordinate;
no independence between different offsets is assumed. -/
theorem multi_offset_low_hit_vectors_card_le {κ : Type*} (T : Finset κ)
    (U : ι → Finset ℕ) (a : κ → ι → ℕ)
    (ha : ∀ j ∈ T, ∀ i, a j i ∈ U i) :
    ((Fintype.piFinset U).filter fun f =>
      ∃ j ∈ T, (Finset.univ.filter fun i : ι => f i = a j i).card < 2).card ≤
      T.card * ((∏ i : ι, ((U i).card - 1)) +
        ∑ i : ι, ∏ k ∈ (Finset.univ.erase i), ((U k).card - 1)) := by
  classical
  let B : κ → Finset (ι → ℕ) := fun j =>
    (Fintype.piFinset U).filter fun f =>
      (Finset.univ.filter fun i : ι => f i = a j i).card < 2
  have hsubset : ((Fintype.piFinset U).filter fun f =>
      ∃ j ∈ T, (Finset.univ.filter fun i : ι => f i = a j i).card < 2) ⊆
      T.biUnion B := by
    intro f hf
    obtain ⟨hfU, j, hjT, hj⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_biUnion.mpr
      ⟨j, hjT, Finset.mem_filter.mpr ⟨hfU, hj⟩⟩
  calc
    _ ≤ (T.biUnion B).card := Finset.card_le_card hsubset
    _ ≤ ∑ j ∈ T, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ T, ((∏ i : ι, ((U i).card - 1)) +
        ∑ i : ι, ∏ k ∈ (Finset.univ.erase i), ((U k).card - 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact low_hit_vectors_card_le U (a j) (ha j hj)
    _ = _ := by simp

/-- The complete independent unit-residue vector space for a finite support
has exactly the product of the `p-1` local unit counts. -/
theorem prime_unit_vector_card (S : Finset ℕ) :
    (Fintype.piFinset fun p : {p : ℕ // p ∈ S} =>
      Finset.Ico 1 (p : ℕ)).card = ∏ p ∈ S, (p - 1) := by
  classical
  rw [Fintype.card_piFinset]
  simpa using (Finset.prod_coe_sort S (fun p : ℕ => p - 1))

/-- Prime-unit coordinate vectors failing robustness at at least one of the
first `J` offsets. -/
noncomputable def primeOffsetBadVectors (S : Finset ℕ) (J : ℕ)
    (a : ℕ → {p : ℕ // p ∈ S} → ℕ) :
    Finset ({p : ℕ // p ∈ S} → ℕ) := by
  classical
  exact (Fintype.piFinset fun p : {p : ℕ // p ∈ S} => Finset.Ico 1 (p : ℕ)).filter
    fun f => ∃ j ∈ Finset.Icc 1 J,
      (Finset.univ.filter fun p : {p : ℕ // p ∈ S} => f p = a j p).card < 2

/-- Exact switched-prime unit-vector union bound for all manuscript offsets
`1 ≤ j ≤ J`: each zero-hit factor is `p-2`, and each unique-hit fiber deletes
that factor at its distinguished prime. -/
theorem prime_unit_multi_offset_low_hit_card_le (S : Finset ℕ) (J : ℕ)
    (a : ℕ → {p : ℕ // p ∈ S} → ℕ)
    (ha : ∀ j ∈ Finset.Icc 1 J, ∀ p : {p : ℕ // p ∈ S},
      a j p ∈ Finset.Ico 1 (p : ℕ)) :
    (primeOffsetBadVectors S J a).card ≤
      J * ((∏ p ∈ S, (p - 2)) +
        ∑ p : {p : ℕ // p ∈ S},
          ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2)) := by
  classical
  have h := multi_offset_low_hit_vectors_card_le (Finset.Icc 1 J)
    (fun p : {p : ℕ // p ∈ S} => Finset.Ico 1 (p : ℕ)) a ha
  have hzero :
      (∏ p : {p : ℕ // p ∈ S}, ((Finset.Ico 1 (p : ℕ)).card - 1)) =
        ∏ p ∈ S, (p - 2) := by
    simpa [Nat.sub_sub] using (Finset.prod_coe_sort S (fun p : ℕ => p - 2))
  rw [hzero] at h
  simpa [primeOffsetBadVectors, Nat.sub_sub] using h

end FiniteProduct

end Erdos689

#print axioms Erdos689.coprime_units_crt_fiber_card
#print axioms Erdos689.no_hit_vectors_card
#print axioms Erdos689.one_hit_vectors_card
#print axioms Erdos689.low_hit_vectors_subset
#print axioms Erdos689.low_hit_vectors_card_le
#print axioms Erdos689.multi_offset_low_hit_vectors_card_le
#print axioms Erdos689.prime_unit_vector_card
#print axioms Erdos689.prime_unit_multi_offset_low_hit_card_le
