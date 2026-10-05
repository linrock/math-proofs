module

public import Mathlib
public import Structural
public import GreedyMatching
public import Cleanup
public import AnalyticBridge

@[expose] public section


/-!
# Simultaneous reserve switches and noncircular matching realization

A protected reserve can be reassigned on any subset simultaneously.  Every
formerly protected hit survives, and the exact deficiency at each target drops
by the number of newly selected reserve hits, truncated at zero.
-/

open scoped BigOperators

namespace Erdos689

/-- Reassign exactly the prime moduli in a finite selected set. -/
def partialSwitch (a f : ℕ → ℕ) (L : Finset ℕ) : ℕ → ℕ :=
  fun p => if p ∈ L then f p else a p

/-- The number of selected new residue classes hitting a target. -/
def reserveHits (L : Finset ℕ) (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  (L.filter fun p => f p ≡ m [MOD p]).card

/-- Distinct prime labels used by a three-partite matching. -/
def matchingLabels (M : Finset TripleEdge) : Finset ℕ :=
  M.image fun e => e.2.2

/-- Both closed-interval targets repaired by each selected edge. -/
def matchingTargets (M : Finset TripleEdge) : Finset ℕ :=
  (M.image fun e => 2 * e.1) ∪ (M.image fun e => 2 * e.2.1)

/-- The concrete residue selected for a matched prime label. -/
noncomputable def matchingRepair (M : Finset TripleEdge) (p : ℕ) : ℕ :=
  if h : ∃ e ∈ M, e.2.2 = p then 2 * (Classical.choose h).1 else 0

/-- Every old hit protected from the entire reserve survives a partial switch. -/
theorem protectedPrimes_subset_partialSwitch {n m : ℕ}
    {a f : ℕ → ℕ} {R L : Finset ℕ} (hsub : L ⊆ R) :
    protectedPrimes n a R m ⊆
      protectedPrimes n (partialSwitch a f L) (R \ L) m := by
  classical
  intro p hp
  obtain ⟨hcovered, houtside⟩ := Finset.mem_filter.mp hp
  have hnotselected : p ∉ L := fun h => houtside (hsub h)
  apply Finset.mem_filter.mpr
  constructor
  · obtain ⟨hone, hbound, hprime, hhit⟩ :=
      mem_coveredPrimes_iff.mp hcovered
    apply mem_coveredPrimes_iff.mpr
    refine ⟨hone, hbound, hprime, ?_⟩
    simpa [partialSwitch, hnotselected] using hhit
  · intro hremaining
    exact houtside (Finset.mem_sdiff.mp hremaining).1

/-- Reassigning any subset leaves the complete unused reserve protected. -/
theorem protectedReserve_partialSwitch {n : ℕ}
    {a f : ℕ → ℕ} {R L : Finset ℕ}
    (hreserve : protectedReserve n a R) (hsub : L ⊆ R) :
    protectedReserve n (partialSwitch a f L) (R \ L) := by
  classical
  intro p hp
  obtain ⟨hreservep, hnotselected⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hprime, hbound, hzero, hprotected⟩ := hreserve p hreservep
  refine ⟨hprime, hbound, ?_, ?_⟩
  · simpa [partialSwitch, hnotselected] using hzero
  · intro m hm hdiv
    exact (hprotected m hm hdiv).trans
      (Finset.card_le_card (protectedPrimes_subset_partialSwitch hsub))

/-- At an originally deficient target, selected reserve hits are genuinely new. -/
theorem coveredPrimes_partialSwitch_of_deficient {n m : ℕ}
    {a f : ℕ → ℕ} {R L : Finset ℕ}
    (hreserve : protectedReserve n a R) (hsub : L ⊆ R)
    (hm : m ∈ Finset.Icc 1 n) (hdeficient : coverage n a m < 2) :
    coveredPrimes n (partialSwitch a f L) m =
      coveredPrimes n a m ∪ (L.filter fun p => f p ≡ m [MOD p]) := by
  classical
  ext p
  by_cases hpselected : p ∈ L
  · have hpreserve : p ∈ R := hsub hpselected
    obtain ⟨hprime, hbound, hzero, _⟩ := hreserve p hpreserve
    have hold : p ∉ coveredPrimes n a m := by
      intro hcovered
      have hhit := (mem_coveredPrimes_iff.mp hcovered).2.2.2
      exact protectedReserve_not_dvd_deficient hreserve hpreserve hm hdeficient
        ((zero_class_hit_iff_dvd hzero).mp hhit)
    constructor
    · intro hcovered
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hpselected, ?_⟩
      have hhit := (mem_coveredPrimes_iff.mp hcovered).2.2.2
      simpa [partialSwitch, hpselected] using hhit
    · intro hcovered
      rcases Finset.mem_union.mp hcovered with holdhit | hnewhit
      · exact False.elim (hold holdhit)
      · have hhit := (Finset.mem_filter.mp hnewhit).2
        apply mem_coveredPrimes_iff.mpr
        refine ⟨hprime.one_le, hbound, hprime, ?_⟩
        simpa [partialSwitch, hpselected] using hhit
  · constructor
    · intro hcovered
      apply Finset.mem_union.mpr
      left
      obtain ⟨hone, hbound, hprime, hhit⟩ :=
        mem_coveredPrimes_iff.mp hcovered
      apply mem_coveredPrimes_iff.mpr
      refine ⟨hone, hbound, hprime, ?_⟩
      simpa [partialSwitch, hpselected] using hhit
    · intro hcovered
      rcases Finset.mem_union.mp hcovered with holdhit | hnewhit
      · obtain ⟨hone, hbound, hprime, hhit⟩ :=
          mem_coveredPrimes_iff.mp holdhit
        apply mem_coveredPrimes_iff.mpr
        refine ⟨hone, hbound, hprime, ?_⟩
        simpa [partialSwitch, hpselected] using hhit
      · exact False.elim (hpselected (Finset.mem_filter.mp hnewhit).1)

/-- Every selected class adds exactly one distinct hit at a deficient target. -/
theorem coverage_partialSwitch_of_deficient {n m : ℕ}
    {a f : ℕ → ℕ} {R L : Finset ℕ}
    (hreserve : protectedReserve n a R) (hsub : L ⊆ R)
    (hm : m ∈ Finset.Icc 1 n) (hdeficient : coverage n a m < 2) :
    coverage n (partialSwitch a f L) m =
      coverage n a m + reserveHits L f m := by
  classical
  unfold coverage reserveHits
  rw [coveredPrimes_partialSwitch_of_deficient hreserve hsub hm hdeficient]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro p hpold hpnew
  have hpselected := (Finset.mem_filter.mp hpnew).1
  have hpreserve : p ∈ R := hsub hpselected
  have hhit := (mem_coveredPrimes_iff.mp hpold).2.2.2
  exact protectedReserve_not_dvd_deficient hreserve hpreserve hm hdeficient
    ((zero_class_hit_iff_dvd (hreserve p hpreserve).2.2.1).mp hhit)

/-- Simultaneously reassigning protected primes never creates a new deficiency. -/
theorem partialSwitch_preserves_double {n m : ℕ}
    {a f : ℕ → ℕ} {R L : Finset ℕ}
    (hreserve : protectedReserve n a R) (hsub : L ⊆ R)
    (hm : m ∈ Finset.Icc 1 n) (hcovered : 2 ≤ coverage n a m) :
    2 ≤ coverage n (partialSwitch a f L) m := by
  classical
  by_cases hdiv : ∃ p ∈ R, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := hdiv
    have hprotected := (hreserve p hp).2.2.2 m hm hpm
    have hsurvive := Finset.card_le_card
      (protectedPrimes_subset_partialSwitch
        (n := n) (a := a) (f := f) (m := m) hsub)
    have hsubset := Finset.card_le_card
      (protectedPrimes_subset_covered n m (partialSwitch a f L) (R \ L))
    change (protectedPrimes n (partialSwitch a f L) (R \ L) m).card ≤
      coverage n (partialSwitch a f L) m at hsubset
    omega
  · have hsubset : coveredPrimes n a m ⊆
        coveredPrimes n (partialSwitch a f L) m := by
      intro p hp
      have hnotselected : p ∉ L := by
        intro hselected
        have hpreserve := hsub hselected
        have hhit := (mem_coveredPrimes_iff.mp hp).2.2.2
        exact hdiv ⟨p, hpreserve,
          (zero_class_hit_iff_dvd (hreserve p hpreserve).2.2.1).mp hhit⟩
      obtain ⟨hone, hbound, hprime, hhit⟩ := mem_coveredPrimes_iff.mp hp
      apply mem_coveredPrimes_iff.mpr
      refine ⟨hone, hbound, hprime, ?_⟩
      simpa [partialSwitch, hnotselected] using hhit
    exact hcovered.trans (Finset.card_le_card hsubset)

/-- Exact simultaneous-switch token law, including all incidental overlaps. -/
theorem partialSwitch_deficiency_token {n m : ℕ}
    {a f : ℕ → ℕ} {R L : Finset ℕ}
    (hreserve : protectedReserve n a R) (hsub : L ⊆ R)
    (hm : m ∈ Finset.Icc 1 n) :
    2 - coverage n (partialSwitch a f L) m =
      (2 - coverage n a m) - reserveHits L f m := by
  by_cases hdeficient : coverage n a m < 2
  · have hgain := coverage_partialSwitch_of_deficient
      (f := f) hreserve hsub hm hdeficient
    omega
  · have hsafe := partialSwitch_preserves_double
      (f := f) hreserve hsub hm (by omega)
    omega

/-- Distinct initially deficient targets each consume one exact deficiency token. -/
theorem partialSwitch_deficiency_le_of_targets {n : ℕ}
    {a f : ℕ → ℕ} {R L T : Finset ℕ}
    (hreserve : protectedReserve n a R) (hsub : L ⊆ R)
    (htargets : T ⊆ Finset.Icc 1 n)
    (hdeficient : ∀ m ∈ T, coverage n a m < 2)
    (hhits : ∀ m ∈ T, 0 < reserveHits L f m) :
    deficiency n (partialSwitch a f L) + T.card ≤ deficiency n a := by
  classical
  have hindicator :
      (∑ m ∈ Finset.Icc 1 n, if m ∈ T then 1 else 0) = T.card := by
    rw [← Finset.sum_filter]
    have heq : (Finset.Icc 1 n).filter (fun m => m ∈ T) = T := by
      ext m
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨htargets h, h⟩⟩
    simp [heq]
  have hsum :
      (∑ m ∈ Finset.Icc 1 n,
        ((2 - coverage n (partialSwitch a f L) m) +
          if m ∈ T then 1 else 0)) ≤
        ∑ m ∈ Finset.Icc 1 n, (2 - coverage n a m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hexact := partialSwitch_deficiency_token
      (f := f) hreserve hsub hm
    by_cases hmem : m ∈ T
    · have hpositive := hhits m hmem
      have hmissing := hdeficient m hmem
      simp only [hmem, ↓reduceIte]
      omega
    · simp only [hmem, ↓reduceIte, Nat.add_zero]
      omega
  rw [Finset.sum_add_distrib, hindicator] at hsum
  exact hsum

/-- A genuine three-partite matching uses each prime label at most once. -/
theorem matchingLabels_card {M : Finset TripleEdge}
    (hmatching : threePartiteMatching M) :
    (matchingLabels M).card = M.card := by
  classical
  unfold matchingLabels
  apply Finset.card_image_of_injOn
  intro e he f hf heq
  by_contra hne
  exact hmatching e he f hf hne (Or.inr (Or.inr heq))

/-- The first target coordinate occurs once per selected matching edge. -/
theorem matching_left_targets_card {M : Finset TripleEdge}
    (hmatching : threePartiteMatching M) :
    (M.image fun e => 2 * e.1).card = M.card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he f hf heq
  change 2 * e.1 = 2 * f.1 at heq
  have hcoord : e.1 = f.1 := by omega
  by_contra hne
  exact hmatching e he f hf hne (Or.inl hcoord)

/-- The second target coordinate occurs once per selected matching edge. -/
theorem matching_right_targets_card {M : Finset TripleEdge}
    (hmatching : threePartiteMatching M) :
    (M.image fun e => 2 * e.2.1).card = M.card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he f hf heq
  change 2 * e.2.1 = 2 * f.2.1 at heq
  have hcoord : e.2.1 = f.2.1 := by omega
  by_contra hne
  exact hmatching e he f hf hne (Or.inr (Or.inl hcoord))

/-- Disjoint target parts turn a matching into exactly two distinct targets per edge. -/
theorem matchingTargets_card {M : Finset TripleEdge}
    (hmatching : threePartiteMatching M)
    (hcross : ∀ e ∈ M, ∀ f ∈ M, e.1 ≠ f.2.1) :
    (matchingTargets M).card = 2 * M.card := by
  classical
  unfold matchingTargets
  have hdisjoint : Disjoint
      (M.image fun e => 2 * e.1) (M.image fun e => 2 * e.2.1) := by
    apply Finset.disjoint_left.mpr
    intro m hleft hright
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hleft
    obtain ⟨f, hf, hfeq⟩ := Finset.mem_image.mp hright
    apply hcross e he f hf
    omega
  rw [Finset.card_union_of_disjoint hdisjoint,
    matching_left_targets_card hmatching,
    matching_right_targets_card hmatching]
  omega

/-- A matched label is assigned the first target of its uniquely selected edge. -/
theorem matchingRepair_eq {M : Finset TripleEdge} {e : TripleEdge}
    (hmatching : threePartiteMatching M) (he : e ∈ M) :
    matchingRepair M e.2.2 = 2 * e.1 := by
  classical
  have hexists : ∃ f ∈ M, f.2.2 = e.2.2 := ⟨e, he, rfl⟩
  unfold matchingRepair
  simp only [dif_pos hexists]
  have hchosen := Classical.choose_spec hexists
  have hsame : Classical.choose hexists = e := by
    by_contra hne
    exact hmatching (Classical.choose hexists) hchosen.1 e he hne
      (Or.inr (Or.inr hchosen.2))
  rw [hsame]

/-- Every admissible matching has an explicitly realized protected post-switch ledger. -/
theorem matching_realizes_protected_ledger {n : ℕ}
    {a : ℕ → ℕ} {R : Finset ℕ} {E M : Finset TripleEdge}
    (hreserve : protectedReserve n a R)
    (hlabels : ∀ e ∈ E, e.2.2 ∈ R)
    (hleft : ∀ e ∈ E,
      2 * e.1 ∈ Finset.Icc 1 n ∧ coverage n a (2 * e.1) < 2)
    (hright : ∀ e ∈ E,
      2 * e.2.1 ∈ Finset.Icc 1 n ∧ coverage n a (2 * e.2.1) < 2)
    (hpaired : ∀ e ∈ E, 2 * e.1 ≡ 2 * e.2.1 [MOD e.2.2])
    (hcross : ∀ e ∈ E, ∀ f ∈ E, e.1 ≠ f.2.1)
    (hsubmatching : M ⊆ E) (hmatching : threePartiteMatching M) :
    ∃ final : ℕ → ℕ, ∃ available : Finset ℕ,
      protectedReserve n final available ∧
      available.card + M.card = R.card ∧
      deficiency n final + 2 * M.card ≤ deficiency n a := by
  classical
  let L := matchingLabels M
  let f := matchingRepair M
  have hselected : L ⊆ R := by
    intro p hp
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hp
    subst p
    exact hlabels e (hsubmatching he)
  have htargetsubset : matchingTargets M ⊆ Finset.Icc 1 n := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      exact (hleft e (hsubmatching he)).1
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      exact (hright e (hsubmatching he)).1
  have htargetdeficient : ∀ m ∈ matchingTargets M, coverage n a m < 2 := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      exact (hleft e (hsubmatching he)).2
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      exact (hright e (hsubmatching he)).2
  have htargethits : ∀ m ∈ matchingTargets M, 0 < reserveHits L f m := by
    intro m hm
    unfold reserveHits
    apply Finset.card_pos.mpr
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      refine ⟨e.2.2, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      · change matchingRepair M e.2.2 ≡ 2 * e.1 [MOD e.2.2]
        rw [matchingRepair_eq hmatching he]
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      refine ⟨e.2.2, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      · change matchingRepair M e.2.2 ≡ 2 * e.2.1 [MOD e.2.2]
        rw [matchingRepair_eq hmatching he]
        exact hpaired e (hsubmatching he)
  have hcardtargets : (matchingTargets M).card = 2 * M.card :=
    matchingTargets_card hmatching (by
      intro e he g hg
      exact hcross e (hsubmatching he) g (hsubmatching hg))
  have hdrop := partialSwitch_deficiency_le_of_targets
    (f := f) hreserve hselected htargetsubset htargetdeficient htargethits
  rw [hcardtargets] at hdrop
  refine ⟨partialSwitch a f L, R \ L,
    protectedReserve_partialSwitch hreserve hselected, ?_, hdrop⟩
  have hdifference := Finset.card_sdiff_of_subset hselected
  have hcardlabels : L.card = M.card := matchingLabels_card hmatching
  have hcardbound : L.card ≤ R.card := Finset.card_le_card hselected
  omega

/-- Concrete local edge conditions, scalar estimates, and a protected reserve suffice. -/
theorem covering_of_protected_matching {n D k : ℕ}
    (a : ℕ → ℕ) (R : Finset ℕ) (E : Finset TripleEdge)
    (hreserve : protectedReserve n a R)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ E.card)
    (hsurplus : deficiency n a ≤ R.card + k)
    (hlabels : ∀ e ∈ E, e.2.2 ∈ R)
    (hleft : ∀ e ∈ E,
      2 * e.1 ∈ Finset.Icc 1 n ∧ coverage n a (2 * e.1) < 2)
    (hright : ∀ e ∈ E,
      2 * e.2.1 ∈ Finset.Icc 1 n ∧ coverage n a (2 * e.2.1) < 2)
    (hpaired : ∀ e ∈ E, 2 * e.1 ≡ 2 * e.2.1 [MOD e.2.2])
    (hcross : ∀ e ∈ E, ∀ f ∈ E, e.1 ≠ f.2.1) :
    ∃ final : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m := by
  apply covering_of_explicit_matching_ledger
    a R E hdegree hx hy hz hedges hsurplus
  intro M hsubmatching hmatching
  exact matching_realizes_protected_ledger hreserve hlabels hleft hright
    hpaired hcross hsubmatching hmatching

/-- The fixed manuscript assignment and canonical reserve need no construction hypothesis. -/
theorem covering_of_canonical_matching {n J D k : ℕ}
    (S : Finset ℕ) (b : ℕ → ℕ) (E : Finset TripleEdge)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ E.card)
    (hsurplus : deficiency n (initialAssignment S b) ≤
      (canonicalReserve S b n J).card + k)
    (hlabels : ∀ e ∈ E, e.2.2 ∈ canonicalReserve S b n J)
    (hleft : ∀ e ∈ E,
      2 * e.1 ∈ Finset.Icc 1 n ∧
        coverage n (initialAssignment S b) (2 * e.1) < 2)
    (hright : ∀ e ∈ E,
      2 * e.2.1 ∈ Finset.Icc 1 n ∧
        coverage n (initialAssignment S b) (2 * e.2.1) < 2)
    (hpaired : ∀ e ∈ E, 2 * e.1 ≡ 2 * e.2.1 [MOD e.2.2])
    (hcross : ∀ e ∈ E, ∀ f ∈ E, e.1 ≠ f.2.1) :
    ∃ final : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m := by
  exact covering_of_protected_matching
    (initialAssignment S b) (canonicalReserve S b n J) E
    (initialAssignment_protectedReserve hsupport)
    hdegree hx hy hz hedges hsurplus hlabels hleft hright hpaired hcross

end Erdos689

