module

public import ProtectedReserveOmission1139
public import ProtectedReserveConductor1139
public import FixedSupportMargin1139

@[expose] public section


/-!
# Quantitative residue-label savings from the actual Erdős #689 matching

The completed #689 proof has a strict protected-reserve/matching surplus.
Its historical covering theorem discarded that surplus because it returned
only the final all-prime residue assignment.  This module retains the exact
unused protected reserve: a greedy matching repairs two deficient targets
per consumed label, and unused zero-class labels can subsequently be omitted
from the CRT conductor.

All reserve containment, matching size, original deficiency, and residue
protection hypotheses concern the actual finite #689 construction.  No
expanded double covering, prime-pattern estimate, or new mathematical axiom
is introduced.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos689

/-- Strengthen the existing exact postmatching ledger by retaining the fact
    that the still-available protected reserve is a SUBSET of the original
    reserve.  This provenance is essential for charging the logarithmic
    conductor savings of the unused genuine prime labels. -/
theorem matching_realizes_protected_ledger_with_subset {n : ℕ}
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
      available ⊆ R ∧ protectedReserve n final available ∧
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
  have htargetdeficient : ∀ m ∈ matchingTargets M,
      coverage n a m < 2 := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      exact (hleft e (hsubmatching he)).2
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      subst m
      exact (hright e (hsubmatching he)).2
  have htargethits : ∀ m ∈ matchingTargets M,
      0 < reserveHits L f m := by
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
    Finset.sdiff_subset, protectedReserve_partialSwitch hreserve hselected,
    ?_, hdrop⟩
  have hdifference := Finset.card_sdiff_of_subset hselected
  have hcardlabels : L.card = M.card := matchingLabels_card hmatching
  have hcardbound : L.card ≤ R.card := Finset.card_le_card hselected
  omega

/-- Exact quantitative matching/cleanup theorem.  A genuine greedy matching
    of rank-three edges consumes one reserve label while repairing TWO
    distinct deficiency tokens.  Any strict integer margin

    `initialDeficiency + saved ≤ initialReserve + requiredMatching`

    therefore survives as at least `saved` UNUSED protected reserve primes.
    The output retains their subset provenance, zero-class protection, and
    full original double coverage. -/
theorem covering_with_unused_of_protected_matching_surplus
    {n D k saved : ℕ}
    (a : ℕ → ℕ) (R : Finset ℕ) (E : Finset TripleEdge)
    (hreserve : protectedReserve n a R)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ E.card)
    (hsurplus : deficiency n a + saved ≤ R.card + k)
    (hlabels : ∀ e ∈ E, e.2.2 ∈ R)
    (hleft : ∀ e ∈ E,
      2 * e.1 ∈ Finset.Icc 1 n ∧ coverage n a (2 * e.1) < 2)
    (hright : ∀ e ∈ E,
      2 * e.2.1 ∈ Finset.Icc 1 n ∧ coverage n a (2 * e.2.1) < 2)
    (hpaired : ∀ e ∈ E, 2 * e.1 ≡ 2 * e.2.1 [MOD e.2.2])
    (hcross : ∀ e ∈ E, ∀ f ∈ E, e.1 ≠ f.2.1) :
    ∃ final : ℕ → ℕ, ∃ unused : Finset ℕ,
      unused ⊆ R ∧ protectedReserve n final unused ∧
      (∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m) ∧
      saved ≤ unused.card := by
  obtain ⟨M, hsubmatching, hmatching, hbound⟩ :=
    exists_greedy_matching hx hy hz
  have hmatching_size : k ≤ M.card := by
    apply Nat.le_of_mul_le_mul_left (hedges.trans hbound)
    exact Nat.mul_pos (by norm_num) hdegree
  obtain ⟨after_matching, available, havailable_subset, havailable,
    havailable_card, hdrop⟩ :=
    matching_realizes_protected_ledger_with_subset
      hreserve hlabels hleft hright hpaired hcross hsubmatching hmatching
  have hbudget : deficiency n after_matching ≤ available.card := by
    omega
  obtain ⟨final, unused, hunused_subset, hunused,
    hcover, hunused_card⟩ :=
    exists_covering_of_protectedReserve_with_unused havailable hbudget
  refine ⟨final, unused, hunused_subset.trans havailable_subset,
    hunused, hcover, ?_⟩
  omega

/-- Specialize the strict-surplus theorem to the genuine, already audited
    #689 robust manuscript edge family.  Every edge label belongs to the
    actual canonical reserve; its left/right targets are genuinely
    deficient, and the two target parts are globally disjoint. -/
theorem manuscript_cover_with_unused_of_strict_scalar
    {n J D k saved : ℕ}
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n)
    (hlarge : (2 : ℝ) ≤ τ * n)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter
        fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter
        fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter
        fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ (robustManuscriptEdges S b n J τ ell).card)
    (hsurplus : deficiency n (initialAssignment S b) + saved ≤
      (canonicalReserve S b n J).card + k) :
    ∃ final : ℕ → ℕ, ∃ unused : Finset ℕ,
      unused ⊆ canonicalReserve S b n J ∧
      protectedReserve n final unused ∧
      (∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m) ∧
      saved ≤ unused.card := by
  classical
  have hprimes : ∀ s ∈ S, s.Prime := fun s hs => (hsupport s hs).1
  have hlabels : ∀ e ∈ robustManuscriptEdges S b n J τ ell,
      e.2.2 ∈ canonicalReserve S b n J := by
    intro e he
    exact robustManuscriptEdge_label_mem_canonicalReserve hlarge hscale he
  apply covering_with_unused_of_protected_matching_surplus
    (initialAssignment S b)
    (canonicalReserve S b n J)
    (robustManuscriptEdges S b n J τ ell)
    (initialAssignment_protectedReserve hsupport)
    hdegree hx hy hz hedges hsurplus hlabels
  · intro e he
    have hdata := Finset.mem_filter.mp he
    have hedge := hdata.2.1
    have hcoordinate := (Finset.mem_product.mp hdata.1).1
    have hpositive : 0 < e.1 := by
      have := (Finset.mem_Icc.mp hcoordinate).1
      omega
    exact ⟨manuscriptEdge_left_target_mem hedge hpositive,
      manuscriptEdge_left_deficient hprimes hedge⟩
  · intro e he
    have hdata := Finset.mem_filter.mp he
    have hedge := hdata.2.1
    have hcoordinate :=
      (Finset.mem_product.mp (Finset.mem_product.mp hdata.1).2).1
    have hpositive : 0 < e.2.1 := by
      have := (Finset.mem_Icc.mp hcoordinate).1
      omega
    exact ⟨manuscriptEdge_right_target_mem hedge hpositive,
      manuscriptEdge_right_deficient hprimes hedge⟩
  · intro e he
    exact manuscriptEdge_paired_targets (Finset.mem_filter.mp he).2.1
  · intro e he f hf
    have hfirst := (Finset.mem_filter.mp he).2.1
    have hsecond := (Finset.mem_filter.mp hf).2.1
    have hlabel := (Finset.mem_filter.mp (hlabels e he)).2.2.1
    exact manuscriptEdges_cross_disjoint hfirst hsecond hlabel


end Erdos689

namespace Erdos1139

/-- UNCONDITIONAL positive-density UNUSED protected reserve, extracted from
    the actual completed #689 proof.  The old all-prime covering statement
    hid these savings; here the returned labels stay in the genuine
    canonical reserve and are simultaneously removable from the conductor.

    This uses the strict full greedy matching capacity, not the former
    minimum matching size selected merely to close the covering. -/
theorem eventual_positive_density_unused_protected_reserve :
    ∃ (data : FixedSupportAnalyticData) (γ : ℝ), 0 < γ ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (a : ℕ → ℕ) (unused : Finset ℕ),
          unused ⊆ Erdos689.canonicalReserve
            data.support data.residue n data.parameter ∧
          Erdos689.protectedReserve n a unused ∧
          (∀ m ∈ Finset.Icc 1 n, 2 ≤ Erdos689.coverage n a m) ∧
          ⌊γ * ((n : ℝ) / Real.log n)⌋₊ ≤ unused.card := by
  obtain ⟨data, γ, hγ, heventual⟩ :=
    exists_fixed_support_strict_scalar_margin
  refine ⟨data, γ, hγ, ?_⟩
  filter_upwards [heventual] with n hn
  obtain ⟨hbounded, hlarge, ⟨scalar⟩⟩ := hn
  have hsupport : ∀ s ∈ data.support,
      s.Prime ∧ 3 < s ∧ s ≤ n := by
    intro s hs
    exact ⟨(data.support_valid s hs).1,
      (data.support_valid s hs).2.1, hbounded s hs⟩
  exact Erdos689.manuscript_cover_with_unused_of_strict_scalar
    data.support data.residue data.tau data.width
    hsupport hlarge data.reserve_cutoff
    scalar.degree_positive scalar.degree_left scalar.degree_right
    scalar.degree_label scalar.enough_edges scalar.strict_reserve_surplus

/-- A fixed actual CRT-location coefficient gives the same lower bound for
    the LITERAL upstream normalized extended-real limsup.  The covering may
    vary at every sufficiently large length, and all selected prime-square
    conductors are charged exactly. -/
theorem original_normalized_limsup_ge_of_eventual_crt_cost
    (A : ℝ) (hA : 0 < A)
    (hcovers : ∀ᶠ y : ℕ in atTop,
      ∃ (P squared : Finset ℕ) (a : ℕ → ℕ),
        UnrestrictedPrimeSquareDoubleCover y P squared a ∧
          A * Real.log
            (((2 * (∏ p ∈ P, selectedPrimePower squared p) + 1 : ℕ) : ℝ))
            ≤ (y : ℝ)) :
    (A : EReal) ≤
      Filter.atTop.limsup
        (fun k : ℕ =>
          (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
             (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
            Real.log ((k : ℝ) + 1) : EReal)) := by
  change
    (A : EReal) ≤
      Filter.atTop.limsup
        (fun k : ℕ =>
          (((Nat.nth AlmostPrime (k + 1) : ℝ) -
             (Nat.nth AlmostPrime k : ℝ)) /
            Real.log ((k : ℝ) + 1) : EReal))
  apply (le_limsup_iff).2
  intro b hb
  obtain ⟨a, hba, ha⟩ := EReal.exists_between_coe_real hb
  have haA : a < A := EReal.coe_lt_coe_iff.mp ha
  let B : ℝ := max a (A / 2)
  have hBpositive : 0 < B :=
    lt_of_lt_of_le (by positivity) (le_max_right a (A / 2))
  have hBA : B < A := max_lt haA (by linarith)
  have haB : a ≤ B := le_max_left a (A / 2)
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp hcovers
  apply Filter.frequently_atTop.mpr
  intro K
  let y := threshold + Nat.nth AlmostPrime (K + 2) + 1
  have hythreshold : threshold ≤ y := by dsimp [y]; omega
  obtain ⟨P, squared, residue, hcover, hcost⟩ :=
    hthreshold y hythreshold
  obtain ⟨N, k, _hlower, hupper, hkN, _hprevious, _hnext, hgap⟩ :=
    unrestricted_square_double_cover_forces_original_sequence_gap hcover
  have hylarge : Nat.nth AlmostPrime (K + 2) < y := by
    dsimp [y]
    omega
  have hgapupper :
      Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k ≤
        Nat.nth AlmostPrime (k + 1) := Nat.sub_le _ _
  have hnthlarge :
      Nat.nth AlmostPrime (K + 2) < Nat.nth AlmostPrime (k + 1) := by
    omega
  have hindexlarge : K + 2 < k + 1 :=
    (Nat.nth_lt_nth almostPrime_infinite).mp hnthlarge
  have hkpositive : 0 < k := by omega
  refine ⟨k, by omega, ?_⟩
  have hlocation :
      k + 1 ≤ 2 * (∏ p ∈ P, selectedPrimePower squared p) + 1 := by
    omega
  have hcast :
      (k : ℝ) + 1 ≤
        (((2 * (∏ p ∈ P, selectedPrimePower squared p) + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hlocation
  have hsmallpositive : 0 < (k : ℝ) + 1 := by positivity
  have hlargepositive :
      0 < (((2 * (∏ p ∈ P, selectedPrimePower squared p) + 1 : ℕ) : ℝ)) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hsmallpositive hlargepositive hcast
  have hdenominator : 0 < Real.log ((k : ℝ) + 1) := by
    apply Real.log_pos
    have hsuccessor : 1 < k + 1 := by omega
    exact_mod_cast hsuccessor
  have hscaledA : A * Real.log ((k : ℝ) + 1) ≤ (y : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog hA.le).trans hcost
  have hscaledB : B * Real.log ((k : ℝ) + 1) ≤ (y : ℝ) :=
    (mul_le_mul_of_nonneg_right hBA.le hdenominator.le).trans hscaledA
  have hmonotone : Nat.nth AlmostPrime k ≤ Nat.nth AlmostPrime (k + 1) :=
    (Nat.nth_monotone almostPrime_infinite) (by omega)
  have hgapreal :
      (y : ℝ) <
        (Nat.nth AlmostPrime (k + 1) : ℝ) -
          (Nat.nth AlmostPrime k : ℝ) := by
    have hcastgap : (y : ℝ) <
        (Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k : ℕ) := by
      exact_mod_cast hgap
    simpa [Nat.cast_sub hmonotone] using hcastgap
  have hratio :
      B <
        ((Nat.nth AlmostPrime (k + 1) : ℝ) -
          (Nat.nth AlmostPrime k : ℝ)) /
          Real.log ((k : ℝ) + 1) :=
    (lt_div_iff₀ hdenominator).mpr (hscaledB.trans_lt hgapreal)
  exact hba.trans (EReal.coe_lt_coe_iff.mpr (haB.trans_lt hratio))

/-- Every FIXED strict improvement over the primorial logarithmic conductor
    coefficient forces a genuinely stronger original normalized-limsup
    bound than one.  The fixed factor two and successor in the exact CRT
    location are absorbed explicitly; no sublinear-cost cover is assumed. -/
theorem original_normalized_limsup_gt_one_of_eventual_improved_conductor
    (r : ℝ) (hr : r < 1)
    (hcovers : ∀ᶠ y : ℕ in atTop,
      ∃ (P squared : Finset ℕ) (a : ℕ → ℕ),
        UnrestrictedPrimeSquareDoubleCover y P squared a ∧
          Real.log ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ)
            ≤ r * (y : ℝ)) :
    ∃ A : ℝ, 1 < A ∧
      (A : EReal) ≤
        Filter.atTop.limsup
          (fun k : ℕ =>
            (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
               (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
              Real.log ((k : ℝ) + 1) : EReal)) := by
  let t : ℝ := max r (1 / 2)
  have htpositive : 0 < t :=
    lt_of_lt_of_le (by norm_num) (le_max_right r (1 / 2))
  have htone : t < 1 := max_lt hr (by norm_num)
  have hrt : r ≤ t := le_max_left r (1 / 2)
  let δ : ℝ := (1 - t) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let A : ℝ := 2 / (1 + t)
  have hdenominator : 0 < 1 + t := by linarith
  have hApositive : 0 < A := by dsimp [A]; positivity
  have hAone : 1 < A := by
    dsimp [A]
    apply (lt_div_iff₀ hdenominator).mpr
    linarith
  obtain ⟨B, hB⟩ := exists_nat_ge (Real.log (3 : ℝ) / δ)
  refine ⟨A, hAone, original_normalized_limsup_ge_of_eventual_crt_cost
    A hApositive ?_⟩
  filter_upwards [hcovers, eventually_ge_atTop B] with y witness hyB
  obtain ⟨P, squared, a, hcover, hcost⟩ := witness
  refine ⟨P, squared, a, hcover, ?_⟩
  let Q : ℕ := ∏ p ∈ P, selectedPrimePower squared p
  have hQnat : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun p hp => pow_pos (hcover.1 p hp).pos _)
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQnat
  have hargpositive : 0 < (((2 * Q + 1 : ℕ) : ℝ)) := by positivity
  have hthreepositive : 0 < (3 : ℝ) * (Q : ℝ) := by positivity
  have hargbound : (((2 * Q + 1 : ℕ) : ℝ)) ≤ (3 : ℝ) * (Q : ℝ) := by
    have hnat : 2 * Q + 1 ≤ 3 * Q := by omega
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log.monotoneOn
    hargpositive hthreepositive hargbound
  rw [Real.log_mul (by norm_num) (ne_of_gt hQreal)] at hlog
  have hyreal : (B : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyB
  have hfixed : Real.log (3 : ℝ) ≤ δ * (y : ℝ) := by
    have hquotient : Real.log (3 : ℝ) / δ ≤ (y : ℝ) := hB.trans hyreal
    have hscaled := (div_le_iff₀ hδ).mp hquotient
    nlinarith
  change Real.log (Q : ℝ) ≤ r * (y : ℝ) at hcost
  have hvariable : Real.log (Q : ℝ) ≤ t * (y : ℝ) :=
    hcost.trans (mul_le_mul_of_nonneg_right hrt (Nat.cast_nonneg y))
  have hcombined :
      Real.log (((2 * Q + 1 : ℕ) : ℝ)) ≤ (δ + t) * (y : ℝ) := by
    linarith
  change A * Real.log (((2 * Q + 1 : ℕ) : ℝ)) ≤ (y : ℝ)
  calc
    A * Real.log (((2 * Q + 1 : ℕ) : ℝ)) ≤
        A * ((δ + t) * (y : ℝ)) :=
      mul_le_mul_of_nonneg_left hcombined hApositive.le
    _ = (y : ℝ) := by
      dsimp [A, δ]
      field_simp
      ring

/-- UNCONDITIONAL strict improvement over the full primorial conductor.
    The completed #689 proof actually supplies, at every sufficiently large
    length, a genuine double cover after deleting a positive-density set of
    unused protected reserve primes.  Their exact logarithmic mass yields a
    fixed coefficient `r < 1` for the actual selected CRT conductor. -/
theorem eventual_original_covers_with_strictly_improved_conductor :
    ∃ r : ℝ, r < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (P squared : Finset ℕ) (a : ℕ → ℕ),
          UnrestrictedPrimeSquareDoubleCover n P squared a ∧
            Real.log
              ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ)
              ≤ r * (n : ℝ) := by
  obtain ⟨data, γ, hγ, hreserve⟩ :=
    eventual_positive_density_unused_protected_reserve
  let r : ℝ := 1 - γ / 8
  have hr : r < 1 := by dsimp [r]; linarith
  have hsaving := eventually_pruned_conductor_linear_saving
    data.support data.residue data.parameter γ hγ
  refine ⟨r, hr, ?_⟩
  filter_upwards [hreserve, hsaving] with n hwitness hcost
  obtain ⟨a, unused, hsubset, hprotected, hcovered, hcard⟩ := hwitness
  refine ⟨Erdos689.prunedPrimeSupport n unused, ∅, a,
    protectedReserve_pruned_double_cover hprotected hcovered, ?_⟩
  exact hcost a unused hprotected hsubset hcard

/-- UNCONDITIONAL STRICT BREAKTHROUGH beyond the previous `limsup ≥ 1`
    local frontier.  The exact upstream historical normalized extended-real
    limsup is strictly greater than one.  The proof extracts and charges the
    genuinely unused reserve-prime density hidden in the completed #689
    matching; it neither assumes nor proves the infinite-limsup conjecture. -/
theorem original_normalized_limsup_strictly_gt_one_unconditional :
    (1 : EReal) <
      Filter.atTop.limsup
        (fun k : ℕ =>
          (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
             (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
            Real.log ((k : ℝ) + 1) : EReal)) := by
  obtain ⟨r, hr, hcovers⟩ :=
    eventual_original_covers_with_strictly_improved_conductor
  obtain ⟨A, hA, hbound⟩ :=
    original_normalized_limsup_gt_one_of_eventual_improved_conductor
      r hr hcovers
  have hstrict : (1 : EReal) < (A : EReal) := by
    exact_mod_cast hA
  exact hstrict.trans_le hbound

/-- Equivalent quantified positive-gap form of the strict improvement:
    some fixed REAL `η > 0` is a certified lower bound in excess of one for
    the literal original normalized extended-real limsup. -/
theorem original_normalized_limsup_ge_one_add_positive_unconditional :
    ∃ η : ℝ, 0 < η ∧
      ((1 + η : ℝ) : EReal) ≤
        Filter.atTop.limsup
          (fun k : ℕ =>
            (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
               (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
              Real.log ((k : ℝ) + 1) : EReal)) := by
  obtain ⟨r, hr, hcovers⟩ :=
    eventual_original_covers_with_strictly_improved_conductor
  obtain ⟨A, hA, hbound⟩ :=
    original_normalized_limsup_gt_one_of_eventual_improved_conductor
      r hr hcovers
  refine ⟨A - 1, by linarith, ?_⟩
  have hidentity : (1 : ℝ) + (A - 1) = A := by ring
  rw [hidentity]
  exact hbound


end Erdos1139
