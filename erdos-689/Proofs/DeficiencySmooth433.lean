import DeficiencyDensity433

/-!
# Arbitrary smooth even coefficients inside the actual initial deficiency

The coefficient `c` may have arbitrary powers of two and arbitrary powers of
switched support primes. Excluding the single prime parameter `p = 2` makes
distinct smooth-core targets `c * p` globally disjoint. That finite exclusion
does not alter the exact fixed-progression prime density `1 / (c * φ(W))`.

Every finite family of missed reduced smooth-core residues consequently injects
simultaneously into the genuine initial-deficiency ledger. The theorem covers
all dyadic shells and all support-prime exponents, but does not supply the
infinite tail/interchange or the matching deficiency upper bound.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- A coefficient supported only on two and the switched auxiliary primes. -/
def deficiencySmoothCoefficient (S : Finset ℕ) (c : ℕ) : Prop :=
  0 < c ∧ 2 ∣ c ∧
    ∀ p : ℕ, p.Prime → p ∣ c → p = 2 ∨ p ∈ S

/-- Prime values in the exact fixed progression, with the exceptional prime two removed. -/
noncomputable def smoothDeficiencyPrimeStratum
    (S : Finset ℕ) (c r n : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Icc 1 (n / c)).filter fun p =>
    p.Prime ∧ p % (∏ s ∈ S, s) = r % (∏ s ∈ S, s)).erase 2

/-- Any even smooth-times-prime target missed by the support has at most one old hit. -/
theorem initialAssignment_even_smooth_prime_coverage_general
    {S : Finset ℕ} {b : ℕ → ℕ} {n c p : ℕ}
    (hsmooth : deficiencySmoothCoefficient S c)
    (hprime : p.Prime)
    (hmiss : switchedHits S b (c * p) = 0) :
    coverage n (initialAssignment S b) (c * p) ≤ 1 := by
  have hsubset : coveredPrimes n (initialAssignment S b) (c * p) ⊆ {p} := by
    intro q hq
    obtain ⟨_, _, hqprime, hhit⟩ := mem_coveredPrimes_iff.mp hq
    have hqnotwo : q ≠ 2 := by
      intro heq
      subst q
      have htarget : (c * p) % 2 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hsmooth.2.1 p)
      change (initialAssignment S b 2) % 2 = (c * p) % 2 at hhit
      simp [initialAssignment, htarget] at hhit
    have hqnotS : q ∉ S := by
      intro hmem
      have haux : q ∈ S.filter (fun s => b s ≡ c * p [MOD s]) := by
        apply Finset.mem_filter.mpr
        refine ⟨hmem, ?_⟩
        simpa [initialAssignment, hqnotwo, hmem] using hhit
      have hpositive : 0 < switchedHits S b (c * p) :=
        Finset.card_pos.mpr ⟨q, haux⟩
      omega
    have hzero : initialAssignment S b q = 0 := by
      simp [initialAssignment, hqnotwo, hqnotS]
    have hdiv := (zero_class_hit_iff_dvd hzero).mp hhit
    rcases hqprime.dvd_mul.mp hdiv with hcore | hp
    · rcases hsmooth.2.2 q hqprime hcore with htwo | hsupport
      · exact False.elim (hqnotwo htwo)
      · exact False.elim (hqnotS hsupport)
    · have heq := (Nat.prime_dvd_prime_iff_eq hqprime hprime).mp hp
      simp [heq]
  change (coveredPrimes n (initialAssignment S b) (c * p)).card ≤ 1
  simpa using Finset.card_le_card hsubset

/-- A reduced smooth stratum contains neither two nor any switched support prime. -/
theorem smoothDeficiencyPrimeStratum_external
    {S : Finset ℕ} {c r n p : ℕ}
    (hcoprime : Nat.Coprime r (∏ s ∈ S, s))
    (hp : p ∈ smoothDeficiencyPrimeStratum S c r n) :
    p ≠ 2 ∧ p ∉ S := by
  obtain ⟨hnotwo, hbase⟩ := Finset.mem_erase.mp hp
  have hprime := (Finset.mem_filter.mp hbase).2.1
  have hresidue := (Finset.mem_filter.mp hbase).2.2
  let W := ∏ s ∈ S, s
  have hp_coprime : Nat.Coprime p W := by
    change Nat.gcd p W = 1
    have hfirst : Nat.gcd p W = Nat.gcd (p % W) W := by
      rw [Nat.gcd_comm p W, Nat.gcd_rec]
    have hsecond : Nat.gcd r W = Nat.gcd (r % W) W := by
      rw [Nat.gcd_comm r W, Nat.gcd_rec]
    rw [hfirst, hresidue, ← hsecond]
    exact hcoprime
  refine ⟨hnotwo, ?_⟩
  intro hmem
  have hdiv : p ∣ W := Finset.dvd_prod_of_mem (fun s : ℕ => s) hmem
  exact (hprime.coprime_iff_not_dvd.mp hp_coprime) hdiv

/-- A smooth stratum inherits its exact zero-hit condition from its reduced residue. -/
theorem smoothDeficiencyPrimeStratum_switchedHits_zero
    {S : Finset ℕ} {b : ℕ → ℕ} {c r n p : ℕ}
    (hp : p ∈ smoothDeficiencyPrimeStratum S c r n)
    (hmiss : switchedHits S b (c * r) = 0) :
    switchedHits S b (c * p) = 0 := by
  have hresidue := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2.2
  have hproduct : (c * p) % (∏ s ∈ S, s) =
      (c * r) % (∏ s ∈ S, s) := by
    calc
      (c * p) % (∏ s ∈ S, s) =
          (c % (∏ s ∈ S, s) * (p % (∏ s ∈ S, s))) %
            (∏ s ∈ S, s) := Nat.mul_mod c p _
      _ = (c % (∏ s ∈ S, s) * (r % (∏ s ∈ S, s))) %
            (∏ s ∈ S, s) := by rw [hresidue]
      _ = (c * r) % (∏ s ∈ S, s) := (Nat.mul_mod c r _).symm
  rw [switchedHits_eq_of_mod_product_eq hproduct, hmiss]

/-- Distinct even smooth coefficients cannot share an external-prime target. -/
theorem smoothDeficiencyTarget_core_prime_injective
    {S : Finset ℕ} {c c' p p' : ℕ}
    (hsmooth' : deficiencySmoothCoefficient S c')
    (hp : p.Prime) (hp' : p'.Prime)
    (hpnotwo : p ≠ 2) (hpoutside : p ∉ S)
    (heq : c * p = c' * p') :
    c = c' ∧ p = p' := by
  have hdiv : p ∣ c' * p' := by
    rw [← heq]
    exact dvd_mul_left p c
  rcases hp.dvd_mul.mp hdiv with hcore | hprime
  · rcases hsmooth'.2.2 p hp hcore with htwo | hsupport
    · exact False.elim (hpnotwo htwo)
    · exact False.elim (hpoutside hsupport)
  · have hpequal := (Nat.prime_dvd_prime_iff_eq hp hp').mp hprime
    subst p'
    exact ⟨Nat.mul_right_cancel hp.pos heq, rfl⟩

/-- The reciprocal prime-counting normalization tends to zero. -/
theorem inverse_prime_counting_scale_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop
    1 0 1 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext n
  simp [div_eq_mul_inv, mul_comm]

/-- Removing the single prime two leaves the exact fixed smooth-core PNT density. -/
theorem smoothDeficiencyPrimeStratum_asymptotic
    (S : Finset ℕ) (c r : ℕ)
    (hsupport : ∀ s ∈ S, 0 < s)
    (hsmooth : deficiencySmoothCoefficient S c)
    (hcoprime : Nat.Coprime r (∏ s ∈ S, s)) :
    Tendsto
      (fun n : ℕ =>
        ((smoothDeficiencyPrimeStratum S c r n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop
      (nhds ((1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
        ((c : ℝ)⁻¹))) := by
  have hceq : 2 * (c / 2) = c :=
    Nat.two_mul_div_two_of_even (even_iff_two_dvd.mpr hsmooth.2.1)
  have hcpos := hsmooth.1
  have hdpos : 0 < c / 2 := by omega
  have hbase := fixedDeficiencyPrimeStratum_asymptotic
    S (c / 2) r hsupport hdpos hcoprime
  rw [hceq] at hbase
  by_cases htwo : 2 % (∏ s ∈ S, s) = r % (∏ s ∈ S, s)
  · have hsub := hbase.sub inverse_prime_counting_scale_tendsto_zero
    simp only [sub_zero] at hsub
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop (2 * c)] with n hn
    have hbound : 2 ≤ n / c :=
      (Nat.le_div_iff_mul_le hsmooth.1).mpr (by simpa [Nat.mul_comm] using hn)
    have hmem : 2 ∈ fixedDeficiencyPrimeStratum S (c / 2) r n := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by norm_num, ?_⟩,
        Nat.prime_two, htwo⟩
      simpa [hceq] using hbound
    have hcard := Finset.card_erase_add_one hmem
    have hnat :
        (((fixedDeficiencyPrimeStratum S (c / 2) r n).erase 2).card : ℝ) + 1 =
          ((fixedDeficiencyPrimeStratum S (c / 2) r n).card : ℝ) := by
      exact_mod_cast hcard
    have herase : smoothDeficiencyPrimeStratum S c r n =
        (fixedDeficiencyPrimeStratum S (c / 2) r n).erase 2 := by
      unfold smoothDeficiencyPrimeStratum fixedDeficiencyPrimeStratum
      rw [hceq]
    rw [herase, ← sub_div]
    congr 1
    linarith
  · apply hbase.congr'
    filter_upwards [] with n
    have hnotmem : 2 ∉ fixedDeficiencyPrimeStratum S (c / 2) r n := by
      intro hmem
      exact htwo (Finset.mem_filter.mp hmem).2.2
    have herase : smoothDeficiencyPrimeStratum S c r n =
        (fixedDeficiencyPrimeStratum S (c / 2) r n).erase 2 := by
      unfold smoothDeficiencyPrimeStratum fixedDeficiencyPrimeStratum
      rw [hceq]
    rw [herase, Finset.erase_eq_self.mpr hnotmem]

/-- The exact nonvacuous smooth-core/residue admissibility condition. -/
def admissibleSmoothDeficiencyCore
    (S : Finset ℕ) (b : ℕ → ℕ) (v : ℕ × ℕ) : Prop :=
  deficiencySmoothCoefficient S v.1 ∧
    v.2 < ∏ s ∈ S, s ∧ Nat.Coprime v.2 (∏ s ∈ S, s) ∧
      switchedHits S b (v.1 * v.2) = 0

/-- Actual targets produced by an arbitrary even smooth-core stratum. -/
noncomputable def smoothDeficiencyTargets
    (S : Finset ℕ) (c r n : ℕ) : Finset ℕ := by
  classical
  exact (smoothDeficiencyPrimeStratum S c r n).image fun p => c * p

/-- Positive smooth multiplication preserves every stratum's exact prime count. -/
theorem smoothDeficiencyTargets_card (S : Finset ℕ) (c r n : ℕ)
    (hc : 0 < c) :
    (smoothDeficiencyTargets S c r n).card =
      (smoothDeficiencyPrimeStratum S c r n).card := by
  unfold smoothDeficiencyTargets
  exact Finset.card_image_of_injective _
    (fun p q h => Nat.mul_left_cancel hc h)

/-- Distinct reduced even smooth-core pairs have disjoint actual target sets. -/
theorem smoothDeficiencyTargets_disjoint
    {S : Finset ℕ} {c c' r r' n : ℕ}
    (hsmooth' : deficiencySmoothCoefficient S c')
    (hr : r < ∏ s ∈ S, s) (hr' : r' < ∏ s ∈ S, s)
    (hcoprime : Nat.Coprime r (∏ s ∈ S, s))
    (hne : (c, r) ≠ (c', r')) :
    Disjoint (smoothDeficiencyTargets S c r n)
      (smoothDeficiencyTargets S c' r' n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro m hm hm'
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hm
  obtain ⟨p', hp', heq'⟩ := Finset.mem_image.mp hm'
  have htarget : c * p = c' * p' := heq.trans heq'.symm
  have hpprime := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2.1
  have hp'prime := (Finset.mem_filter.mp (Finset.mem_erase.mp hp').2).2.1
  obtain ⟨hpnotwo, hpoutside⟩ := smoothDeficiencyPrimeStratum_external hcoprime hp
  obtain ⟨hceq, hpeq⟩ := smoothDeficiencyTarget_core_prime_injective
    hsmooth' hpprime hp'prime hpnotwo hpoutside htarget
  have hres := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2.2
  have hres' := (Finset.mem_filter.mp (Finset.mem_erase.mp hp').2).2.2
  have hr_eq : r = r' := by
    calc
      r = r % (∏ s ∈ S, s) := (Nat.mod_eq_of_lt hr).symm
      _ = p % (∏ s ∈ S, s) := hres.symm
      _ = p' % (∏ s ∈ S, s) := by rw [hpeq]
      _ = r' % (∏ s ∈ S, s) := hres'
      _ = r' := Nat.mod_eq_of_lt hr'
  exact hne (Prod.ext hceq hr_eq)

/-- All finite families of arbitrary even smooth cores inject into actual deficiency. -/
theorem finiteSmoothDeficiencyFamily_card_le_initial_deficiency
    (S : Finset ℕ) (b : ℕ → ℕ) (F : Finset (ℕ × ℕ)) (n : ℕ)
    (hfamily : ∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) :
    (∑ v ∈ F, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) ≤
      deficiency n (initialAssignment S b) := by
  classical
  let target : (ℕ × ℕ) → Finset ℕ :=
    fun v => smoothDeficiencyTargets S v.1 v.2 n
  let union := F.biUnion target
  have hdisjoint : (↑F : Set (ℕ × ℕ)).PairwiseDisjoint target := by
    intro v hv v' hv' hne
    obtain ⟨_, hr, hcoprime, _⟩ := hfamily v hv
    obtain ⟨hsmooth', hr', _, _⟩ := hfamily v' hv'
    exact smoothDeficiencyTargets_disjoint hsmooth' hr hr' hcoprime hne
  have hsubset : union ⊆ Finset.Icc 1 n := by
    intro m hm
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hm
    have hcoeff := (hfamily v hv).1.1
    have hinterval :=
      (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
    have hppos := (Finset.mem_Icc.mp hinterval).1
    have hpbound := (Finset.mem_Icc.mp hinterval).2
    subst m
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr
        (ne_of_gt (Nat.mul_pos hcoeff (by omega)))
    · have hbound := (Nat.le_div_iff_mul_le hcoeff).mp hpbound
      simpa [Nat.mul_comm] using hbound
  have hcard : union.card =
      ∑ v ∈ F, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card := by
    rw [Finset.card_biUnion hdisjoint]
    apply Finset.sum_congr rfl
    intro v hv
    exact smoothDeficiencyTargets_card S v.1 v.2 n (hfamily v hv).1.1
  calc
    (∑ v ∈ F, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) =
        union.card := hcard.symm
    _ = ∑ m ∈ union, 1 := Finset.card_eq_sum_ones union
    _ ≤ ∑ m ∈ union,
        (2 - coverage n (initialAssignment S b) m) := by
          apply Finset.sum_le_sum
          intro m hm
          obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hm
          obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hm
          obtain ⟨hsmooth, _, _, hmiss⟩ := hfamily v hv
          have hprime :=
            (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2.1
          subst m
          have hzero := smoothDeficiencyPrimeStratum_switchedHits_zero hp hmiss
          have hdef := initialAssignment_even_smooth_prime_coverage_general
            (n := n) hsmooth hprime hzero
          omega
    _ ≤ ∑ m ∈ Finset.Icc 1 n,
        (2 - coverage n (initialAssignment S b) m) :=
          Finset.sum_le_sum_of_subset hsubset
    _ = deficiency n (initialAssignment S b) := rfl

/-- Every finite family, including arbitrary prime powers and dyadic shells, has exact density. -/
theorem finiteSmoothDeficiencyFamily_asymptotic
    (S : Finset ℕ) (b : ℕ → ℕ) (F : Finset (ℕ × ℕ))
    (hsupport : ∀ s ∈ S, s.Prime)
    (hfamily : ∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) :
    Tendsto
      (fun n : ℕ =>
        ((∑ v ∈ F, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop
      (nhds (∑ v ∈ F,
        (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
          ((v.1 : ℝ)⁻¹))) := by
  have hsum := tendsto_finsetSum F (fun v hv =>
    smoothDeficiencyPrimeStratum_asymptotic S v.1 v.2
      (fun s hs => (hsupport s hs).pos)
      (hfamily v hv).1 (hfamily v hv).2.2.1)
  convert hsum using 1
  funext n
  simp [Finset.sum_div]

/-- The actual deficiency dominates every finite truncation of the complete smooth-core sum. -/
theorem initial_deficiency_eventual_lower_bound_of_finite_smooth_family
    (S : Finset ℕ) (b : ℕ → ℕ) (F : Finset (ℕ × ℕ))
    (hsupport : ∀ s ∈ S, s.Prime)
    (hfamily : ∀ v ∈ F, admissibleSmoothDeficiencyCore S b v)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∑ v ∈ F,
        (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
          ((v.1 : ℝ)⁻¹)) - ε ≤
        (deficiency n (initialAssignment S b) : ℝ) /
          ((n : ℝ) / Real.log n) := by
  have hasymptotic := finiteSmoothDeficiencyFamily_asymptotic
    S b F hsupport hfamily
  have hbelow : ∀ᶠ n : ℕ in atTop,
      (∑ v ∈ F,
        (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
          ((v.1 : ℝ)⁻¹)) - ε <
        ((∑ v ∈ F, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
          ((n : ℝ) / Real.log n) :=
    (tendsto_order.mp hasymptotic).1 _ (sub_lt_self _ hε)
  filter_upwards [hbelow, eventually_ge_atTop 2] with n hn_lower hn
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 1 < n)
  have hden : 0 < (n : ℝ) / Real.log n :=
    div_pos (by exact_mod_cast (by omega : 0 < n)) (Real.log_pos hn_real)
  have hcard := finiteSmoothDeficiencyFamily_card_le_initial_deficiency
    S b F n hfamily
  have hcard_real :
      ((∑ v ∈ F, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) ≤
        (deficiency n (initialAssignment S b) : ℝ) := by
    exact_mod_cast hcard
  exact (le_of_lt hn_lower).trans
    ((div_le_div_iff_of_pos_right hden).mpr hcard_real)

#print axioms initialAssignment_even_smooth_prime_coverage_general
#print axioms smoothDeficiencyPrimeStratum_external
#print axioms smoothDeficiencyPrimeStratum_switchedHits_zero
#print axioms smoothDeficiencyTarget_core_prime_injective
#print axioms inverse_prime_counting_scale_tendsto_zero
#print axioms smoothDeficiencyPrimeStratum_asymptotic
#print axioms smoothDeficiencyTargets_card
#print axioms smoothDeficiencyTargets_disjoint
#print axioms finiteSmoothDeficiencyFamily_card_le_initial_deficiency
#print axioms finiteSmoothDeficiencyFamily_asymptotic
#print axioms initial_deficiency_eventual_lower_bound_of_finite_smooth_family

end Erdos689
