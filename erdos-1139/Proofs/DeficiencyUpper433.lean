module

public import DeficiencyRectangle433
public import DeficiencyClassification
public import DeficiencySmoothTail433

@[expose] public section


/-!
# Upper-side structural decomposition of the actual initial deficiency

This module concerns the genuine closed-interval quantity
`deficiency n (initialAssignment S b)`.  It separates targets with no
external prime factor from genuinely deficient targets with their unique
external prime.  The former are smooth over the fixed support enlarged by
two; the latter each contribute exactly one demand token.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Actual deficient targets possessing at least one outside prime divisor. -/
noncomputable def initialDeficiencyExternalTargets
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun m =>
    coverage n (initialAssignment S b) m < 2 ∧
      (externalPrimeFactors S m).Nonempty

/-- The exact deficiency weight from targets with no outside prime divisor. -/
noncomputable def initialDeficiencyExternalFreeWeight
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ := by
  classical
  exact ∑ m ∈ (Finset.Icc 1 n).filter
    (fun m => externalPrimeFactors S m = ∅),
      (2 - coverage n (initialAssignment S b) m)

/-- An outside-prime-free target is supported precisely on two and `S`. -/
theorem externalPrimeFactors_eq_empty_iff_primeFactors_subset
    (S : Finset ℕ) (m : ℕ) :
    externalPrimeFactors S m = ∅ ↔ m.primeFactors ⊆ insert 2 S := by
  classical
  constructor
  · intro hempty p hp
    by_cases htwo : p = 2
    · simp [htwo]
    · have hsupport : p ∈ S := by
        by_contra hnot
        have hexternal : p ∈ externalPrimeFactors S m :=
          Finset.mem_filter.mpr ⟨hp, htwo, hnot⟩
        rw [hempty] at hexternal
        simp at hexternal
      exact Finset.mem_insert_of_mem hsupport
  · intro hsubset
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    obtain ⟨hfactor, htwo, hsupport⟩ := Finset.mem_filter.mp hp
    rcases Finset.mem_insert.mp (hsubset hfactor) with heq | hmem
    · exact htwo heq
    · exact hsupport hmem

/-- Every genuinely deficient target with an outside prime has exactly one hit. -/
theorem initialDeficiencyExternalTargets_coverage_eq_one
    {S : Finset ℕ} {b : ℕ → ℕ} {n m : ℕ}
    (hm : m ∈ initialDeficiencyExternalTargets S b n) :
    coverage n (initialAssignment S b) m = 1 := by
  obtain ⟨hinterval, hdeficient, hexternal⟩ := Finset.mem_filter.mp hm
  obtain ⟨hone, hmn⟩ := Finset.mem_Icc.mp hinterval
  have hcard : 0 < (externalPrimeFactors S m).card :=
    Finset.card_pos.mpr hexternal
  have hbound := externalPrimeFactors_card_le_coverage
    (S := S) (b := b) hone hmn
  omega

/-- Every genuinely deficient target with an outside prime has exactly one
distinct outside prime. -/
theorem initialDeficiencyExternalTargets_external_card_eq_one
    {S : Finset ℕ} {b : ℕ → ℕ} {n m : ℕ}
    (hm : m ∈ initialDeficiencyExternalTargets S b n) :
    (externalPrimeFactors S m).card = 1 := by
  obtain ⟨hinterval, hdeficient, hexternal⟩ := Finset.mem_filter.mp hm
  obtain ⟨hone, hmn⟩ := Finset.mem_Icc.mp hinterval
  have hpositive := Finset.card_pos.mpr hexternal
  have hupper := deficient_externalPrimeFactors_card_le_one
    (S := S) (b := b) hone hmn hdeficient
  omega

/-- The actual deficiency is exactly its outside-prime-free weight plus one
token for each genuinely deficient target with an outside prime. -/
theorem initial_deficiency_eq_externalFreeWeight_add_externalTargets
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    deficiency n (initialAssignment S b) =
      initialDeficiencyExternalFreeWeight S b n +
        (initialDeficiencyExternalTargets S b n).card := by
  classical
  let interval : Finset ℕ := Finset.Icc 1 n
  let token : ℕ → ℕ := fun m => 2 - coverage n (initialAssignment S b) m
  have hsplit := Finset.sum_filter_add_sum_filter_not interval
    (fun m => externalPrimeFactors S m = ∅) token
  have hsecond :
      (∑ m ∈ interval.filter
        (fun m => ¬ externalPrimeFactors S m = ∅), token m) =
        (initialDeficiencyExternalTargets S b n).card := by
    rw [Finset.card_eq_sum_ones]
    have hfilter :
        initialDeficiencyExternalTargets S b n =
          (interval.filter (fun m => ¬ externalPrimeFactors S m = ∅)).filter
            (fun m => coverage n (initialAssignment S b) m < 2) := by
      ext m
      simp only [initialDeficiencyExternalTargets, interval, Finset.mem_filter]
      constructor
      · rintro ⟨hinterval, hdef, hnonempty⟩
        exact ⟨⟨hinterval, Finset.nonempty_iff_ne_empty.mp hnonempty⟩, hdef⟩
      · rintro ⟨⟨hinterval, hne⟩, hdef⟩
        exact ⟨hinterval, hdef, Finset.nonempty_iff_ne_empty.mpr hne⟩
    rw [hfilter]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hdef : coverage n (initialAssignment S b) m < 2
    · have hinterval := (Finset.mem_filter.mp hm).1
      have hne := (Finset.mem_filter.mp hm).2
      have htarget : m ∈ initialDeficiencyExternalTargets S b n := by
        apply Finset.mem_filter.mpr
        exact ⟨hinterval, hdef, Finset.nonempty_iff_ne_empty.mpr hne⟩
      have hcoverage := initialDeficiencyExternalTargets_coverage_eq_one htarget
      simp [token, hcoverage]
    · have hle : 2 ≤ coverage n (initialAssignment S b) m := by omega
      simp [token, hdef, Nat.sub_eq_zero_of_le hle]
  change (∑ m ∈ interval, token m) = _
  rw [← hsplit, hsecond]
  rfl

/-- The entire outside-prime-free contribution is bounded by twice the number
of actual positive targets smooth over the fixed support `insert 2 S`. -/
theorem initialDeficiencyExternalFreeWeight_le_smooth
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    initialDeficiencyExternalFreeWeight S b n ≤
      2 * (supportSmoothNumbersUpTo (insert 2 S) n).card := by
  classical
  let free : Finset ℕ :=
    (Finset.Icc 1 n).filter fun m => externalPrimeFactors S m = ∅
  have hsubset : free ⊆ supportSmoothNumbersUpTo (insert 2 S) n := by
    intro m hm
    obtain ⟨hinterval, hempty⟩ := Finset.mem_filter.mp hm
    apply Finset.mem_filter.mpr
    exact ⟨hinterval,
      (externalPrimeFactors_eq_empty_iff_primeFactors_subset S m).mp hempty⟩
  calc
    initialDeficiencyExternalFreeWeight S b n =
        ∑ m ∈ free, (2 - coverage n (initialAssignment S b) m) := rfl
    _ ≤ ∑ _m ∈ free, 2 := by
      apply Finset.sum_le_sum
      intro m hm
      omega
    _ = 2 * free.card := by simp [Nat.mul_comm]
    _ ≤ 2 * (supportSmoothNumbersUpTo (insert 2 S) n).card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)

/-- Sharp unconditional structural upper bound for the actual deficiency. -/
theorem initial_deficiency_le_externalTargets_add_twice_smooth
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    deficiency n (initialAssignment S b) ≤
      (initialDeficiencyExternalTargets S b n).card +
        2 * (supportSmoothNumbersUpTo (insert 2 S) n).card := by
  rw [initial_deficiency_eq_externalFreeWeight_add_externalTargets]
  have h := initialDeficiencyExternalFreeWeight_le_smooth S b n
  omega

/-- The outside-prime-free ledger is exactly the already formalized actual
deficiency restricted to the fixed support enlarged by two. -/
theorem initialDeficiencyExternalFreeWeight_eq_supportSmoothInitialDeficiency
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    initialDeficiencyExternalFreeWeight S b n =
      supportSmoothInitialDeficiency S (insert 2 S) b n := by
  classical
  unfold initialDeficiencyExternalFreeWeight supportSmoothInitialDeficiency
    supportSmoothNumbersUpTo
  congr 1
  ext m
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ =>
    externalPrimeFactors_eq_empty_iff_primeFactors_subset S m

/-- All targets without an outside prime contribute zero density on the
actual prime-counting normalization. -/
theorem initialDeficiencyExternalFreeWeight_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ =>
        (initialDeficiencyExternalFreeWeight S b n : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  simpa only [initialDeficiencyExternalFreeWeight_eq_supportSmoothInitialDeficiency]
    using supportSmoothInitialDeficiency_normalized_tendsto_zero S (insert 2 S) b

/-- The sharp upper-side reduction: actual normalized deficiency differs from
the normalized cardinality of its unique-outside-prime targets by `o(1)`. -/
theorem initial_deficiency_upper_reduction
    (S : Finset ℕ) (b : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ =>
        (deficiency n (initialAssignment S b) : ℝ) /
            ((n : ℝ) / Real.log n) -
          ((initialDeficiencyExternalTargets S b n).card : ℝ) /
            ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  have hfree := initialDeficiencyExternalFreeWeight_normalized_tendsto_zero S b
  apply hfree.congr'
  filter_upwards [] with n
  rw [initial_deficiency_eq_externalFreeWeight_add_externalTargets]
  push_cast
  ring

/-- The full initial-deficiency asymptotic is exactly equivalent to the
noncircular prime-stratum asymptotic for its outside-prime target set. -/
theorem initial_deficiency_asymptotic_iff_externalTargets
    (S : Finset ℕ) (b : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ =>
        (deficiency n (initialAssignment S b) : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) ↔
    Tendsto
      (fun n : ℕ =>
        ((initialDeficiencyExternalTargets S b n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) := by
  have hfree := initialDeficiencyExternalFreeWeight_normalized_tendsto_zero S b
  constructor
  · intro hdeficiency
    have hsub := hdeficiency.sub hfree
    simp only [sub_zero] at hsub
    apply hsub.congr'
    filter_upwards [] with n
    rw [initial_deficiency_eq_externalFreeWeight_add_externalTargets]
    push_cast
    ring
  · intro hexternal
    have hadd := hfree.add hexternal
    simp only [zero_add] at hadd
    apply hadd.congr'
    filter_upwards [] with n
    rw [initial_deficiency_eq_externalFreeWeight_add_externalTargets]
    push_cast
    ring

/-- Actual deficient targets whose unique outside prime occurs to exponent one. -/
noncomputable def initialDeficiencySimpleExternalTargets
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (initialDeficiencyExternalTargets S b n).filter fun m =>
    ¬ ∃ p ∈ externalPrimeFactors S m, p ^ 2 ∣ m

/-- Actual deficient targets whose unique outside prime occurs to higher power. -/
noncomputable def initialDeficiencyPrimePowerTargets
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (initialDeficiencyExternalTargets S b n).filter fun m =>
    ∃ p ∈ externalPrimeFactors S m, p ^ 2 ∣ m

/-- Exact disjoint outside-prime exponent split; no target is dropped or counted
twice, including the possible fixed external prime three. -/
theorem initialDeficiencyExternalTargets_card_eq_simple_add_primePower
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    (initialDeficiencyExternalTargets S b n).card =
      (initialDeficiencySimpleExternalTargets S b n).card +
        (initialDeficiencyPrimePowerTargets S b n).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := initialDeficiencyExternalTargets S b n)
    (fun m => ∃ p ∈ externalPrimeFactors S m, p ^ 2 ∣ m)
  simpa [initialDeficiencySimpleExternalTargets,
    initialDeficiencyPrimePowerTargets, Nat.add_comm] using hsplit.symm

/-- Exact three-way decomposition of the actual demand ledger. -/
theorem initial_deficiency_eq_externalFreeWeight_add_simple_add_primePower
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    deficiency n (initialAssignment S b) =
      initialDeficiencyExternalFreeWeight S b n +
        (initialDeficiencySimpleExternalTargets S b n).card +
          (initialDeficiencyPrimePowerTargets S b n).card := by
  rw [initial_deficiency_eq_externalFreeWeight_add_externalTargets,
    initialDeficiencyExternalTargets_card_eq_simple_add_primePower]
  omega

/-- Sharp finite upper bound with the main exponent-one prime strata, the exact
higher-prime-power exception, and only the fixed-support smooth error. -/
theorem initial_deficiency_le_simple_add_primePower_add_twice_smooth
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    deficiency n (initialAssignment S b) ≤
      (initialDeficiencySimpleExternalTargets S b n).card +
        (initialDeficiencyPrimePowerTargets S b n).card +
          2 * (supportSmoothNumbersUpTo (insert 2 S) n).card := by
  rw [initial_deficiency_eq_externalFreeWeight_add_simple_add_primePower]
  have h := initialDeficiencyExternalFreeWeight_le_smooth S b n
  omega

/-- Under the actual available-support hypotheses, an outside-prime deficient
target must be even and receive no switched-support hit. -/
theorem initialDeficiencyExternalTargets_even_and_switchedHits_zero
    {S : Finset ℕ} {b : ℕ → ℕ} {n m : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hn : 2 ≤ n)
    (hm : m ∈ initialDeficiencyExternalTargets S b n) :
    2 ∣ m ∧ switchedHits S b m = 0 := by
  have hinterval := (Finset.mem_filter.mp hm).1
  obtain ⟨hone, hmn⟩ := Finset.mem_Icc.mp hinterval
  have hcoverage := initialDeficiencyExternalTargets_coverage_eq_one hm
  have hcard := initialDeficiencyExternalTargets_external_card_eq_one hm
  have hledger := initialAssignment_coverage_eq_parity_add_switched_add_external
    (S := S) (b := b) hsupport htwo hone hmn hn
  rw [hcoverage, hcard] at hledger
  have hmiss : switchedHits S b m = 0 := by omega
  have hnotodd : m % 2 ≠ 1 := by
    intro hodd
    simp [hodd] at hledger
  have hmod : m % 2 = 0 := by
    have hlt := Nat.mod_lt m (by norm_num : 0 < 2)
    omega
  exact ⟨Nat.dvd_of_mod_eq_zero hmod, hmiss⟩

/-- The unique outside-prime factor of an exponent-one target actually occurs
to factorization exponent one. -/
theorem initialDeficiencySimpleExternalTargets_factorization_eq_one
    {S : Finset ℕ} {b : ℕ → ℕ} {n m p : ℕ}
    (hm : m ∈ initialDeficiencySimpleExternalTargets S b n)
    (hp : p ∈ externalPrimeFactors S m) :
    m.factorization p = 1 := by
  obtain ⟨hexternal, hnotpower⟩ := Finset.mem_filter.mp hm
  obtain ⟨hinterval, _, _⟩ := Finset.mem_filter.mp hexternal
  have hmpos := (Finset.mem_Icc.mp hinterval).1
  obtain ⟨hfactor, _, _⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hfactor
  have hdiv := Nat.dvd_of_mem_primeFactors hfactor
  have hpositive := hprime.factorization_pos_of_dvd (by omega : m ≠ 0) hdiv
  have hnotlarge : ¬ 2 ≤ m.factorization p := by
    intro hlarge
    exact hnotpower
      ⟨p, hp, (hprime.pow_dvd_iff_le_factorization (by omega)).mpr hlarge⟩
  omega

/-- Every genuine exponent-one outside-prime target has its exact intended
representation by an even support-smooth core and a missed external prime. -/
theorem initialDeficiencySimpleExternalTargets_smooth_prime_representation
    {S : Finset ℕ} {b : ℕ → ℕ} {n m : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hn : 2 ≤ n)
    (hm : m ∈ initialDeficiencySimpleExternalTargets S b n) :
    ∃ c p : ℕ,
      deficiencySmoothCoefficient S c ∧ p.Prime ∧ p ≠ 2 ∧ p ∉ S ∧
        ¬ p ∣ c ∧ m = c * p ∧ switchedHits S b m = 0 := by
  obtain ⟨hexternal, _⟩ := Finset.mem_filter.mp hm
  obtain ⟨hinterval, hdeficient, hnonempty⟩ := Finset.mem_filter.mp hexternal
  obtain ⟨hmpos, hmn⟩ := Finset.mem_Icc.mp hinterval
  obtain ⟨p, hp⟩ := hnonempty
  obtain ⟨hfactor, hpnotwo, hpnotS⟩ := Finset.mem_filter.mp hp
  have hpprime := Nat.prime_of_mem_primeFactors hfactor
  have hfactorization :=
    initialDeficiencySimpleExternalTargets_factorization_eq_one hm hp
  let c : ℕ := m / p ^ m.factorization p
  have hcpos : 0 < c := Nat.ordCompl_pos p (by omega)
  have hnotdiv : ¬ p ∣ c := Nat.not_dvd_ordCompl hpprime (by omega)
  have hrepr : m = c * p := by
    have hproduct := Nat.ordProj_mul_ordCompl_eq_self m p
    simpa [c, hfactorization, Nat.mul_comm] using hproduct.symm
  obtain ⟨hmeven, hmiss⟩ :=
    initialDeficiencyExternalTargets_even_and_switchedHits_zero
      hsupport htwo hn hexternal
  have hceven : 2 ∣ c := by
    rw [hrepr] at hmeven
    rcases Nat.prime_two.dvd_mul.mp hmeven with hc | hprime
    · exact hc
    · have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpprime).mp hprime
      exact False.elim (hpnotwo heq.symm)
  have hcsmooth : deficiencySmoothCoefficient S c := by
    refine ⟨hcpos, hceven, ?_⟩
    intro q hqprime hqdiv
    by_cases hqnotwo : q = 2
    · exact Or.inl hqnotwo
    · by_cases hqS : q ∈ S
      · exact Or.inr hqS
      · have hqm : q ∣ m := by
          rw [hrepr]
          exact dvd_mul_of_dvd_left hqdiv p
        have hqfactor : q ∈ m.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hqprime, hqm, by omega⟩
        have hqexternal : q ∈ externalPrimeFactors S m :=
          Finset.mem_filter.mpr ⟨hqfactor, hqnotwo, hqS⟩
        have heq := deficient_external_prime_factor_unique
          (S := S) (b := b) hmpos hmn hdeficient hqexternal hp
        subst q
        exact False.elim (hnotdiv hqdiv)
  exact ⟨c, p, hcsmooth, hpprime, hpnotwo, hpnotS, hnotdiv, hrepr, hmiss⟩

/-- All actual admissible even smooth-core/reduced-residue pairs up to the
current closed-interval endpoint. -/
noncomputable def initialDeficiencySmoothCoreFamily
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 n).product
    (Finset.range (∏ s ∈ S, s))).filter
      (admissibleSmoothDeficiencyCore S b)

/-- Membership in the moving core family implies genuine, nonvacuous
smooth-core/residue admissibility. -/
theorem initialDeficiencySmoothCoreFamily_admissible
    {S : Finset ℕ} {b : ℕ → ℕ} {n : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ initialDeficiencySmoothCoreFamily S b n) :
    admissibleSmoothDeficiencyCore S b v := by
  classical
  exact (Finset.mem_filter.mp hv).2

/-- Every actual exponent-one outside-prime deficiency belongs to its unique
genuine smooth-core/reduced-prime-progression stratum. -/
theorem initialDeficiencySimpleExternalTargets_subset_smoothCoreUnion
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hn : 2 ≤ n) :
    initialDeficiencySimpleExternalTargets S b n ⊆
      (initialDeficiencySmoothCoreFamily S b n).biUnion
        fun v => smoothDeficiencyTargets S v.1 v.2 n := by
  classical
  intro m hm
  have hexternal := (Finset.mem_filter.mp hm).1
  have hinterval := (Finset.mem_filter.mp hexternal).1
  obtain ⟨hmpos, hmn⟩ := Finset.mem_Icc.mp hinterval
  obtain ⟨c, p, hcsmooth, hpprime, hpnotwo, hpnotS, _hnotdiv,
      hrepr, hmiss⟩ :=
    initialDeficiencySimpleExternalTargets_smooth_prime_representation
      hsupport htwo hn hm
  let W : ℕ := ∏ s ∈ S, s
  have hWpos : 0 < W := by
    dsimp [W]
    exact Finset.prod_pos fun s hs => (hsupport s hs).1.pos
  have hpnotdiv : ¬ p ∣ W := by
    intro hdiv
    exact hpnotS
      (prime_mem_of_dvd_support_product hpprime
        (fun s hs => (hsupport s hs).1) hdiv)
  have hpcoprime : Nat.Coprime p W :=
    hpprime.coprime_iff_not_dvd.mpr hpnotdiv
  let r : ℕ := p % W
  have hrlt : r < W := Nat.mod_lt p hWpos
  have hrcoprime : Nat.Coprime r W := by
    change Nat.gcd r W = 1
    have hgcd : Nat.gcd p W = Nat.gcd (p % W) W := by
      rw [Nat.gcd_comm p W, Nat.gcd_rec]
    exact hgcd.symm.trans hpcoprime
  have hcmiss : switchedHits S b (c * r) = 0 := by
    have hmod : (c * r) % W = (c * p) % W := by
      simp [r, Nat.mul_mod]
    have heq := switchedHits_eq_of_mod_product_eq (S := S) (b := b) hmod
    rw [heq, ← hrepr]
    exact hmiss
  have hc_le : c ≤ n := by
    have hdiv : c ∣ m := by
      refine ⟨p, ?_⟩
      exact hrepr
    exact (Nat.le_of_dvd (by omega) hdiv).trans hmn
  have hcoremem : (c, r) ∈ initialDeficiencySmoothCoreFamily S b n := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hcsmooth.1, hc_le⟩,
        Finset.mem_range.mpr hrlt⟩
    · exact ⟨hcsmooth, hrlt, hrcoprime, hcmiss⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(c, r), hcoremem, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨p, ?_, hrepr.symm⟩
  apply Finset.mem_erase.mpr
  refine ⟨hpnotwo, Finset.mem_filter.mpr ?_⟩
  refine ⟨Finset.mem_Icc.mpr ⟨hpprime.one_le, ?_⟩,
    hpprime, ?_⟩
  · apply (Nat.le_div_iff_mul_le hcsmooth.1).mpr
    simpa [Nat.mul_comm, ← hrepr] using hmn
  · simp [r, W]

/-- Conversely, every genuine admissible smooth-core prime stratum gives an
actual deficient target whose outside prime has exponent exactly one. -/
theorem smoothCoreUnion_subset_initialDeficiencySimpleExternalTargets
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    ((initialDeficiencySmoothCoreFamily S b n).biUnion
      fun v => smoothDeficiencyTargets S v.1 v.2 n) ⊆
        initialDeficiencySimpleExternalTargets S b n := by
  classical
  intro m hm
  obtain ⟨v, hv, htarget⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨hsmooth, _hr, hcoprime, hmiss⟩ :=
    initialDeficiencySmoothCoreFamily_admissible hv
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp htarget
  subst m
  obtain ⟨hpnotwo, hpnotS⟩ := smoothDeficiencyPrimeStratum_external hcoprime hp
  have hpbase := (Finset.mem_erase.mp hp).2
  obtain ⟨hpinterval, hpprime, _hpresidue⟩ := Finset.mem_filter.mp hpbase
  obtain ⟨hppos, hpbound⟩ := Finset.mem_Icc.mp hpinterval
  have htargetpos : 0 < v.1 * p := Nat.mul_pos hsmooth.1 hpprime.pos
  have htargetbound : v.1 * p ≤ n := by
    have hbound := (Nat.le_div_iff_mul_le hsmooth.1).mp hpbound
    simpa [Nat.mul_comm] using hbound
  have hactualmiss := smoothDeficiencyPrimeStratum_switchedHits_zero hp hmiss
  have hcoverage := initialAssignment_even_smooth_prime_coverage_general
    (n := n) hsmooth hpprime hactualmiss
  have hfactor : p ∈ (v.1 * p).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hpprime, dvd_mul_left p v.1, (ne_of_gt htargetpos)⟩
  have hpexternal : p ∈ externalPrimeFactors S (v.1 * p) :=
    Finset.mem_filter.mpr ⟨hfactor, hpnotwo, hpnotS⟩
  have hexternal : v.1 * p ∈ initialDeficiencyExternalTargets S b n := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨htargetpos, htargetbound⟩,
      by omega, ⟨p, hpexternal⟩⟩
  apply Finset.mem_filter.mpr
  refine ⟨hexternal, ?_⟩
  rintro ⟨q, hq, hpower⟩
  have heqprime := deficient_external_prime_factor_unique
    (S := S) (b := b) htargetpos htargetbound (by omega) hq hpexternal
  subst q
  have hnotdiv : ¬ p ∣ v.1 := by
    intro hdiv
    rcases hsmooth.2.2 p hpprime hdiv with htwo | hsupport
    · exact hpnotwo htwo
    · exact hpnotS hsupport
  obtain ⟨k, hk⟩ := hpower
  have hcancel : v.1 * p = (p * k) * p := by
    calc
      v.1 * p = p ^ 2 * k := hk
      _ = (p * k) * p := by simp only [pow_two]; ac_rfl
  have hcore : v.1 = p * k := Nat.mul_right_cancel hpprime.pos hcancel
  exact hnotdiv ⟨k, hcore⟩

/-- Exact equality between genuine exponent-one outside-prime deficiencies and
the union of actual admissible smooth-core prime progressions. -/
theorem initialDeficiencySimpleExternalTargets_eq_smoothCoreUnion
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hn : 2 ≤ n) :
    initialDeficiencySimpleExternalTargets S b n =
      (initialDeficiencySmoothCoreFamily S b n).biUnion
        fun v => smoothDeficiencyTargets S v.1 v.2 n := by
  apply Finset.Subset.antisymm
  · exact initialDeficiencySimpleExternalTargets_subset_smoothCoreUnion
      S b hsupport htwo hn
  · exact smoothCoreUnion_subset_initialDeficiencySimpleExternalTargets S b n

/-- Exact main-term count from all genuine, moving even smooth-core/reduced
prime-progression strata; this contains no deficiency or covering predicate. -/
noncomputable def initialDeficiencyMainPrimeStratumCount
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ v ∈ initialDeficiencySmoothCoreFamily S b n,
    (smoothDeficiencyPrimeStratum S v.1 v.2 n).card

/-- Distinct admissible smooth-core/reduced-residue strata are disjoint, so the
actual main-term target count is their exact prime-count sum. -/
theorem initialDeficiencySimpleExternalTargets_card_eq_mainPrimeStratumCount
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hn : 2 ≤ n) :
    (initialDeficiencySimpleExternalTargets S b n).card =
      initialDeficiencyMainPrimeStratumCount S b n := by
  classical
  let F := initialDeficiencySmoothCoreFamily S b n
  let targets : (ℕ × ℕ) → Finset ℕ :=
    fun v => smoothDeficiencyTargets S v.1 v.2 n
  have hdisjoint : (↑F : Set (ℕ × ℕ)).PairwiseDisjoint targets := by
    intro v hv v' hv' hne
    obtain ⟨_hsmooth, hr, hcoprime, _hmiss⟩ :=
      initialDeficiencySmoothCoreFamily_admissible hv
    obtain ⟨hsmooth', hr', _hcoprime', _hmiss'⟩ :=
      initialDeficiencySmoothCoreFamily_admissible hv'
    exact smoothDeficiencyTargets_disjoint hsmooth' hr hr' hcoprime hne
  rw [initialDeficiencySimpleExternalTargets_eq_smoothCoreUnion
    S b hsupport htwo hn, Finset.card_biUnion hdisjoint]
  unfold initialDeficiencyMainPrimeStratumCount
  apply Finset.sum_congr rfl
  intro v hv
  exact smoothDeficiencyTargets_card S v.1 v.2 n
    (initialDeficiencySmoothCoreFamily_admissible hv).1.1

/-- Exact finite actual-deficiency identity with its explicit prime-progression
main term and its separate higher-external-prime-power exception. -/
theorem initial_deficiency_eq_externalFreeWeight_add_mainPrimeStratum_add_primePower
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ s ≤ n)
    (htwo : 2 ∉ S) (hn : 2 ≤ n) :
    deficiency n (initialAssignment S b) =
      initialDeficiencyExternalFreeWeight S b n +
        initialDeficiencyMainPrimeStratumCount S b n +
          (initialDeficiencyPrimePowerTargets S b n).card := by
  rw [initial_deficiency_eq_externalFreeWeight_add_simple_add_primePower,
    initialDeficiencySimpleExternalTargets_card_eq_mainPrimeStratumCount
      S b hsupport htwo hn]

/-- After every fixed support prime becomes available, outside-prime deficits
split exactly into the explicit smooth-core prime sum and prime-power error. -/
theorem eventually_initialDeficiencyExternalTargets_card_eq_main_add_primePower
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (htwo : 2 ∉ S) :
    ∀ᶠ n : ℕ in atTop,
      (initialDeficiencyExternalTargets S b n).card =
        initialDeficiencyMainPrimeStratumCount S b n +
          (initialDeficiencyPrimePowerTargets S b n).card := by
  filter_upwards [eventually_ge_atTop (S.sup id), eventually_ge_atTop 2]
    with n hlarge hn
  have havailable : ∀ s ∈ S, s.Prime ∧ s ≤ n := by
    intro s hs
    exact ⟨hsupport s hs, (Finset.le_sup (f := @id ℕ) hs).trans hlarge⟩
  rw [initialDeficiencyExternalTargets_card_eq_simple_add_primePower,
    initialDeficiencySimpleExternalTargets_card_eq_mainPrimeStratumCount
      S b havailable htwo hn]

/-- The full actual deficiency asymptotic is equivalent to the explicit
prime-progression main sum plus the separately specified prime-power error. -/
theorem initial_deficiency_asymptotic_iff_main_add_primePower
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (htwo : 2 ∉ S) :
    Tendsto
      (fun n : ℕ =>
        (deficiency n (initialAssignment S b) : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) ↔
    Tendsto
      (fun n : ℕ =>
        (initialDeficiencyMainPrimeStratumCount S b n : ℝ) /
            ((n : ℝ) / Real.log n) +
          ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) /
            ((n : ℝ) / Real.log n))
      atTop (nhds 1) := by
  rw [initial_deficiency_asymptotic_iff_externalTargets]
  have hsplit :=
    eventually_initialDeficiencyExternalTargets_card_eq_main_add_primePower
      S b hsupport htwo
  have heq :
      (fun n : ℕ =>
        ((initialDeficiencyExternalTargets S b n).card : ℝ) /
          ((n : ℝ) / Real.log n)) =ᶠ[atTop]
      (fun n : ℕ =>
        (initialDeficiencyMainPrimeStratumCount S b n : ℝ) /
            ((n : ℝ) / Real.log n) +
          ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) /
            ((n : ℝ) / Real.log n)) := by
    filter_upwards [hsplit] with n hn
    rw [hn]
    push_cast
    ring
  exact Filter.tendsto_congr' heq

/-- Once the explicitly identified actual prime-power exception is negligible,
the only missing analytic theorem is the normalized asymptotic of the genuine
moving smooth-core/reduced-prime-progression sum. -/
theorem initial_deficiency_asymptotic_iff_mainPrimeStratum_of_primePower_negligible
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (htwo : 2 ∉ S)
    (hpower : Tendsto
      (fun n : ℕ =>
        ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        (deficiency n (initialAssignment S b) : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) ↔
    Tendsto
      (fun n : ℕ =>
        (initialDeficiencyMainPrimeStratumCount S b n : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) := by
  rw [initial_deficiency_asymptotic_iff_main_add_primePower S b hsupport htwo]
  constructor
  · intro hcombined
    have hsub := hcombined.sub hpower
    simp only [sub_zero] at hsub
    apply hsub.congr'
    filter_upwards [] with n
    ring
  · intro hmain
    simpa only [add_zero] using hmain.add hpower


end Erdos689
