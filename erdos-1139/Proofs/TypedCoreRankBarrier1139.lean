module

public import TypedCoreMatchingBridge1139

@[expose] public section


/-!
# Exact prime-target rank obstruction for Erdős problem #1139

The fixed-parameter squared-prime core gives **zero** hits to every prime
strictly above its actual cutoff. Each such prime target consequently needs
two distinct fresh prime labels. Double-counting those incidences proves that
any construction in which every fresh residue hits at most `r` prime targets
must use at least `2 * (π(y) - π(y / z)) / r` distinct labels.

This is an exact necessary condition, not an assumed matching theorem or a
claim that the original infinite-limsup conjecture has been proved.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Prime targets beyond the *actual integer* fixed-core cutoff. -/
def fixedCoreLargePrimeTargets (y z : ℕ) : Finset ℕ :=
  Nat.primesLE y \ fixedParameterCorePrimes y z

/-- Membership retains primality, the closed upper endpoint, and the strict
integer-division lower cutoff. -/
theorem mem_fixedCoreLargePrimeTargets
    {y z h : ℕ} :
    h ∈ fixedCoreLargePrimeTargets y z ↔
      h.Prime ∧ y / z < h ∧ h ≤ y := by
  unfold fixedCoreLargePrimeTargets fixedParameterCorePrimes
  simp only [Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨bounded, prime⟩, not_small⟩
    refine ⟨prime, ?_, bounded⟩
    apply Nat.lt_of_not_ge
    intro small
    exact not_small ⟨small, prime⟩
  · rintro ⟨prime, large, bounded⟩
    refine ⟨⟨bounded, prime⟩, ?_⟩
    intro small
    exact (Nat.not_le_of_gt large) small.1

/-- The large-prime target count is exactly the prime-counting difference;
no interval endpoint or selected small prime is silently discarded. -/
theorem fixedCoreLargePrimeTargets_card
    (y z : ℕ) :
    (fixedCoreLargePrimeTargets y z).card =
      Nat.primeCounting y - Nat.primeCounting (y / z) := by
  unfold fixedCoreLargePrimeTargets fixedParameterCorePrimes
  rw [Finset.card_sdiff_of_subset
    (Nat.primesLE_mono (Nat.div_le_self y z))]
  simp only [Nat.primesLE_card_eq_primeCounting]

/-- Every prime strictly above the core cutoff receives exactly zero broad
hits and exactly zero nested square hits from the actual zero-residue core. -/
theorem fixedParameterCoreHits_eq_zero_of_large_prime
    {y z h : ℕ} (prime : h.Prime) (large : y / z < h) :
    fixedParameterCoreHits y z h = 0 := by
  classical
  have broad_empty :
      ((fixedParameterCorePrimes y z).filter
        fun p => (0 : ℕ) ≡ h [MOD p]) = ∅ := by
    rw [fixedParameterCore_zero_broad_hits_eq_small_prime_factors prime.pos]
    simpa [prime.primeFactors] using large
  have square_empty :
      ((fixedParameterCoreSquared y z).filter
        fun p => (0 : ℕ) ≡ h [MOD p ^ 2]) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p selected hit
    have pprime := fixedParameterCorePrimes_prime y z p
      (fixedParameterCoreSquared_subset y z selected)
    have square_divides : p ^ 2 ∣ h :=
      Nat.modEq_zero_iff_dvd.mp hit.symm
    have divides : p ∣ h := dvd_trans (by simp [pow_two]) square_divides
    have equal : p = h :=
      (Nat.prime_dvd_prime_iff_eq pprime prime).mp divides
    have bounded : p ≤ y / z :=
      Nat.le_of_mem_primesLE (fixedParameterCoreSquared_subset y z selected)
    omega
  simp [fixedParameterCoreHits, broad_empty, square_empty]

/-- A successful typed-core repair must assign two DISTINCT new labels to
every prime above the core cutoff. -/
theorem typedCore_large_prime_needs_two_fresh_hits
    {y z : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h)
    {h : ℕ} (target : h ∈ fixedCoreLargePrimeTargets y z) :
    2 ≤ typedCoreFreshHits R b h := by
  obtain ⟨prime, large, bounded⟩ :=
    mem_fixedCoreLargePrimeTargets.mp target
  have interval : h ∈ Finset.Icc 1 y :=
    Finset.mem_Icc.mpr ⟨prime.one_le, bounded⟩
  have target_type : FixedParameterCoreDeficientType y z h :=
    Or.inr (Or.inl prime)
  simpa [fixedParameterCoreHits_eq_zero_of_large_prime prime large] using
    matching h interval target_type

/-- Exact incidence identity between genuinely distinct fresh prime labels
and the actual large prime targets their single coherent residues hit. -/
theorem typedCore_large_prime_incidence_identity
    (y z : ℕ) (R : Finset ℕ) (b : ℕ → ℕ) :
    (∑ h ∈ fixedCoreLargePrimeTargets y z,
      typedCoreFreshHits R b h) =
      ∑ p ∈ R,
        ((fixedCoreLargePrimeTargets y z).filter
          fun h => b p ≡ h [MOD p]).card := by
  classical
  unfold typedCoreFreshHits
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Exact bounded-rank obstruction: if each genuinely selected fresh residue
hits at most `r` large prime targets, at least their twofold total demand must
fit within `r` slots per distinct fresh label. -/
theorem typedCore_bounded_prime_target_rank_forces_labels
    {y z r : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h)
    (rank_bound : ∀ p ∈ R,
      ((fixedCoreLargePrimeTargets y z).filter
        fun h => b p ≡ h [MOD p]).card ≤ r) :
    2 * (fixedCoreLargePrimeTargets y z).card ≤ r * R.card := by
  calc
    2 * (fixedCoreLargePrimeTargets y z).card =
        ∑ h ∈ fixedCoreLargePrimeTargets y z, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ h ∈ fixedCoreLargePrimeTargets y z,
          typedCoreFreshHits R b h := by
      apply Finset.sum_le_sum
      intro h target
      exact typedCore_large_prime_needs_two_fresh_hits matching target
    _ = ∑ p ∈ R,
          ((fixedCoreLargePrimeTargets y z).filter
            fun h => b p ≡ h [MOD p]).card :=
      typedCore_large_prime_incidence_identity y z R b
    _ ≤ ∑ _p ∈ R, r := by
      apply Finset.sum_le_sum
      intro p selected
      exact rank_bound p selected
    _ = r * R.card := by simp [Nat.mul_comm]

/-- The same exact obstruction expressed through the genuine prime counting
functions at the original endpoint and rounded core cutoff. -/
theorem typedCore_bounded_rank_primeCounting_barrier
    {y z r : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h)
    (rank_bound : ∀ p ∈ R,
      ((fixedCoreLargePrimeTargets y z).filter
        fun h => b p ≡ h [MOD p]).card ≤ r) :
    2 * (Nat.primeCounting y - Nat.primeCounting (y / z)) ≤ r * R.card := by
  rw [← fixedCoreLargePrimeTargets_card y z]
  exact typedCore_bounded_prime_target_rank_forces_labels matching rank_bound

/-- Prime labels fresh for the actual full fixed-parameter core necessarily
lie strictly above its rounded cutoff. -/
theorem typedCore_fresh_prime_exceeds_cutoff
    {y z p : ℕ} {R : Finset ℕ}
    (reserve_primes : ∀ q ∈ R, q.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R)
    (selected : p ∈ R) :
    y / z < p := by
  have prime := reserve_primes p selected
  have not_core : p ∉ fixedParameterCorePrimes y z :=
    Finset.disjoint_right.mp fresh selected
  unfold fixedParameterCorePrimes at not_core
  have not_bounded : ¬ p ≤ y / z := by
    intro bounded
    exact not_core (Nat.mem_primesLE.mpr ⟨bounded, prime⟩)
  exact Nat.lt_of_not_ge not_bounded

/-- A prime target below the rounded core cutoff receives exactly one old
hit; a prime above it receives none.  No prime target ever receives a nested
square hit. -/
theorem fixedParameterCoreHits_prime
    {y z q : ℕ} (prime : q.Prime) :
    fixedParameterCoreHits y z q = if q ≤ y / z then 1 else 0 := by
  classical
  have square_empty :
      ((fixedParameterCoreSquared y z).filter
        fun p => (0 : ℕ) ≡ q [MOD p ^ 2]) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p selected hit
    have pprime := fixedParameterCorePrimes_prime y z p
      (fixedParameterCoreSquared_subset y z selected)
    have square_divides : p ^ 2 ∣ q :=
      Nat.modEq_zero_iff_dvd.mp hit.symm
    exact (Nat.squarefree_iff_prime_squarefree.mp prime.squarefree p pprime)
      (by simpa [pow_two] using square_divides)
  unfold fixedParameterCoreHits
  rw [fixedParameterCore_zero_broad_hits_eq_small_prime_factors prime.pos,
    prime.primeFactors, square_empty]
  rw [Finset.filter_singleton]
  split_ifs <;> simp

/-- A fresh label's complete prime-target incidence counts both prime targets
below the old core cutoff and prime targets above it. -/
def typedCorePrimeTargetLoad (y : ℕ) (b : ℕ → ℕ) (p : ℕ) : ℕ :=
  ((Nat.primesLE y).filter fun q => b p ≡ q [MOD p]).card

/-- Exact transpose of the complete prime-target/fresh-prime incidence
matrix, including the prime targets already carrying one old core hit. -/
theorem typedCore_prime_target_incidence_identity
    (y : ℕ) (R : Finset ℕ) (b : ℕ → ℕ) :
    (∑ q ∈ Nat.primesLE y, typedCoreFreshHits R b q) =
      ∑ p ∈ R, typedCorePrimeTargetLoad y b p := by
  classical
  unfold typedCoreFreshHits typedCorePrimeTargetLoad
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Across every genuine prime target up to `y`, the old core contributes
exactly `π(⌊y / z⌋)` incidences. -/
theorem fixedParameterCore_prime_target_hits_sum
    (y z : ℕ) :
    (∑ q ∈ Nat.primesLE y, fixedParameterCoreHits y z q) =
      Nat.primeCounting (y / z) := by
  classical
  calc
    (∑ q ∈ Nat.primesLE y, fixedParameterCoreHits y z q) =
        ∑ q ∈ Nat.primesLE y, if q ≤ y / z then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro q selected
          exact fixedParameterCoreHits_prime
            (Nat.prime_of_mem_primesLE selected)
    _ = ((Nat.primesLE y).filter fun q => q ≤ y / z).card := by
      simp
    _ = (Nat.primesLE (y / z)).card := by
      congr 1
      ext q
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_, prime⟩, bounded⟩
        exact ⟨bounded, prime⟩
      · rintro ⟨bounded, prime⟩
        exact ⟨⟨bounded.trans (Nat.div_le_self y z), prime⟩, bounded⟩
    _ = Nat.primeCounting (y / z) :=
      Nat.primesLE_card_eq_primeCounting (y / z)

/-- The SHARP exact necessary fresh incidence budget from prime targets:
small primes need one new hit and large primes need two, yielding
`2π(y) - π(⌊y / z⌋)`.  Semiprime and prime-power targets can only increase
the actual requirement. -/
theorem typedCore_prime_target_fresh_incidence_budget
    {y z : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h) :
    2 * Nat.primeCounting y ≤
      Nat.primeCounting (y / z) +
        ∑ p ∈ R, typedCorePrimeTargetLoad y b p := by
  have total :
      (∑ q ∈ Nat.primesLE y, 2) ≤
        ∑ q ∈ Nat.primesLE y,
          (fixedParameterCoreHits y z q + typedCoreFreshHits R b q) := by
    apply Finset.sum_le_sum
    intro q selected
    have prime := Nat.prime_of_mem_primesLE selected
    apply matching q
      (Finset.mem_Icc.mpr ⟨prime.one_le, Nat.le_of_mem_primesLE selected⟩)
    exact Or.inr (Or.inl prime)
  rw [Finset.sum_add_distrib,
    fixedParameterCore_prime_target_hits_sum,
    typedCore_prime_target_incidence_identity] at total
  simpa [Nat.primesLE_card_eq_primeCounting, Nat.mul_comm] using total

/-- Every bounded-rank fresh-prime architecture must pay for the FULL prime
target budget, not merely the large-prime targets.  This improves the
necessary incidence coefficient from `2(1 - 1/z)` to `2 - 1/z`. -/
theorem typedCore_bounded_full_prime_target_rank_forces_labels
    {y z r : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h)
    (rank_bound : ∀ p ∈ R, typedCorePrimeTargetLoad y b p ≤ r) :
    2 * Nat.primeCounting y - Nat.primeCounting (y / z) ≤ r * R.card := by
  have budget := typedCore_prime_target_fresh_incidence_budget matching
  have total : (∑ p ∈ R, typedCorePrimeTargetLoad y b p) ≤ r * R.card := by
    calc
      (∑ p ∈ R, typedCorePrimeTargetLoad y b p) ≤ ∑ _p ∈ R, r := by
        apply Finset.sum_le_sum
        exact rank_bound
      _ = r * R.card := by simp [Nat.mul_comm]
  omega

/-- Exact lower bound for the actual logarithmic cost of genuine prime labels
lying above a positive natural cutoff. -/
theorem prime_product_log_ge_card_mul_log_cutoff
    (R : Finset ℕ) (L : ℕ)
    (positive : 0 < L)
    (primes : ∀ p ∈ R, p.Prime)
    (above : ∀ p ∈ R, L ≤ p) :
    (R.card : ℝ) * Real.log (L : ℝ) ≤
      Real.log ((∏ p ∈ R, p : ℕ) : ℝ) := by
  classical
  have nonzero : ∀ p ∈ R, (p : ℝ) ≠ 0 := by
    intro p selected
    exact_mod_cast (primes p selected).ne_zero
  calc
    (R.card : ℝ) * Real.log (L : ℝ) =
        ∑ _p ∈ R, Real.log (L : ℝ) := by simp
    _ ≤ ∑ p ∈ R, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p selected
      have L_positive : (0 : ℝ) < L := by exact_mod_cast positive
      have p_positive : (0 : ℝ) < p := by
        exact_mod_cast (primes p selected).pos
      apply Real.strictMonoOn_log.monotoneOn L_positive p_positive
      exact_mod_cast above p selected
    _ = Real.log (∏ p ∈ R, (p : ℝ)) := (Real.log_prod nonzero).symm
    _ = Real.log ((∏ p ∈ R, p : ℕ) : ℝ) := by simp

/-- Fully quantitative exact fixed-rank conductor obstruction, charging the
actual logarithm of every distinct genuinely fresh prime.  In combination
with the prime number theorem its leading lower coefficient is
`(2 - 1 / z) / r`, so fixed rank cannot produce vanishing conductor cost. -/
theorem typedCore_bounded_rank_log_conductor_barrier
    {y z r : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (cutoff_positive : 0 < y / z)
    (rank_positive : 0 < r)
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R)
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h)
    (rank_bound : ∀ p ∈ R, typedCorePrimeTargetLoad y b p ≤ r) :
    (((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) /
        (r : ℝ)) * Real.log ((y / z : ℕ) : ℝ) ≤
      Real.log ((∏ p ∈ R, p : ℕ) : ℝ) := by
  have label_budget :=
    typedCore_bounded_full_prime_target_rank_forces_labels matching rank_bound
  have label_real :
      ((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) ≤
        (r : ℝ) * (R.card : ℝ) := by
    exact_mod_cast label_budget
  have r_positive : (0 : ℝ) < r := by exact_mod_cast rank_positive
  have cardinal_lower :
      ((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) /
        (r : ℝ) ≤ (R.card : ℝ) :=
    (div_le_iff₀ r_positive).mpr (by nlinarith)
  have logarithm_nonnegative : 0 ≤ Real.log ((y / z : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast cutoff_positive
  calc
    (((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) /
        (r : ℝ)) * Real.log ((y / z : ℕ) : ℝ) ≤
        (R.card : ℝ) * Real.log ((y / z : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right cardinal_lower logarithm_nonnegative
    _ ≤ Real.log ((∏ p ∈ R, p : ℕ) : ℝ) :=
      prime_product_log_ge_card_mul_log_cutoff R (y / z)
        cutoff_positive reserve_primes
        (fun p selected => (typedCore_fresh_prime_exceeds_cutoff
          reserve_primes fresh selected).le)

/-- The audited progression prime-counting input at modulus one is exactly
ordinary prime counting, including its closed upper endpoint. -/
theorem primeAPCount_one_eq_primeCounting (y : ℕ) :
    Erdos730.FullDensity.primeAPCount 1 0 y = Nat.primeCounting y := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  unfold Erdos730.FullDensity.primeAPCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
  constructor
  · rintro ⟨bounded, prime, _⟩
    exact ⟨by omega, prime⟩
  · rintro ⟨bounded, prime⟩
    exact ⟨by omega, prime, by simpa using Nat.mod_one p⟩

/-- Prime counting has its genuine full prime-number-theorem normalization;
this imports the previously audited modulus-one proof rather than replacing
it by an analytic assumption. -/
theorem primeCounting_normalized_tendsto_one :
    Tendsto
      (fun y : ℕ =>
        (Nat.primeCounting y : ℝ) / ((y : ℝ) / Real.log (y : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have pnt :=
    (Erdos730.FullDensity.pntAPInputAtModulus 1 (by norm_num)).2
      0 (by norm_num) (by norm_num)
  simpa [primeAPCount_one_eq_primeCounting] using pnt

/-- Prime counting at the fixed rounded cutoff `⌊y/z⌋`, normalized at the
ORIGINAL endpoint `y`, has leading coefficient exactly `1/z`. -/
theorem primeCounting_fixed_cutoff_normalized_tendsto
    (z : ℕ) (positive : 0 < z) :
    Tendsto
      (fun y : ℕ =>
        (Nat.primeCounting (y / z) : ℝ) /
          ((y : ℝ) / Real.log (y : ℝ)))
      atTop (𝓝 ((z : ℝ)⁻¹)) := by
  have cutoff := primeCounting_normalized_tendsto_one.comp
    (Nat.tendsto_div_const_atTop positive.ne')
  have scale := Erdos689.nat_div_prime_scale_ratio_tendsto z positive
  have combined := cutoff.mul scale
  have target :
      Tendsto
        (fun y : ℕ =>
          ((Nat.primeCounting (y / z) : ℝ) /
            (((y / z : ℕ) : ℝ) / Real.log ((y / z : ℕ) : ℝ))) *
          ((((y / z : ℕ) : ℝ) / Real.log ((y / z : ℕ) : ℝ)) /
            ((y : ℝ) / Real.log (y : ℝ))))
        atTop (𝓝 ((z : ℝ)⁻¹)) := by
    simpa using combined
  apply target.congr'
  filter_upwards [eventually_ge_atTop (2 * z)] with y large
  have cutoff_large : 2 ≤ y / z :=
    (Nat.le_div_iff_mul_le positive).mpr (by simpa [Nat.mul_comm] using large)
  have cutoff_real : (0 : ℝ) < (y / z : ℕ) := by
    exact_mod_cast (by omega : 0 < y / z)
  have log_positive : 0 < Real.log ((y / z : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast cutoff_large
  have middle_nonzero :
      (((y / z : ℕ) : ℝ) / Real.log ((y / z : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero cutoff_real.ne' log_positive.ne'
  exact div_mul_div_cancel₀ middle_nonzero

/-- The SHARP complete prime-target demand, including the singly covered
small prime targets, has leading coefficient `2 - 1/z`. -/
theorem typedCore_full_prime_incidence_coefficient_tendsto
    (z : ℕ) (positive : 0 < z) :
    Tendsto
      (fun y : ℕ =>
        ((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) /
          ((y : ℝ) / Real.log (y : ℝ)))
      atTop (𝓝 ((2 : ℝ) - (z : ℝ)⁻¹)) := by
  have ordinary := primeCounting_normalized_tendsto_one.const_mul (2 : ℝ)
  have cutoff := primeCounting_fixed_cutoff_normalized_tendsto z positive
  have difference := ordinary.sub cutoff
  convert difference using 1
  · funext y
    have cutoff_le : Nat.primeCounting (y / z) ≤ Nat.primeCounting y :=
      Nat.monotone_primeCounting (Nat.div_le_self y z)
    have budget : Nat.primeCounting (y / z) ≤ 2 * Nat.primeCounting y := by
      omega
    rw [Nat.cast_sub budget]
    push_cast
    ring
  · norm_num

/-- For every FIXED positive rank and core parameter, the exact necessary
actual-conductor lower bound has positive leading density
`(2 - 1/z) / r`; in particular it cannot be little-oh of the covered length. -/
theorem typedCore_bounded_rank_required_log_density_tendsto
    (z r : ℕ) (z_positive : 0 < z) (r_positive : 0 < r) :
    Tendsto
      (fun y : ℕ =>
        ((((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) /
          (r : ℝ)) * Real.log ((y / z : ℕ) : ℝ)) / (y : ℝ))
      atTop (𝓝 (((2 : ℝ) - (z : ℝ)⁻¹) / (r : ℝ))) := by
  have incidence :=
    typedCore_full_prime_incidence_coefficient_tendsto z z_positive
  have logarithm := Erdos689.nat_div_log_ratio_tendsto z z_positive
  have scale := (incidence.mul logarithm).div_const (r : ℝ)
  have target :
      Tendsto
        (fun y : ℕ =>
          (((2 * Nat.primeCounting y - Nat.primeCounting (y / z) : ℕ) : ℝ) /
              ((y : ℝ) / Real.log (y : ℝ)) *
            (Real.log ((y / z : ℕ) : ℝ) / Real.log (y : ℝ))) /
            (r : ℝ))
        atTop (𝓝 (((2 : ℝ) - (z : ℝ)⁻¹) / (r : ℝ))) := by
    simpa using scale
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with y large
  have y_positive : (0 : ℝ) < y := by
    exact_mod_cast (by omega : 0 < y)
  have y_log_positive : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast large
  have rank_real : (0 : ℝ) < r := by exact_mod_cast r_positive
  field_simp [y_positive.ne', y_log_positive.ne', rank_real.ne']

/-- Every fixed-rank repair has actual logarithmic conductor eventually
larger than ANY coefficient strictly below `(2 - 1/z) / r`.  All target
demands, prime freshness, and actual distinct-label products are retained. -/
theorem eventually_typedCore_bounded_rank_linear_conductor
    (z r : ℕ) (z_positive : 0 < z) (r_positive : 0 < r)
    (c : ℝ) (coefficient : c < ((2 : ℝ) - (z : ℝ)⁻¹) / (r : ℝ)) :
    ∀ᶠ y : ℕ in atTop,
      ∀ (R : Finset ℕ) (b : ℕ → ℕ),
        (∀ p ∈ R, p.Prime) →
        Disjoint (fixedParameterCorePrimes y z) R →
        (∀ h ∈ Finset.Icc 1 y,
          FixedParameterCoreDeficientType y z h →
            2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h) →
        (∀ p ∈ R, typedCorePrimeTargetLoad y b p ≤ r) →
        c * (y : ℝ) < Real.log ((∏ p ∈ R, p : ℕ) : ℝ) := by
  have density :=
    (tendsto_order.mp
      (typedCore_bounded_rank_required_log_density_tendsto
        z r z_positive r_positive)).1 c coefficient
  have cutoff_positive : ∀ᶠ y : ℕ in atTop, 0 < y / z :=
    (Nat.tendsto_div_const_atTop z_positive.ne').eventually
      (eventually_gt_atTop 0)
  filter_upwards [density, cutoff_positive, eventually_gt_atTop 0]
    with y density_y cutoff_y positive_y
  intro R b reserve_primes fresh matching rank_bound
  have y_real : (0 : ℝ) < y := by exact_mod_cast positive_y
  have scaled := (lt_div_iff₀ y_real).mp density_y
  exact scaled.trans_le
    (typedCore_bounded_rank_log_conductor_barrier
      cutoff_y r_positive reserve_primes fresh matching rank_bound)

/-- In particular, no fixed-parameter sequence of genuine typed-core
matchings with uniformly bounded prime-target rank can have little-oh
fresh-prime conductor.  This is an unconditional impossibility theorem for
the proposed architecture, not a proof of the original Erdős problem. -/
theorem typedCore_bounded_rank_cannot_have_sublinear_conductor
    (z r : ℕ) (z_positive : 0 < z) (r_positive : 0 < r)
    (R : ℕ → Finset ℕ) (b : ℕ → ℕ → ℕ)
    (eventual_matchings : ∀ᶠ y : ℕ in atTop,
      (∀ p ∈ R y, p.Prime) ∧
      Disjoint (fixedParameterCorePrimes y z) (R y) ∧
      (∀ h ∈ Finset.Icc 1 y,
        FixedParameterCoreDeficientType y z h →
          2 ≤ fixedParameterCoreHits y z h +
            typedCoreFreshHits (R y) (b y) h) ∧
      (∀ p ∈ R y, typedCorePrimeTargetLoad y (b y) p ≤ r)) :
    ¬ Tendsto
      (fun y : ℕ =>
        Real.log ((∏ p ∈ R y, p : ℕ) : ℝ) / (y : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  intro sublinear
  have z_real : (1 : ℝ) ≤ z := by exact_mod_cast z_positive
  have inverse_le : (z : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ z_real
  have r_real : (0 : ℝ) < r := by exact_mod_cast r_positive
  let c : ℝ := (((2 : ℝ) - (z : ℝ)⁻¹) / (r : ℝ)) / 2
  have limit_positive : 0 < ((2 : ℝ) - (z : ℝ)⁻¹) / (r : ℝ) :=
    div_pos (by linarith) r_real
  have c_positive : 0 < c := by dsimp [c]; positivity
  have c_lower : c < ((2 : ℝ) - (z : ℝ)⁻¹) / (r : ℝ) := by
    dsimp [c]
    linarith
  have linear := eventually_typedCore_bounded_rank_linear_conductor
    z r z_positive r_positive c c_lower
  have small := (tendsto_order.mp sublinear).2 c c_positive
  obtain ⟨y, lower_y, matching_y, small_y, positive_y⟩ :=
    (linear.and (eventual_matchings.and
      (small.and (eventually_gt_atTop 0)))).exists
  obtain ⟨reserve_primes, fresh, matching, rank_bound⟩ := matching_y
  have strict_lower := lower_y (R y) (b y)
    reserve_primes fresh matching rank_bound
  have y_real : (0 : ℝ) < y := by exact_mod_cast positive_y
  have strict_upper := (div_lt_iff₀ y_real).mp small_y
  linarith


end Erdos1139
