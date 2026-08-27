import DeficiencyUpper433
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Repeated outside-prime factors in the actual initial deficiency

Every genuinely deficient target has at most one distinct prime outside the
fixed support and the parity prime.  This module factors the higher-power
exception *exactly*: its core is supported on the fixed finite set, its moving
prime is at most the square root of the endpoint, and its exponent is at most
the binary logarithm of that endpoint.

The finitary image bound concerns the actual `initialDeficiencyPrimePowerTargets`
set, not an independently chosen surrogate or an assumed asymptotic formula.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- A genuine repeated-outside-prime target has a unique prime-power factor
and an actual fixed-support smooth complementary core.  Both moving parameters
have explicit, endpoint-uniform bounds. -/
theorem initialDeficiencyPrimePowerTargets_smooth_prime_power_representation
    {S : Finset ℕ} {b : ℕ → ℕ} {n m : ℕ}
    (hm : m ∈ initialDeficiencyPrimePowerTargets S b n) :
    ∃ c p k : ℕ,
      0 < c ∧ c.primeFactors ⊆ insert 2 S ∧
        p.Prime ∧ p ≠ 2 ∧ p ∉ S ∧ ¬ p ∣ c ∧
          2 ≤ k ∧ m = c * p ^ k ∧ p ≤ n.sqrt ∧ k ≤ Nat.log 2 n := by
  obtain ⟨hexternal, p, hp, hsquare⟩ := Finset.mem_filter.mp hm
  obtain ⟨hinterval, hdeficient, _⟩ := Finset.mem_filter.mp hexternal
  obtain ⟨hmpos, hmn⟩ := Finset.mem_Icc.mp hinterval
  obtain ⟨hfactor, hpnotwo, hpnotS⟩ := Finset.mem_filter.mp hp
  have hpprime := Nat.prime_of_mem_primeFactors hfactor
  let k : ℕ := m.factorization p
  let c : ℕ := m / p ^ m.factorization p
  have hcpos : 0 < c := Nat.ordCompl_pos p (by omega)
  have hnotdiv : ¬ p ∣ c := Nat.not_dvd_ordCompl hpprime (by omega)
  have hrepr : m = c * p ^ k := by
    have hproduct := Nat.ordProj_mul_ordCompl_eq_self m p
    simpa [c, k, Nat.mul_comm] using hproduct.symm
  have hlarge : 2 ≤ k :=
    (hpprime.pow_dvd_iff_le_factorization (by omega)).mp hsquare
  have hcsmooth : c.primeFactors ⊆ insert 2 S := by
    intro q hqfactor
    have hqprime := Nat.prime_of_mem_primeFactors hqfactor
    have hqdiv := Nat.dvd_of_mem_primeFactors hqfactor
    by_cases hqtwo : q = 2
    · simp [hqtwo]
    · by_cases hqS : q ∈ S
      · exact Finset.mem_insert_of_mem hqS
      · have hqm : q ∣ m := by
          rw [hrepr]
          exact dvd_mul_of_dvd_left hqdiv _
        have hqfactor_m : q ∈ m.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hqprime, hqm, by omega⟩
        have hqexternal : q ∈ externalPrimeFactors S m :=
          Finset.mem_filter.mpr ⟨hqfactor_m, hqtwo, hqS⟩
        have heq := deficient_external_prime_factor_unique
          (S := S) (b := b) hmpos hmn hdeficient hqexternal hp
        subst q
        exact False.elim (hnotdiv hqdiv)
  have hpsquare : p ^ 2 ≤ n :=
    (Nat.le_of_dvd hmpos hsquare).trans hmn
  have hpsqrt : p ≤ n.sqrt := Nat.le_sqrt'.mpr hpsquare
  have hpow : 2 ^ k ≤ n := by
    calc
      2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hpprime.two_le k
      _ ≤ c * p ^ k := Nat.le_mul_of_pos_left _ hcpos
      _ = m := hrepr.symm
      _ ≤ n := hmn
  have hklog : k ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  exact ⟨c, p, k, hcpos, hcsmooth, hpprime, hpnotwo, hpnotS,
    hnotdiv, hlarge, hrepr, hpsqrt, hklog⟩

/-- Every actual repeated-external-prime target lies in an explicit finite
image of smooth cores, square-root-bounded bases, and logarithmically bounded
exponents.  Primality is deliberately dropped only in this upper bound. -/
theorem initialDeficiencyPrimePowerTargets_subset_smooth_power_image
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    initialDeficiencyPrimePowerTargets S b n ⊆
      (((supportSmoothNumbersUpTo (insert 2 S) n ×ˢ
          Finset.range (n.sqrt + 1)) ×ˢ
            Finset.range (Nat.log 2 n + 1)).image
              fun v : (ℕ × ℕ) × ℕ => v.1.1 * v.1.2 ^ v.2) := by
  intro m hm
  obtain ⟨c, p, k, hcpos, hcsmooth, hpprime, _, _, _, _, hrepr, hpsqrt, hklog⟩ :=
    initialDeficiencyPrimePowerTargets_smooth_prime_power_representation hm
  have hmn := (Finset.mem_Icc.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).2
  have hcn : c ≤ n := by
    calc
      c ≤ c * p ^ k := Nat.le_mul_of_pos_right _ (pow_pos hpprime.pos _)
      _ = m := hrepr.symm
      _ ≤ n := hmn
  apply Finset.mem_image.mpr
  refine ⟨((c, p), k), ?_, hrepr.symm⟩
  simp only [Finset.mem_product, Finset.mem_range]
  refine ⟨⟨?_, by omega⟩, by omega⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hcpos, hcn⟩, hcsmooth⟩

/-- Nonvacuous explicit finitary count for the actual repeated-prime exception.
The two moving dimensions have respective sizes `sqrt n + 1` and
`log₂ n + 1`, while all dependence on the fixed support is confined to the
smooth-core counting function. -/
theorem initialDeficiencyPrimePowerTargets_card_le_smooth_mul_sqrt_mul_log
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    (initialDeficiencyPrimePowerTargets S b n).card ≤
      (supportSmoothNumbersUpTo (insert 2 S) n).card *
        (n.sqrt + 1) * (Nat.log 2 n + 1) := by
  calc
    (initialDeficiencyPrimePowerTargets S b n).card ≤
        (((supportSmoothNumbersUpTo (insert 2 S) n ×ˢ
            Finset.range (n.sqrt + 1)) ×ˢ
              Finset.range (Nat.log 2 n + 1)).image
                fun v : (ℕ × ℕ) × ℕ => v.1.1 * v.1.2 ^ v.2).card :=
      Finset.card_le_card
        (initialDeficiencyPrimePowerTargets_subset_smooth_power_image S b n)
    _ ≤ ((supportSmoothNumbersUpTo (insert 2 S) n ×ˢ
          Finset.range (n.sqrt + 1)) ×ˢ
            Finset.range (Nat.log 2 n + 1)).card :=
      Finset.card_image_le
    _ = _ := by simp [Finset.card_product, Nat.mul_assoc]

/-- A fixed-support smooth counting function has an explicit bound with
*every* positive real exponent.  Its constant is the exact finite-support
Euler product, so choosing exponent `1 / 4` improves the generic square-root
bound sufficiently to control the moving repeated-prime exception. -/
theorem supportSmoothNumbersUpTo_card_le_rpow_euler
    (S : Finset ℕ) {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    ((supportSmoothNumbersUpTo S n).card : ℝ) ≤
      (n : ℝ) ^ a *
        (∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-a))⁻¹) := by
  let F := supportSmoothNumbersUpTo S n
  have hsmooth : ∀ m ∈ F, m ∈ Nat.factoredNumbers S := by
    intro m hm
    obtain ⟨hinterval, hsupport⟩ := Finset.mem_filter.mp hm
    exact Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr
      ⟨by have := (Finset.mem_Icc.mp hinterval).1; omega, hsupport⟩
  let embedding : {m : ℕ // m ∈ F} ↪ Nat.factoredNumbers S :=
    ⟨fun m => ⟨m, hsmooth m m.property⟩, by
      intro m m' heq
      apply Subtype.ext
      exact congrArg (fun x : Nat.factoredNumbers S => (x : ℕ)) heq⟩
  let lifted := F.attach.map embedding
  have hsum :
      (∑ m ∈ lifted, (((m : ℕ) : ℝ)) ^ (-a)) =
        ∑ m ∈ F, (m : ℝ) ^ (-a) := by
    dsimp [lifted]
    rw [Finset.sum_map]
    change (∑ m ∈ F.attach, ((m.val : ℝ)) ^ (-a)) = _
    exact Finset.sum_attach F fun m => (m : ℝ) ^ (-a)
  have hmass :
      (∑ m ∈ F, (m : ℝ) ^ (-a)) ≤
        ∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-a))⁻¹ := by
    rw [← hsum, ← supportSmooth_reciprocal_rpow_tsum S ha]
    exact (supportSmooth_reciprocal_rpow_summable S ha).sum_le_tsum
      lifted fun m _ => Real.rpow_nonneg (by positivity) _
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcompare :
      (F.card : ℝ) * (n : ℝ) ^ (-a) ≤
        ∑ m ∈ F, (m : ℝ) ^ (-a) := by
    calc
      (F.card : ℝ) * (n : ℝ) ^ (-a) =
          ∑ _m ∈ F, (n : ℝ) ^ (-a) := by simp
      _ ≤ ∑ m ∈ F, (m : ℝ) ^ (-a) := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hinterval, _⟩ := Finset.mem_filter.mp hm
        obtain ⟨hmpos, hmn⟩ := Finset.mem_Icc.mp hinterval
        apply Real.rpow_le_rpow_of_nonpos
          (by exact_mod_cast hmpos) (by exact_mod_cast hmn)
        linarith
  have hcancel : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add hnreal]
    simp
  change (F.card : ℝ) ≤ _
  calc
    (F.card : ℝ) =
        ((n : ℝ) ^ a * (n : ℝ) ^ (-a)) * (F.card : ℝ) := by
      rw [hcancel, one_mul]
    _ = (n : ℝ) ^ a * ((F.card : ℝ) * (n : ℝ) ^ (-a)) := by ring
    _ ≤ (n : ℝ) ^ a *
        (∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-a))⁻¹) :=
      mul_le_mul_of_nonneg_left (hcompare.trans hmass)
        (Real.rpow_nonneg hnreal.le a)

/-- Fully explicit sublinear bound for the actual higher-outside-prime-power
contribution.  The Euler-product constant depends only on the fixed support,
never on the endpoint, the assignment, or the moving external prime. -/
theorem initialDeficiencyPrimePowerTargets_card_le_three_quarters_log
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) ≤
      (4 / Real.log 2) *
        (∏ p ∈ insert 2 S with p.Prime,
          (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹) *
        (n : ℝ) ^ (3 / 4 : ℝ) * Real.log (n : ℝ) := by
  let T := insert 2 S
  let C : ℝ :=
    ∏ p ∈ T with p.Prime, (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogpos : 0 < Real.log (n : ℝ) := hlogtwo.trans_le hlogmono
  have hC : 0 ≤ C := by
    dsimp [C]
    rw [← supportSmooth_reciprocal_rpow_tsum T (by norm_num : 0 < (1 / 4 : ℝ))]
    exact tsum_nonneg fun m => Real.rpow_nonneg (by positivity) _
  have hcore :
      ((supportSmoothNumbersUpTo T n).card : ℝ) ≤
        (n : ℝ) ^ (1 / 4 : ℝ) * C :=
    supportSmoothNumbersUpTo_card_le_rpow_euler T (by norm_num) hnpos
  have hrootone : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.one_le_sqrt.mpr hnone
  have hrootnat : (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hroot :
      (n.sqrt : ℝ) + 1 ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    linarith
  have hbinary := Real.natLog_le_logb n 2
  simp only [Real.logb, Nat.cast_ofNat] at hbinary
  have hone_log : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlogtwo).mpr (by simpa using hlogmono)
  have hlog :
      (Nat.log 2 n : ℝ) + 1 ≤
        2 * (Real.log (n : ℝ) / Real.log 2) := by
    linarith
  have hfinite :
      ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) ≤
        ((supportSmoothNumbersUpTo T n).card : ℝ) *
          ((n.sqrt : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := by
    exact_mod_cast
      initialDeficiencyPrimePowerTargets_card_le_smooth_mul_sqrt_mul_log S b n
  have hpow :
      (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
        (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hnreal]
    congr 1
    norm_num
  change ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) ≤
    (4 / Real.log 2) * C * (n : ℝ) ^ (3 / 4 : ℝ) * Real.log (n : ℝ)
  calc
    ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) ≤
        ((supportSmoothNumbersUpTo T n).card : ℝ) *
          ((n.sqrt : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := hfinite
    _ ≤ ((n : ℝ) ^ (1 / 4 : ℝ) * C) *
          (2 * (n : ℝ) ^ (1 / 2 : ℝ)) *
          (2 * (Real.log (n : ℝ) / Real.log 2)) := by
      gcongr
    _ = (4 / Real.log 2) * C *
          ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) *
          Real.log (n : ℝ) := by ring
    _ = _ := by rw [hpow]

/-- Two logarithms are negligible against a quarter power on the actual
natural endpoint sequence. -/
theorem log_sq_div_quarter_rpow_nat_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 4 : ℝ))
      atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop 2
      (by norm_num : 0 < (1 / 4 : ℝ))).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def, Real.rpow_two] using hnat

/-- The genuine unique-outside-prime higher-power exception contributes zero
on the exact `n / log n` initial-deficiency scale.  This is unconditional for
every fixed finite support and every assignment; no prime-number theorem,
uniform progression estimate, or sieve assumption is required. -/
theorem initialDeficiencyPrimePowerTargets_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  let C : ℝ := (4 / Real.log 2) *
    (∏ p ∈ insert 2 S with p.Prime,
      (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹)
  have hupper : Tendsto
      (fun n : ℕ =>
        C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 4 : ℝ)))
      atTop (nhds 0) := by
    simpa using log_sq_div_quarter_rpow_nat_tendsto_zero.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    have hquarter : 0 < (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_pos_of_pos hnreal _
    have hcard :=
      initialDeficiencyPrimePowerTargets_card_le_three_quarters_log S b hn
    change ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) ≤
      C * (n : ℝ) ^ (3 / 4 : ℝ) * Real.log (n : ℝ) at hcard
    have hpow :
        (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) =
          (n : ℝ) := by
      rw [← Real.rpow_add hnreal]
      norm_num
    have hratio :
        (n : ℝ) ^ (3 / 4 : ℝ) / (n : ℝ) =
          1 / (n : ℝ) ^ (1 / 4 : ℝ) := by
      apply (div_eq_div_iff hnreal.ne' hquarter.ne').mpr
      simpa using hpow
    calc
      ((initialDeficiencyPrimePowerTargets S b n).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (C * (n : ℝ) ^ (3 / 4 : ℝ) * Real.log (n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
          exact (div_le_div_iff_of_pos_right (div_pos hnreal hlog)).mpr hcard
      _ = C * Real.log (n : ℝ) ^ 2 *
          ((n : ℝ) ^ (3 / 4 : ℝ) / (n : ℝ)) := by
          field_simp
      _ = C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [hratio]
          ring

/-- Unconditional exact reduction of the full initial-deficiency asymptotic
to its explicit moving smooth-core/reduced-prime-progression sum.  Both the
fixed-support smooth targets and the genuine repeated outside-prime powers
have now been eliminated without analytic hypotheses. -/
theorem initial_deficiency_asymptotic_iff_mainPrimeStratum
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
          ((n : ℝ) / Real.log n))
      atTop (nhds 1) :=
  initial_deficiency_asymptotic_iff_mainPrimeStratum_of_primePower_negligible
    S b hsupport htwo
    (initialDeficiencyPrimePowerTargets_normalized_tendsto_zero S b)

end Erdos689

#print axioms Erdos689.initialDeficiencyPrimePowerTargets_smooth_prime_power_representation
#print axioms Erdos689.initialDeficiencyPrimePowerTargets_subset_smooth_power_image
#print axioms Erdos689.initialDeficiencyPrimePowerTargets_card_le_smooth_mul_sqrt_mul_log
#print axioms Erdos689.supportSmoothNumbersUpTo_card_le_rpow_euler
#print axioms Erdos689.initialDeficiencyPrimePowerTargets_card_le_three_quarters_log
#print axioms Erdos689.log_sq_div_quarter_rpow_nat_tendsto_zero
#print axioms Erdos689.initialDeficiencyPrimePowerTargets_normalized_tendsto_zero
#print axioms Erdos689.initial_deficiency_asymptotic_iff_mainPrimeStratum
