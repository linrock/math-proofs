import DeficiencyClassification
import DeficiencySmooth433

/-!
# Fixed-support smooth exceptional targets for Erdős problem #689

Mathlib already proves that the positive `k`-smooth integers below `n` have
cardinality at most `2 ^ π(k - 1) * sqrt n`.  The statements below transfer
that unconditional theorem to the *actual* switched-prime support and to the
actual initially deficient odd targets.  In particular their contribution is
negligible on the `n / log n` scale; no prime-pattern or sieve conjecture is
assumed.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Positive closed-interval integers whose prime factors all lie in `S`. -/
def supportSmoothNumbersUpTo (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => m.primeFactors ⊆ S

/-- A support prime lies below the canonical finite-support smooth cutoff. -/
theorem support_prime_lt_smooth_cutoff {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) : p < S.sup id + 1 := by
  have hle : p ≤ S.sup id := Finset.le_sup (f := @id ℕ) hp
  omega

/-- Every positive integer supported on `S` is genuinely smooth for its
canonical cutoff, including the empty-support case. -/
theorem mem_smoothNumbers_of_primeFactors_subset_support
    {S : Finset ℕ} {m : ℕ} (hm : m ≠ 0)
    (hsupport : m.primeFactors ⊆ S) :
    m ∈ Nat.smoothNumbers (S.sup id + 1) := by
  apply Nat.mem_smoothNumbers_of_primeFactors_subset hm
  intro p hp
  exact Finset.mem_range.mpr
    (support_prime_lt_smooth_cutoff (hsupport hp))

/-- The exact switched-support smooth targets embed into Mathlib's bounded
smooth-number set. -/
theorem supportSmoothNumbersUpTo_subset (S : Finset ℕ) (n : ℕ) :
    supportSmoothNumbersUpTo S n ⊆
      Nat.smoothNumbersUpTo n (S.sup id + 1) := by
  intro m hm
  obtain ⟨hinterval, hsupport⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmpos, hmn⟩ := Finset.mem_Icc.mp hinterval
  exact Nat.mem_smoothNumbersUpTo.mpr
    ⟨hmn, mem_smoothNumbers_of_primeFactors_subset_support
      (by omega) hsupport⟩

/-- An explicit fixed-support square-root bound for all actual smooth targets. -/
theorem supportSmoothNumbersUpTo_card_le (S : Finset ℕ) (n : ℕ) :
    (supportSmoothNumbersUpTo S n).card ≤
      2 ^ (S.sup id + 1).primesBelow.card * n.sqrt := by
  exact (Finset.card_le_card (supportSmoothNumbersUpTo_subset S n)).trans
    (Nat.smoothNumbersUpTo_card_le n (S.sup id + 1))

/-- The square-root saving dominates the logarithmic normalization on the
actual natural endpoint sequence. -/
theorem log_div_sqrt_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ))
      atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Real.sqrt_eq_rpow, Function.comp_def] using hnat

/-- Fixed-support smooth targets have zero density on the exact prime-counting
scale required by the initial-deficiency asymptotic. -/
theorem supportSmoothNumbersUpTo_normalized_tendsto_zero (S : Finset ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((supportSmoothNumbersUpTo S n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  let C : ℝ := (2 ^ (S.sup id + 1).primesBelow.card : ℕ)
  have hC : 0 ≤ C := by positivity
  have hupper : Tendsto
      (fun n : ℕ => C * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)))
      atTop (nhds 0) := by
    simpa using log_div_sqrt_nat_tendsto_zero.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hnreal
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
    have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hcard : ((supportSmoothNumbersUpTo S n).card : ℝ) ≤
        C * (n.sqrt : ℝ) := by
      dsimp [C]
      exact_mod_cast supportSmoothNumbersUpTo_card_le S n
    have hrootbound : (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    calc
      ((supportSmoothNumbersUpTo S n).card : ℝ) /
          ((n : ℝ) / Real.log n) ≤
        (C * Real.sqrt (n : ℝ)) / ((n : ℝ) / Real.log n) := by
          apply (div_le_div_iff_of_pos_right (div_pos hnpos hlog)).mpr
          exact hcard.trans (mul_le_mul_of_nonneg_left hrootbound hC)
      _ = C * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) := by
          have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
            Real.sq_sqrt hnpos.le
          field_simp
          nlinarith

/-- Completely multiplicative reciprocal real powers on the natural numbers. -/
noncomputable def smoothReciprocalRpow (a : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-a)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)

/-- Every prime has reciprocal real-power weight strictly below one. -/
theorem smoothReciprocalRpow_prime_norm_lt_one {a : ℝ} (ha : 0 < a)
    {p : ℕ} (hp : p.Prime) :
    ‖smoothReciprocalRpow a p‖ < 1 := by
  have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans (by norm_num) hpone
  change ‖(p : ℝ) ^ (-a)‖ < 1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hppos.le _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hpone (neg_lt_zero.mpr ha)

/-- The exact finite-support Euler product converges for *every* positive
reciprocal exponent, including the Rankin exponent one half. -/
theorem supportSmooth_reciprocal_rpow_hasSum
    (S : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    HasSum
      (fun m : Nat.factoredNumbers S => ((m : ℕ) : ℝ) ^ (-a))
      (∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-a))⁻¹) := by
  have heuler :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := smoothReciprocalRpow a)
      (fun {_} hp => smoothReciprocalRpow_prime_norm_lt_one ha hp) S
  exact heuler.2

/-- Fixed-support smooth reciprocal powers are summable below the ordinary
zeta convergence threshold; in particular exponent `1 / 2` is allowed. -/
theorem supportSmooth_reciprocal_rpow_summable
    (S : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    Summable
      (fun m : Nat.factoredNumbers S => ((m : ℕ) : ℝ) ^ (-a)) :=
  (supportSmooth_reciprocal_rpow_hasSum S ha).summable

/-- Exact explicit value of the fixed-support reciprocal real-power mass. -/
theorem supportSmooth_reciprocal_rpow_tsum
    (S : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    (∑' m : Nat.factoredNumbers S, ((m : ℕ) : ℝ) ^ (-a)) =
      ∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-a))⁻¹ :=
  (supportSmooth_reciprocal_rpow_hasSum S ha).tsum_eq

/-- The complete quantitative Rankin bound for any finite tail of actual
fixed-support smooth integers.  The exponent may be chosen to be one half. -/
theorem supportSmooth_reciprocal_rankin_tail
    (S : Finset ℕ) (F : Finset (Nat.factoredNumbers S))
    {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθone : θ < 1)
    (hlarge : ∀ m ∈ F, R ≤ ((m : ℕ) : ℝ)) :
    (∑ m ∈ F, (((m : ℕ) : ℝ))⁻¹) ≤
      R ^ (-θ) *
        (∏ p ∈ S with p.Prime,
          (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹) := by
  have hremaining : 0 < 1 - θ := sub_pos.mpr hθone
  have hsummable :=
    supportSmooth_reciprocal_rpow_summable S hremaining
  have hmass :
      (∑ m ∈ F, (((m : ℕ) : ℝ)) ^ (-(1 - θ))) ≤
        ∏ p ∈ S with p.Prime,
          (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹ := by
    calc
      (∑ m ∈ F, (((m : ℕ) : ℝ)) ^ (-(1 - θ))) ≤
          ∑' m : Nat.factoredNumbers S,
            (((m : ℕ) : ℝ)) ^ (-(1 - θ)) :=
        hsummable.sum_le_tsum F fun m _ =>
          Real.rpow_nonneg (by positivity) _
      _ = _ := supportSmooth_reciprocal_rpow_tsum S hremaining
  calc
    (∑ m ∈ F, (((m : ℕ) : ℝ))⁻¹) ≤
        ∑ m ∈ F,
          R ^ (-θ) * (((m : ℕ) : ℝ)) ^ (-(1 - θ)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : (0 : ℝ) < ((m : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero m.property.1
      have hcompare :
          (((m : ℕ) : ℝ)) ^ (-θ) ≤ R ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos hR (hlarge m hm) (by linarith)
      calc
        (((m : ℕ) : ℝ))⁻¹ =
            (((m : ℕ) : ℝ)) ^ (-θ) *
              (((m : ℕ) : ℝ)) ^ (-(1 - θ)) := by
          rw [← Real.rpow_add hmpos]
          convert (Real.rpow_neg_one (((m : ℕ) : ℝ))).symm using 1
          ring_nf
        _ ≤ R ^ (-θ) * (((m : ℕ) : ℝ)) ^ (-(1 - θ)) :=
          mul_le_mul_of_nonneg_right hcompare
            (Real.rpow_nonneg hmpos.le _)
    _ = R ^ (-θ) *
          (∑ m ∈ F, (((m : ℕ) : ℝ)) ^ (-(1 - θ))) := by
      rw [Finset.mul_sum]
    _ ≤ R ^ (-θ) *
          (∏ p ∈ S with p.Prime,
            (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹) :=
      mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hR.le _)

/-- The manuscript's genuine even smooth coefficients are exactly usable as
positive integers supported on `insert 2 S`. -/
theorem deficiencySmoothCoefficient_mem_factoredNumbers
    {S : Finset ℕ} {c : ℕ}
    (hc : deficiencySmoothCoefficient S c) :
    c ∈ Nat.factoredNumbers (insert 2 S) := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hdiv
  rcases hc.2.2 p hp hdiv with htwo | hsupport
  · exact htwo ▸ Finset.mem_insert_self 2 S
  · exact Finset.mem_insert_of_mem hsupport

/-- Direct natural-valued Rankin tail, convenient for coefficient finsets
without manually constructing a subtype-indexed family. -/
theorem supportSmooth_reciprocal_rankin_tail_finset
    (S F : Finset ℕ) {R θ : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθone : θ < 1)
    (hsmooth : ∀ m ∈ F, m ∈ Nat.factoredNumbers S)
    (hlarge : ∀ m ∈ F, R ≤ (m : ℝ)) :
    (∑ m ∈ F, (m : ℝ)⁻¹) ≤
      R ^ (-θ) *
        (∏ p ∈ S with p.Prime,
          (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹) := by
  let embedding : {m : ℕ // m ∈ F} ↪ Nat.factoredNumbers S :=
    ⟨fun m => ⟨m, hsmooth m m.property⟩, by
      intro m m' heq
      apply Subtype.ext
      exact congrArg (fun x : Nat.factoredNumbers S => (x : ℕ)) heq⟩
  let lifted := F.attach.map embedding
  have hlarge_lifted :
      ∀ m ∈ lifted, R ≤ ((m : ℕ) : ℝ) := by
    intro m hm
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hm
    subst m
    exact hlarge v v.property
  have htail := supportSmooth_reciprocal_rankin_tail
    S lifted hR hθ hθone hlarge_lifted
  have hsum :
      (∑ m ∈ lifted, (((m : ℕ) : ℝ))⁻¹) =
        ∑ m ∈ F, (m : ℝ)⁻¹ := by
    dsimp [lifted]
    rw [Finset.sum_map]
    change (∑ m ∈ F.attach, ((m.val : ℝ))⁻¹) = _
    exact Finset.sum_attach F fun m => (m : ℝ)⁻¹
  rwa [hsum] at htail

/-- The actual odd targets with fewer than two initial prime-congruence hits. -/
def oddInitiallyDeficientTargets (S : Finset ℕ) (b : ℕ → ℕ)
    (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m =>
    m % 2 = 1 ∧ coverage n (initialAssignment S b) m < 2

/-- Every actual odd initially deficient target is supported on the switched
primes, without changing the closed target interval. -/
theorem oddInitiallyDeficientTargets_subset_supportSmooth
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) :
    oddInitiallyDeficientTargets S b n ⊆ supportSmoothNumbersUpTo S n := by
  intro m hm
  obtain ⟨hinterval, hodd, hdeficient⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmpos, hmn⟩ := Finset.mem_Icc.mp hinterval
  exact Finset.mem_filter.mpr
    ⟨hinterval, odd_deficient_primeFactors_subset_support
      hmpos hmn hn hodd hdeficient⟩

/-- Actual odd deficient targets satisfy the same explicit square-root bound. -/
theorem oddInitiallyDeficientTargets_card_le
    (S : Finset ℕ) (b : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (oddInitiallyDeficientTargets S b n).card ≤
      2 ^ (S.sup id + 1).primesBelow.card * n.sqrt := by
  exact (Finset.card_le_card
    (oddInitiallyDeficientTargets_subset_supportSmooth S b hn)).trans
    (supportSmoothNumbersUpTo_card_le S n)

/-- Odd genuinely deficient targets are negligible relative to `n / log n`. -/
theorem oddInitiallyDeficientTargets_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((oddInitiallyDeficientTargets S b n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (supportSmoothNumbersUpTo_normalized_tendsto_zero S) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hden : 0 < (n : ℝ) / Real.log n :=
      div_pos (by positivity) (Real.log_pos hnreal)
    apply (div_le_div_iff_of_pos_right hden).mpr
    exact_mod_cast Finset.card_le_card
      (oddInitiallyDeficientTargets_subset_supportSmooth S b hn)

/-- The actual initial demand restricted to a fixed smooth support. -/
def supportSmoothInitialDeficiency (S T : Finset ℕ) (b : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  ∑ m ∈ supportSmoothNumbersUpTo T n,
    (2 - coverage n (initialAssignment S b) m)

/-- Each smooth target contributes at most two genuine deficiency tokens. -/
theorem supportSmoothInitialDeficiency_le_two_card
    (S T : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) :
    supportSmoothInitialDeficiency S T b n ≤
      2 * (supportSmoothNumbersUpTo T n).card := by
  unfold supportSmoothInitialDeficiency
  calc
    (∑ m ∈ supportSmoothNumbersUpTo T n,
      (2 - coverage n (initialAssignment S b) m)) ≤
        ∑ _m ∈ supportSmoothNumbersUpTo T n, 2 := by
          apply Finset.sum_le_sum
          intro m hm
          omega
    _ = 2 * (supportSmoothNumbersUpTo T n).card := by simp [Nat.mul_comm]

/-- The entire smooth-support part of the actual initial deficiency, even with
two-token targets, is negligible on the exact `n / log n` scale. -/
theorem supportSmoothInitialDeficiency_normalized_tendsto_zero
    (S T : Finset ℕ) (b : ℕ → ℕ) :
    Tendsto
      (fun n : ℕ =>
        (supportSmoothInitialDeficiency S T b n : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n : ℕ =>
        (2 : ℝ) * (((supportSmoothNumbersUpTo T n).card : ℝ) /
          ((n : ℝ) / Real.log n)))
      atTop (nhds 0) := by
    simpa using (supportSmoothNumbersUpTo_normalized_tendsto_zero T).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hden : 0 < (n : ℝ) / Real.log n :=
      div_pos (by positivity) (Real.log_pos hnreal)
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hden).mpr
    exact_mod_cast supportSmoothInitialDeficiency_le_two_card S T b n

#print axioms support_prime_lt_smooth_cutoff
#print axioms mem_smoothNumbers_of_primeFactors_subset_support
#print axioms supportSmoothNumbersUpTo_subset
#print axioms supportSmoothNumbersUpTo_card_le
#print axioms log_div_sqrt_nat_tendsto_zero
#print axioms supportSmoothNumbersUpTo_normalized_tendsto_zero
#print axioms smoothReciprocalRpow_prime_norm_lt_one
#print axioms supportSmooth_reciprocal_rpow_hasSum
#print axioms supportSmooth_reciprocal_rpow_summable
#print axioms supportSmooth_reciprocal_rpow_tsum
#print axioms supportSmooth_reciprocal_rankin_tail
#print axioms deficiencySmoothCoefficient_mem_factoredNumbers
#print axioms supportSmooth_reciprocal_rankin_tail_finset
#print axioms oddInitiallyDeficientTargets_subset_supportSmooth
#print axioms oddInitiallyDeficientTargets_card_le
#print axioms oddInitiallyDeficientTargets_normalized_tendsto_zero
#print axioms supportSmoothInitialDeficiency_le_two_card
#print axioms supportSmoothInitialDeficiency_normalized_tendsto_zero

end Erdos689
