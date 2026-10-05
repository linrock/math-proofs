module

public import ActualRightVertexLeftAuditBounds433

@[expose] public section


/-!
# Uniform complete moving-determinant fixed-left Selberg errors

All actual fixed-left coefficient-summed errors are negligible on the
original `n/log(n)^2` scale uniformly in every moving determinant prime.
The bound retains the incomplete-block term, cutoff-fourth-power remainder,
small-sieve-prime exceptions, and both support-prime exception families.
No moving-prime-independent remainder is assumed: it follows from the
previously verified explicit uniform reciprocal Selberg bound.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The complete actual moving-modulus fixed-left Selberg error normalized
by the true graph-degree scale converges uniformly to zero over EVERY
genuine moving determinant prime, expressed in the exact eventual-ε form. -/
theorem actualLeftMoving_fixedModulus_errors_normalized_eventually_lt
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, r.Prime →
        (((((∏ p ∈ S, p).divisors.card : ℕ) : ℝ)) *
          ((((∏ p ∈ S, p) : ℕ) : ℝ) *
            (2 / twoRootSelbergDenominator
                ((6 * (∏ p ∈ S, p)) * actualLeftMovingExcludedPrime S r)
                (selbergSquareRootBlockCutoff n ^ 2) +
              (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
                ((2 * Nat.primeCounting
                  (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
            ((2 * S.card : ℕ) : ℝ))) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) < ε := by
  let W : ℕ := ∏ p ∈ S, p
  let M : ℕ := 6 * W
  let K : ℝ := (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2)
  let R : ℕ → ℝ := fun n =>
    (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
      ((2 * Nat.primeCounting
        (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))
  let A : ℝ := (W.divisors.card : ℝ) * W
  let B : ℝ := (W.divisors.card : ℝ) *
    ((W : ℝ) * (2 * K) + ((2 * S.card : ℕ) : ℝ))
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hM : 2 ∣ M :=
    dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) W
  have hMtwo : 2 ≤ M := by dsimp [M]; omega
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hscale :
      Tendsto
        (fun n : ℕ =>
          1 / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
        atTop (nhds 0) := by
    simpa [one_div, inv_div] using actualLabel_log_sq_div_nat_tendsto_zero
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          A * (R n / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) +
          B * (1 / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)))
        atTop (nhds 0) := by
    simpa [R] using
      (selberg_block_cutoff_complete_remainder_normalized_tendsto_zero.const_mul A).add
        (hscale.const_mul B)
  have hsmall := hmajor.eventually (gt_mem_nhds hε)
  have hlogtop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards
    [twoRootSelbergDenominator_fifth_root_eventually_inv_le_explicit
      M hM hMtwo,
      hsmall,
      (tendsto_atTop.1 hlogtop 1)] with n hreciprocal hbound hlog
  intro r hr
  have hchosen := actualLeftMovingExcludedPrime_prime_coprime_ge_five
    S r (fun p hp => (hsupport p hp).1) hr
  have hrec := hreciprocal
    (actualLeftMovingExcludedPrime S r)
      hchosen.1 hchosen.2.1 hchosen.2.2
  change (1 : ℝ) ≤ Real.log (n : ℝ) at hlog
  have hlogpow : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have hinv :
      (twoRootSelbergDenominator
        (M * actualLeftMovingExcludedPrime S r)
        (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤ K := by
    calc
      (twoRootSelbergDenominator
        (M * actualLeftMovingExcludedPrime S r)
        (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤
          K / (Real.log (n : ℝ)) ^ 2 := hrec
      _ ≤ K := (div_le_self hK hlogpow)
  have hdenominator : 0 ≤ twoRootSelbergDenominator
      (M * actualLeftMovingExcludedPrime S r)
      (selbergSquareRootBlockCutoff n ^ 2) :=
    twoRootSelbergDenominator_nonneg
      (dvd_mul_of_dvd_left hM (actualLeftMovingExcludedPrime S r))
      (selbergSquareRootBlockCutoff n ^ 2)
  have herror :
      (2 : ℝ) / twoRootSelbergDenominator
        (M * actualLeftMovingExcludedPrime S r)
        (selbergSquareRootBlockCutoff n ^ 2) ≤ 2 * K := by
    change 2 * (twoRootSelbergDenominator
      (M * actualLeftMovingExcludedPrime S r)
      (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤ 2 * K
    gcongr
  have hpoint :
      ((W.divisors.card : ℝ) *
        ((W : ℝ) *
          (2 / twoRootSelbergDenominator
              (M * actualLeftMovingExcludedPrime S r)
              (selbergSquareRootBlockCutoff n ^ 2) + R n) +
          ((2 * S.card : ℕ) : ℝ))) /
        ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
      A * (R n / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) +
        B * (1 / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) := by
    calc
      ((W.divisors.card : ℝ) *
        ((W : ℝ) *
          (2 / twoRootSelbergDenominator
              (M * actualLeftMovingExcludedPrime S r)
              (selbergSquareRootBlockCutoff n ^ 2) + R n) +
          ((2 * S.card : ℕ) : ℝ))) /
        ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
        ((W.divisors.card : ℝ) *
          ((W : ℝ) * (2 * K + R n) +
            ((2 * S.card : ℕ) : ℝ))) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by gcongr
      _ = A * (R n / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) +
          B * (1 / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) := by
        dsimp [A, B]
        ring
  change
    ((W.divisors.card : ℝ) *
      ((W : ℝ) *
        (2 / twoRootSelbergDenominator
            (M * actualLeftMovingExcludedPrime S r)
            (selbergSquareRootBlockCutoff n ^ 2) + R n) +
        ((2 * S.card : ℕ) : ℝ))) /
      ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) < ε
  exact hpoint.trans_lt hbound

/-- The ENTIRE actual fixed-left moving-modulus coefficient-summed error is
eventually less than one original graph-degree unit, uniformly in every
moving determinant prime and including the determinant-three branch. -/
theorem actualLeftMoving_fixedModulus_errors_eventually_lt_scale
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, r.Prime →
        (((((∏ p ∈ S, p).divisors.card : ℕ) : ℝ)) *
          ((((∏ p ∈ S, p) : ℕ) : ℝ) *
            (2 / twoRootSelbergDenominator
                ((6 * (∏ p ∈ S, p)) * actualLeftMovingExcludedPrime S r)
                (selbergSquareRootBlockCutoff n ^ 2) +
              (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
                ((2 * Nat.primeCounting
                  (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
            ((2 * S.card : ℕ) : ℝ))) <
          (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
  filter_upwards
    [actualLeftMoving_fixedModulus_errors_normalized_eventually_lt
      S hsupport 1 (by norm_num), eventually_ge_atTop 2] with n herror hn
  intro r hr
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hscale : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by positivity
  exact (div_lt_one hscale).mp (herror r hr)


end Erdos689
