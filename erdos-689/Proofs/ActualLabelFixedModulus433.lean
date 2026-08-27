import ActualLabelSieveMainTerm433
import ExceptionalSelectorAssembly433

/-!
# Fixed-modulus leading constant for actual fixed-label graph fibers

The true even excluded modulus is `2*W`, not `W`.  Its totient equals
`φ(W)` for an odd support, so the factor four in `(2*W/φ(W))²` exactly
cancels the true graph-endpoint factor `1/4`.  The resulting genuine
fixed-modulus Selberg leading constant is `121`, not `605/12`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The actual even excluded support modulus has exactly the original support
totient; the modulus itself is still twice the support product. -/
theorem actualOddSupport_totient_two_mul
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    (2 * (∏ p ∈ S, p)).totient = (∏ p ∈ S, p).totient := by
  apply Nat.totient_two_mul_of_odd
  exact Nat.coprime_two_right.mp
    (oddSupportDivisor_coprime_two S (∏ p ∈ S, p) hsupport dvd_rfl)

/-- The *actual* support-uniform fixed-label Selberg main term, including the
doubled excluded modulus and the exact graph endpoint, has eventual leading
constant `121`.  No moving excluded-prime or factor-four loss is omitted. -/
theorem actualFixedLabel_fixedModulus_main_term_eventually_le
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
          (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
            twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
              (selbergSquareRootBlockCutoff n ^ 2)) ≤
        (121 : ℝ) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  have hphi : 0 < W.totient := Nat.totient_pos.mpr hW
  have hphireal : (0 : ℝ) < W.totient := by exact_mod_cast hphi
  have htotient : (2 * W).totient = W.totient :=
    actualOddSupport_totient_two_mul S hsupport
  filter_upwards
    [twoRootSelbergDenominator_fixed_fifth_root_eventually_inv_le
      (2 * W) (by simp) (by omega)] with n hdenominator
  change
    (n : ℝ) * (W.totient : ℝ) ^ 2 /
        (4 * (W : ℝ) ^ 2 *
          twoRootSelbergDenominator (2 * W)
            (selbergSquareRootBlockCutoff n ^ 2)) ≤ _
  rw [htotient] at hdenominator
  have hmain : 0 ≤
      (n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2) := by
    positivity
  calc
    (n : ℝ) * (W.totient : ℝ) ^ 2 /
        (4 * (W : ℝ) ^ 2 *
          twoRootSelbergDenominator (2 * W)
            (selbergSquareRootBlockCutoff n ^ 2)) =
      ((n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2)) *
        (twoRootSelbergDenominator (2 * W)
          (selbergSquareRootBlockCutoff n ^ 2))⁻¹ := by
        rw [div_mul_eq_div_mul_one_div]
        rw [one_div]
    _ ≤ ((n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2)) *
          ((121 : ℝ) * (((2 * W : ℕ) : ℝ) / W.totient) ^ 2 /
            (Real.log (n : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hdenominator hmain
    _ = (121 : ℝ) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
      push_cast
      field_simp
      ring

/-- Every fixed constant is negligible on the genuine graph-degree scale. -/
theorem actualLabel_log_sq_div_nat_tendsto_zero :
    Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop 2
      (by norm_num : 0 < (1 : ℝ))).tendsto_div_nhds_zero
  have hnatural := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def, Real.rpow_two, Real.rpow_one] using hnatural

/-- With the genuine fixed even modulus and exact fifth-root block cutoff,
*all* errors in the proven summed actual fixed-label sieve are little-o of
`n/log(n)^2`, uniformly in the moving label itself. -/
theorem actualFixedLabel_fixedModulus_errors_normalized_tendsto_zero
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    Tendsto
      (fun n : ℕ =>
        (((actualCanonicalLabelCoefficientPairs S).card : ℝ) *
          ((((∏ p ∈ S, p) : ℕ) : ℝ) *
            (3 / twoRootSelbergDenominator (2 * (∏ p ∈ S, p))
                (selbergSquareRootBlockCutoff n ^ 2) +
              (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
                ((2 * Nat.primeCounting
                  (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))) +
            ((2 * S.card : ℕ) : ℝ))) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
      atTop (nhds 0) := by
  let W : ℕ := ∏ p ∈ S, p
  let K : ℝ := (121 : ℝ) * (((2 * W : ℕ) : ℝ) / W.totient) ^ 2
  let R : ℕ → ℝ := fun n =>
    (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
      ((2 * Nat.primeCounting
        (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ))
  let A : ℝ := ((actualCanonicalLabelCoefficientPairs S).card : ℝ) * W
  let B : ℝ := ((actualCanonicalLabelCoefficientPairs S).card : ℝ) *
    ((W : ℝ) * (3 * K) + ((2 * S.card : ℕ) : ℝ))
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
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
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by
      have hdenominator := twoRootSelbergDenominator_nonneg
        (M := 2 * (∏ p ∈ S, p)) (by simp)
        (selbergSquareRootBlockCutoff n ^ 2)
      positivity)) _ hmajor
  have hlogtop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards
    [twoRootSelbergDenominator_fixed_fifth_root_eventually_inv_le
      (2 * W) (by simp) (by omega),
      (tendsto_atTop.1 hlogtop 1)] with n hdenominator hlog
  have htotient := actualOddSupport_totient_two_mul S hsupport
  change (2 * W).totient = W.totient at htotient
  rw [htotient] at hdenominator
  change (1 : ℝ) ≤ Real.log (n : ℝ) at hlog
  have hlogpow : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have hdenbound :
      (twoRootSelbergDenominator (2 * W)
        (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤ K := by
    calc
      (twoRootSelbergDenominator (2 * W)
        (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤
        K / Real.log (n : ℝ) ^ 2 := hdenominator
      _ ≤ K / 1 := by gcongr
      _ = K := by simp
  have hthree :
      3 / twoRootSelbergDenominator (2 * W)
        (selbergSquareRootBlockCutoff n ^ 2) ≤ 3 * K := by
    rw [div_eq_mul_inv]
    nlinarith
  change
    (((actualCanonicalLabelCoefficientPairs S).card : ℝ) *
      ((W : ℝ) *
        (3 / twoRootSelbergDenominator (2 * W)
            (selbergSquareRootBlockCutoff n ^ 2) + R n) +
        ((2 * S.card : ℕ) : ℝ))) /
      ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤ _
  calc
    (((actualCanonicalLabelCoefficientPairs S).card : ℝ) *
      ((W : ℝ) *
        (3 / twoRootSelbergDenominator (2 * W)
            (selbergSquareRootBlockCutoff n ^ 2) + R n) +
        ((2 * S.card : ℕ) : ℝ))) /
      ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
      (((actualCanonicalLabelCoefficientPairs S).card : ℝ) *
        ((W : ℝ) * (3 * K + R n) +
          ((2 * S.card : ℕ) : ℝ))) /
        ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
          gcongr
    _ = A * (R n / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) +
        B * (1 / ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) := by
          dsimp [A, B]
          ring

/-- The sum of *actual edge-bounded fixed-label graph fibers* over all
coprime support-divisor pairs is eventually bounded by
`122*n/log(n)^2`.  Every sieve prime condition is the exact existing
fixed-modulus Selberg condition, and the moving label is only required to
avoid the actual sieve primes.  No prime-pattern, density, graph-degree,
or Selberg remainder bound is postulated. -/
theorem actualFixedLabel_fixedModulus_fiber_sum_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (z : ℕ) (P : Finset ℕ),
        (∀ p ∈ S, ¬ p ∣ z) →
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, 2 < p) →
        (∀ p ∈ P, ¬ p ∣ z) →
        Nat.Coprime (∏ p ∈ P, p) (2 * (∏ p ∈ S, p)) →
        (∀ p : ℕ, p.Prime →
          (p ∣ ∏ q ∈ P, q ↔
            p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
              Nat.Coprime p (2 * (∏ p ∈ S, p)))) →
        (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
          ((edgeBoundedLabelFiberSwitchedPrimeParameters
            S b n z c.1 c.2).card : ℝ)) ≤
          (122 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  have hsmall :=
    (actualFixedLabel_fixedModulus_errors_normalized_tendsto_zero
      S hsupport).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [actualFixedLabel_fixedModulus_main_term_eventually_le S hsupport,
      hsmall, eventually_ge_atTop 2] with n hmain herror hn
  intro z P hz hprime hlarge havoidz hPM hprimes
  have hnpositive : 0 < n := by omega
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hscale : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    positivity
  have hcutoff : 0 < selbergSquareRootBlockCutoff n ^ 2 :=
    selbergSquareRootBlockCutoff_sq_pos_of_pos n hnpositive
  have hWM : (∏ p ∈ S, p) ∣ 2 * (∏ p ∈ S, p) := by
    refine ⟨2, ?_⟩
    ring
  have hfinite := actualCanonicalLabelFiber_sum_le_sharp_main_and_errors
    S P b n z (2 * (∏ p ∈ S, p))
      (selbergSquareRootBlockCutoff n ^ 2)
      hsupport hz hb hprime hlarge hcutoff havoidz
      (by simp) hPM hWM hprimes
  have herror' := (div_lt_one hscale).mp herror
  nlinarith

#print axioms Erdos689.actualOddSupport_totient_two_mul
#print axioms Erdos689.actualFixedLabel_fixedModulus_main_term_eventually_le
#print axioms Erdos689.actualLabel_log_sq_div_nat_tendsto_zero
#print axioms Erdos689.actualFixedLabel_fixedModulus_errors_normalized_tendsto_zero
#print axioms Erdos689.actualFixedLabel_fixedModulus_fiber_sum_eventually_le

end Erdos689
