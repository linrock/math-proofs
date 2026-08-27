import ActualLeftVertexMajorIntegration433

/-!
# Genuine prime-filtered `lcm(q,W)` major-arc residue-cell models

Inside a unit residue cell of the true common modulus, the actual switched
left and center prime windows are EXACTLY their coefficient-sensitive
interval progressions when their genuine switched masks vanish.  The
robust label window is exactly its actual fixed-residue interval
progression.  Applying the already proved Siegel--Walfisz/Abel interval
result and the independent proper-prime-power estimate yields an actual
prime-only, exponentially rated cell model at the ORIGINAL rational Farey
center; its numerator is correctly rescaled from `q` to `lcm(q,W)`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- A genuine unit residue modulo `lcm(q,W)` forces every prime in that
residue class to avoid the switched support. -/
theorem actualMajorArcLcm_unit_cell_prime_outside_support
    (S : Finset ℕ) (denominator residue p : ℕ)
    (_hsupport : ∀ s ∈ S, s.Prime)
    (hp : p.Prime)
    (hresidue : p % actualMajorArcLcmResidueModulus S denominator = residue)
    (hunit : Nat.Coprime residue
      (actualMajorArcLcmResidueModulus S denominator)) :
    p ∉ S := by
  let L := actualMajorArcLcmResidueModulus S denominator
  have hpunit : Nat.Coprime p L := by
    apply (ZMod.coprime_mod_iff_coprime p L).mp
    simpa [L, hresidue] using hunit
  intro hpS
  have hpW : p ∣ ∏ s ∈ S, s :=
    Finset.dvd_prod_of_mem (fun s : ℕ => s) hpS
  have hpL : p ∣ L := dvd_trans hpW
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  exact (hp.coprime_iff_not_dvd.mp hpunit) hpL

/-- On a genuine unit residue cell with an admissible switched target, the
ACTUAL fixed-left prime window is exactly the prime-filtered interval
`[1,n/(2*a)+1)` in that common residue class. -/
theorem actualMajorArcLeftPrime_unit_cell_eq_interval
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n a denominator residue : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : 0 < a)
    (hunit : Nat.Coprime residue
      (actualMajorArcLcmResidueModulus S denominator))
    (hswitched : switchedHits S b (2 * (a * residue)) = 0) :
    (actualMajorArcLeftPrimeWindow S b n a).filter
      (fun t => t % actualMajorArcLcmResidueModulus S denominator = residue) =
      ((Finset.Ico 1 (n / (2 * a) + 1)).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator = residue)).filter
          Nat.Prime := by
  classical
  let L := actualMajorArcLcmResidueModulus S denominator
  have hcoefficient : 0 < 2 * a := by omega
  ext t
  constructor
  · intro ht
    obtain ⟨hwindow, hcell⟩ := Finset.mem_filter.mp ht
    obtain ⟨hinterval, htprime, _, hbound, _⟩ :=
      Finset.mem_filter.mp hwindow
    have hdiv : t ≤ n / (2 * a) := by
      apply (Nat.le_div_iff_mul_le hcoefficient).mpr
      convert hbound using 1
      ring
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hinterval).1,
        by omega⟩, hcell⟩, htprime⟩
  · intro ht
    obtain ⟨hfiltered, htprime⟩ := Finset.mem_filter.mp ht
    obtain ⟨hinterval, hcell⟩ := Finset.mem_filter.mp hfiltered
    obtain ⟨htlower, htupper⟩ := Finset.mem_Ico.mp hinterval
    have hdiv : t ≤ n / (2 * a) := by omega
    have hmul : t * (2 * a) ≤ n :=
      (Nat.le_div_iff_mul_le hcoefficient).mp hdiv
    have hbound : 2 * (a * t) ≤ n := by
      convert hmul using 1
      ring
    have htn : t ≤ n := by nlinarith
    have houtside := actualMajorArcLcm_unit_cell_prime_outside_support
      S denominator residue t hsupport htprime hcell hunit
    have htarget : switchedHits S b (2 * (a * t)) = 0 := by
      have hperiod := actualMajorArcLcm_support_switchedHits_eq
        S b denominator (2 * a) t
      have hleft : 2 * (a * t) = (2 * a) * t := by ring
      have hright : 2 * (a * residue) = (2 * a) * residue := by ring
      rw [hleft, hperiod, hcell, ← hright]
      exact hswitched
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcell⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨htlower, htn⟩,
      htprime, houtside, hbound, htarget⟩

/-- On a genuine unit residue cell with an admissible switched target, the
ACTUAL fixed-center prime window is exactly the prime-filtered interval
`[1,n/(4*d)+1)`, retaining the ORIGINAL `4*d*t ≤ n` endpoint. -/
theorem actualMajorArcCenterPrime_unit_cell_eq_interval
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n d denominator residue : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hd : 0 < d)
    (hunit : Nat.Coprime residue
      (actualMajorArcLcmResidueModulus S denominator))
    (hswitched : switchedHits S b (2 * (2 * d * residue)) = 0) :
    (actualMajorArcCenterPrimeWindow S b n d).filter
      (fun t => t % actualMajorArcLcmResidueModulus S denominator = residue) =
      ((Finset.Ico 1 (n / (4 * d) + 1)).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator = residue)).filter
          Nat.Prime := by
  classical
  let L := actualMajorArcLcmResidueModulus S denominator
  have hcoefficient : 0 < 4 * d := by omega
  ext t
  constructor
  · intro ht
    obtain ⟨hwindow, hcell⟩ := Finset.mem_filter.mp ht
    obtain ⟨hinterval, htprime, _, hbound, _⟩ :=
      Finset.mem_filter.mp hwindow
    have hdiv : t ≤ n / (4 * d) := by
      apply (Nat.le_div_iff_mul_le hcoefficient).mpr
      convert hbound using 1
      ring
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hinterval).1,
        by omega⟩, hcell⟩, htprime⟩
  · intro ht
    obtain ⟨hfiltered, htprime⟩ := Finset.mem_filter.mp ht
    obtain ⟨hinterval, hcell⟩ := Finset.mem_filter.mp hfiltered
    obtain ⟨htlower, htupper⟩ := Finset.mem_Ico.mp hinterval
    have hdiv : t ≤ n / (4 * d) := by omega
    have hmul : t * (4 * d) ≤ n :=
      (Nat.le_div_iff_mul_le hcoefficient).mp hdiv
    have hbound : 2 * (2 * d * t) ≤ n := by
      convert hmul using 1
      ring
    have htn : t ≤ n := by nlinarith
    have houtside := actualMajorArcLcm_unit_cell_prime_outside_support
      S denominator residue t hsupport htprime hcell hunit
    have htarget : switchedHits S b (2 * (2 * d * t)) = 0 := by
      have hperiod := actualMajorArcLcm_support_switchedHits_eq
        S b denominator (4 * d) t
      have hleft : 2 * (2 * d * t) = (4 * d) * t := by ring
      have hright : 2 * (2 * d * residue) = (4 * d) * residue := by ring
      rw [hleft, hperiod, hcell, ← hright]
      exact hswitched
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcell⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨htlower, htn⟩,
      htprime, houtside, hbound, htarget⟩

/-- Every common-modulus label cell whose support projection is the actual
robust residue is exactly its true strict/weak prime interval progression. -/
theorem actualMajorArcLabelPrime_compatible_cell_eq_interval
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target denominator residue : ℕ) (τ ell : ℝ)
    (htarget : target ∈ robustResidues S b J)
    (hprojection : residue % (∏ p ∈ S, p) = target) :
    (actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
      (fun t => t % actualMajorArcLcmResidueModulus S denominator = residue) =
      ((Finset.Ico (manuscriptRealLabelLower τ n)
          (manuscriptRealLabelUpper τ ell n)).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator = residue)).filter
          Nat.Prime := by
  classical
  rw [actualMajorArcLabelPrimeWindow_eq_residue_prime_filter
    S b n J target τ ell htarget]
  let W := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hWdiv : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  ext t
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨ht, _⟩, htprime⟩, hcell⟩
    exact ⟨⟨ht, hcell⟩, htprime⟩
  · rintro ⟨⟨ht, hcell⟩, htprime⟩
    have hsupportclass : t % W = target := by
      calc
        t % W = (t % L) % W := (Nat.mod_mod_of_dvd t hWdiv).symm
        _ = residue % W := by rw [hcell]
        _ = target := hprojection
    exact ⟨⟨⟨ht, hsupportclass⟩, htprime⟩, hcell⟩

/-- The ORIGINAL rational Farey center `h/q` equals the correctly lifted
center `h*(L/q)/L` for `L=lcm(q,W)`; replacing its numerator without this
factor would assign incorrect major-arc phases. -/
theorem actualMajorArcLcm_rescaled_rational_center
    (S : Finset ℕ) (denominator : ℕ) (numerator : ℤ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (numerator : ℝ) / denominator =
      ((numerator *
        ((actualMajorArcLcmResidueModulus S denominator / denominator : ℕ) : ℤ)
          : ℤ) : ℝ) /
        (actualMajorArcLcmResidueModulus S denominator : ℝ) := by
  let L := actualMajorArcLcmResidueModulus S denominator
  have hL : 0 < L :=
    actualMajorArcLcmResidueModulus_pos S denominator hdenominator hsupport
  have hdivide : denominator ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).1
  have hfactor : denominator * (L / denominator) = L :=
    Nat.mul_div_cancel' hdivide
  have hfactorReal := congrArg (fun k : ℕ => (k : ℝ)) hfactor
  push_cast at hfactorReal
  have hdreal : (denominator : ℝ) ≠ 0 := by exact_mod_cast hdenominator.ne'
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  change
    (numerator : ℝ) / denominator =
      ((numerator * ((L / denominator : ℕ) : ℤ) : ℤ) : ℝ) / L
  norm_num only [Int.cast_mul, Int.cast_natCast]
  apply (div_eq_div_iff hdreal hLreal).mpr
  rw [← hfactorReal]
  ring

/-- The ACTUAL shifted rational center `h/q-j/W+k` has common-modulus
numerator `h*(L/q)-j*(L/W)+k*L`; both the support shift and the periodic
lift survive exactly, including denominators sharing support prime powers. -/
theorem actualMajorArcLcm_rescaled_shifted_rational_center
    (S : Finset ℕ) (denominator : ℕ)
    (numerator shift lift : ℤ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (numerator : ℝ) / denominator -
        (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) + (lift : ℝ) =
      ((numerator *
          ((actualMajorArcLcmResidueModulus S denominator / denominator : ℕ) : ℤ) -
        shift *
          ((actualMajorArcLcmResidueModulus S denominator /
            (∏ p ∈ S, p) : ℕ) : ℤ) +
        lift * (actualMajorArcLcmResidueModulus S denominator : ℤ) : ℤ) : ℝ) /
          (actualMajorArcLcmResidueModulus S denominator : ℝ) := by
  let W : ℕ := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hL : 0 < L := actualMajorArcLcmResidueModulus_pos
    S denominator hdenominator hsupport
  have hWdiv : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  have hWfactor : W * (L / W) = L := Nat.mul_div_cancel' hWdiv
  have hWfactorReal := congrArg (fun k : ℕ => (k : ℝ)) hWfactor
  push_cast at hWfactorReal
  have hWreal : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hfirst := actualMajorArcLcm_rescaled_rational_center
    S denominator numerator hdenominator hsupport
  have hsecond :
      (shift : ℝ) / W =
        ((shift * ((L / W : ℕ) : ℤ) : ℤ) : ℝ) / L := by
    norm_num only [Int.cast_mul, Int.cast_natCast]
    apply (div_eq_div_iff hWreal hLreal).mpr
    rw [← hWfactorReal]
    ring
  have hlift :
      (lift : ℝ) = ((lift * (L : ℤ) : ℤ) : ℝ) / L := by
    norm_num only [Int.cast_mul, Int.cast_natCast]
    field_simp
  change
    (numerator : ℝ) / denominator - (shift : ℝ) / W + (lift : ℝ) =
      ((numerator * ((L / denominator : ℕ) : ℤ) -
          shift * ((L / W : ℕ) : ℤ) + lift * (L : ℤ) : ℤ) : ℝ) / L
  rw [hfirst, hsecond, hlift]
  norm_num only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  ring

/-- Genuine prime-only Siegel--Walfisz/Abel evaluation on EVERY unit cell
of `lcm(q,W)` at ANY integral common-modulus rational numerator, uniformly
for all Farey denominators below the actual logarithmic cutoff.  The
explicit proper-prime-power error is retained. -/
theorem actualMajorArcLcm_prime_filtered_interval_cell_model
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ denominator : ℕ,
          0 < denominator → denominator ≤ compatibleLogMinorCutoff n →
          ∀ lower upper : ℕ,
            1 ≤ lower → lower ≤ upper → upper ≤ n →
            ∀ residue : ℕ,
              residue < actualMajorArcLcmResidueModulus S denominator →
              Nat.Coprime residue
                (actualMajorArcLcmResidueModulus S denominator) →
              ∀ frequency numerator : ℤ, ∀ β : ℝ,
                ‖ternaryExponentialSum
                    (((Finset.Ico lower upper).filter
                      (fun t => t % actualMajorArcLcmResidueModulus
                        S denominator = residue)).filter Nat.Prime)
                    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
                    frequency
                      ((numerator : ℝ) /
                        actualMajorArcLcmResidueModulus S denominator + β) -
                  ternaryMajorArcIntervalModel
                    lower upper (actualMajorArcLcmResidueModulus S denominator)
                    residue frequency numerator β‖ ≤
                  2 * ternaryMajorArcProgressionError c C n frequency β +
                    (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n := by
  obtain ⟨c, C, hc, hC, N₀, hmodel⟩ :=
    ternary_rated_interval_progression_major_arc_model
      (13 : ℝ) (by norm_num)
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards
    [eventually_ge_atTop N₀,
      actualMajorArcLcmResidueModulus_eventually_siegel_walfisz_range
        S hsupport] with n hn hcommon
  intro denominator hdenominator hcutoff lower upper hlowerpositive
    hlower hupper residue hresidue hunit frequency numerator β
  let L := actualMajorArcLcmResidueModulus S denominator
  let window := (Finset.Ico lower upper).filter
    (fun t => t % L = residue)
  let α : ℝ := (numerator : ℝ) / L + β
  let smooth := ternaryMajorArcIntervalModel
    lower upper L residue frequency numerator β
  let full := ternaryExponentialSum window
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
    frequency α
  let prime := ternaryExponentialSum (window.filter Nat.Prime)
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
    frequency α
  have hL : 0 < L := actualMajorArcLcmResidueModulus_pos
    S denominator hdenominator hsupport
  have hsize : (L : ℝ) ≤ Real.log (n : ℝ) ^ (13 : ℝ) := by
    have hbound := hcommon denominator hdenominator hcutoff
    rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    exact hbound
  have hprogression := hmodel n hn lower upper hlower hupper
    L hL hsize residue hresidue
      (show Nat.gcd residue L = 1 from hunit)
      frequency numerator β
  have hfull : ‖full - smooth‖ ≤
      2 * ternaryMajorArcProgressionError c C n frequency β := by
    dsimp [full, smooth, window, α]
    exact hprogression
  have hwindow : window ⊆ Finset.Ioc 0 n := by
    intro k hk
    obtain ⟨hkinterval, _⟩ := Finset.mem_filter.mp hk
    obtain ⟨hklower, hkupper⟩ := Finset.mem_Ico.mp hkinterval
    apply Finset.mem_Ioc.mpr
    exact ⟨by omega, by omega⟩
  have hpowers := ternary_vonMangoldt_prime_filtered_exponential_error
    window n hwindow frequency α
  have hreverse : ‖prime - full‖ ≤
      (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n := by
    rw [norm_sub_rev]
    exact hpowers
  change ‖prime - smooth‖ ≤
    2 * ternaryMajorArcProgressionError c C n frequency β +
      (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n
  calc
    ‖prime - smooth‖ = ‖(prime - full) + (full - smooth)‖ := by
      congr 1
      ring
    _ ≤ ‖prime - full‖ + ‖full - smooth‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- Prime-only rated evaluation at EVERY actual deduplicated shifted major
center `h/q-j/W+k`, preserving its exact integer numerator and the bounded
proper-prime-power error.  No restriction `gcd(q,W)=1` is imposed. -/
theorem actualMajorArcLcm_shifted_prime_filtered_interval_cell_model
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ denominator : ℕ,
          0 < denominator → denominator ≤ compatibleLogMinorCutoff n →
          ∀ lower upper : ℕ,
            1 ≤ lower → lower ≤ upper → upper ≤ n →
            ∀ residue : ℕ,
              residue < actualMajorArcLcmResidueModulus S denominator →
              Nat.Coprime residue
                (actualMajorArcLcmResidueModulus S denominator) →
              ∀ frequency numerator shift lift : ℤ, ∀ β : ℝ,
                ‖ternaryExponentialSum
                    (((Finset.Ico lower upper).filter
                      (fun t => t % actualMajorArcLcmResidueModulus
                        S denominator = residue)).filter Nat.Prime)
                    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
                    frequency
                      ((numerator : ℝ) / denominator -
                        (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
                        (lift : ℝ) + β) -
                  ternaryMajorArcIntervalModel
                    lower upper (actualMajorArcLcmResidueModulus S denominator)
                    residue frequency
                    (numerator *
                        ((actualMajorArcLcmResidueModulus S denominator /
                          denominator : ℕ) : ℤ) -
                      shift *
                        ((actualMajorArcLcmResidueModulus S denominator /
                          (∏ p ∈ S, p) : ℕ) : ℤ) +
                      lift * (actualMajorArcLcmResidueModulus S denominator : ℤ))
                    β‖ ≤
                  2 * ternaryMajorArcProgressionError c C n frequency β +
                    (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n := by
  obtain ⟨c, C, hc, hC, hmodel⟩ :=
    actualMajorArcLcm_prime_filtered_interval_cell_model S hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hmodel] with n hn
  intro denominator hdenominator hcutoff lower upper hlowerpositive
    hlower hupper residue hresidue hunit frequency numerator shift lift β
  let L := actualMajorArcLcmResidueModulus S denominator
  let effective : ℤ := numerator * ((L / denominator : ℕ) : ℤ) -
    shift * ((L / (∏ p ∈ S, p) : ℕ) : ℤ) + lift * (L : ℤ)
  have hpoint := hn denominator hdenominator hcutoff lower upper
    hlowerpositive hlower hupper residue hresidue hunit
      frequency effective β
  have hcenter := actualMajorArcLcm_rescaled_shifted_rational_center
    S denominator numerator shift lift hdenominator hsupport
  change
    ‖ternaryExponentialSum
        (((Finset.Ico lower upper).filter
          (fun t => t % L = residue)).filter Nat.Prime)
        (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        frequency
          ((numerator : ℝ) / denominator -
            (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
            (lift : ℝ) + β) -
      ternaryMajorArcIntervalModel
        lower upper L residue frequency effective β‖ ≤ _
  rw [hcenter]
  exact hpoint

#print axioms Erdos689.actualMajorArcLcm_unit_cell_prime_outside_support
#print axioms Erdos689.actualMajorArcLeftPrime_unit_cell_eq_interval
#print axioms Erdos689.actualMajorArcCenterPrime_unit_cell_eq_interval
#print axioms Erdos689.actualMajorArcLabelPrime_compatible_cell_eq_interval
#print axioms Erdos689.actualMajorArcLcm_rescaled_rational_center
#print axioms Erdos689.actualMajorArcLcm_rescaled_shifted_rational_center
#print axioms Erdos689.actualMajorArcLcm_prime_filtered_interval_cell_model
#print axioms Erdos689.actualMajorArcLcm_shifted_prime_filtered_interval_cell_model

end Erdos689
