module

public import RobustSupportDensity
public import GoalRootSparseLimsup433
public import ActualMajorArcFinalCoupling433
public import ErdosProblems.Erdos730.PNTAP
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section


/-!
# The exact unconditional original #1139 limsup is at least one

The existing local theorem gave only `1 / 4`.  Reusing the fully audited
#689 covering theorem and the already kernel-proved prime number theorem,
the new unrestricted-conductor bridge removes the former quadratic CRT
baseline.  The real prime-power conductor satisfies `log Q ~ y`, and hence
the literal historical extended-real limsup is at least `1`.

This remains an unconditional partial result.  The original conjecture asks
for an infinite limsup, which is not proved here.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology Chebyshev

namespace Erdos1139

/-- At modulus one, the already audited arithmetic-progression Chebyshev
function is precisely Mathlib's ordinary Chebyshev theta function. -/
theorem mod_one_prime_progression_eq_chebyshev_theta (x : ℝ) :
    Erdos730.FullDensity.thetaAP 1 0 x = Chebyshev.theta x := by
  unfold Erdos730.FullDensity.thetaAP
  rw [Chebyshev.theta_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.mod_one, if_pos rfl]

/-- The actual logarithm of the exact selected primorial conductor has
leading coefficient one, by the previously kernel-proved prime number
theorem in arithmetic progressions specialized to modulus one. -/
theorem original_primorial_log_div_length_tendsto_one :
    Tendsto (fun y : ℕ => Real.log (primorial y : ℝ) / (y : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hpnt := Erdos730.FullDensity.thetaAP_div_id_tendsto
    (A := 1) (a := 0) (by norm_num) (by norm_num) (by norm_num)
  have hnat := hpnt.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hnat using 1
  · funext y
    simp [Function.comp_apply, mod_one_prime_progression_eq_chebyshev_theta,
      Chebyshev.theta_eq_log_primorial]
  · norm_num [Nat.totient_one]

/-- Every fixed normalized coefficient below one is eventually valid for
the actual unrestricted CRT location, including its exact successor. -/
theorem eventually_original_primorial_crt_cost
    (c : ℝ) (hc : 0 < c) (hc' : c < 1) :
    ∀ᶠ y : ℕ in atTop,
      c * Real.log (((2 * primorial y + 1 : ℕ) : ℝ)) ≤ (y : ℝ) := by
  let δ : ℝ := (1 - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hneighborhood : Set.Iio (1 + δ) ∈ 𝓝 (1 : ℝ) :=
    Iio_mem_nhds (by linarith)
  have hpnt : ∀ᶠ y : ℕ in atTop,
      Real.log (primorial y : ℝ) / (y : ℝ) < 1 + δ :=
    original_primorial_log_div_length_tendsto_one.eventually hneighborhood
  obtain ⟨B, hB⟩ := exists_nat_ge (Real.log (3 : ℝ) / δ)
  filter_upwards [hpnt, eventually_ge_atTop (max 1 B)] with y hratio hy
  have hypositive : 0 < (y : ℝ) := by
    have hyone : 1 ≤ y := le_trans (Nat.le_max_left 1 B) hy
    exact_mod_cast hyone
  have hcore : Real.log (primorial y : ℝ) < (1 + δ) * (y : ℝ) := by
    have h := (div_lt_iff₀ hypositive).mp hratio
    nlinarith
  have hyB : B ≤ y := le_trans (Nat.le_max_right 1 B) hy
  have hfixed : Real.log (3 : ℝ) ≤ δ * (y : ℝ) := by
    have hquotient : Real.log (3 : ℝ) / δ ≤ (y : ℝ) :=
      hB.trans (by exact_mod_cast hyB)
    have h := (div_le_iff₀ hδ).mp hquotient
    nlinarith
  have hQnat : 0 < primorial y := primorial_pos y
  have hQ : 0 < (primorial y : ℝ) := by exact_mod_cast hQnat
  have hargpositive : 0 < (((2 * primorial y + 1 : ℕ) : ℝ)) := by
    positivity
  have hthreepositive : 0 < (3 : ℝ) * (primorial y : ℝ) := by
    positivity
  have hargbound :
      (((2 * primorial y + 1 : ℕ) : ℝ)) ≤
        (3 : ℝ) * (primorial y : ℝ) := by
    have hnat : 2 * primorial y + 1 ≤ 3 * primorial y := by omega
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log.monotoneOn
    hargpositive hthreepositive hargbound
  rw [Real.log_mul (by norm_num) (ne_of_gt hQ)] at hlog
  have hsum :
      Real.log (3 : ℝ) + Real.log (primorial y : ℝ) ≤
        (2 - c) * (y : ℝ) := by
    dsimp [δ] at hfixed hcore
    nlinarith
  have hcoefficient : c * (2 - c) ≤ 1 := by
    nlinarith [sq_nonneg (1 - c)]
  calc
    c * Real.log (((2 * primorial y + 1 : ℕ) : ℝ)) ≤
        c * (Real.log (3 : ℝ) + Real.log (primorial y : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog hc.le
    _ ≤ c * ((2 - c) * (y : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hc.le
    _ = (c * (2 - c)) * (y : ℝ) := by ring
    _ ≤ 1 * (y : ℝ) :=
      mul_le_mul_of_nonneg_right hcoefficient hypositive.le
    _ = (y : ℝ) := by ring

/-- A genuine full #689 prime-only double cover is an unrestricted mixed
cover with no prime-square labels.  No artificial bound on the CRT shift
or additional prime-pattern hypothesis is introduced. -/
theorem unrestricted_empty_square_cover_of_original_prime_cover
    {y : ℕ} {a : ℕ → ℕ}
    (hcover : ∀ h ∈ Finset.Icc 1 y,
      2 ≤ ((Finset.Icc 1 y).filter
        fun p => p.Prime ∧ a p ≡ h [MOD p]).card) :
    UnrestrictedPrimeSquareDoubleCover y
      ((Finset.Icc 1 y).filter Nat.Prime) ∅ a := by
  have hprime := prime_double_cover_of_full_prime_cover hcover
  refine ⟨fun p hp => (hprime.1 p hp).1, Finset.empty_subset _, ?_⟩
  intro h hh
  simpa using hprime.2 h hh

/-- The already proved original #689 covering gives actual original #1139
sequence gaps at location at most TWICE the exact primorial conductor.
This removes the earlier additive quadratic CRT baseline entirely. -/
theorem eventual_original_sequence_gaps_at_twice_primorial :
    ∀ᶠ y : ℕ in atTop,
      ∃ N k : ℕ,
        primorial y < N ∧ N ≤ 2 * primorial y ∧
        k ≤ N ∧ Nat.nth AlmostPrime k ≤ N ∧
        N + y < Nat.nth AlmostPrime (k + 1) ∧
        y < Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k := by
  filter_upwards [Erdos689.officialStatement_unconditional] with y hy
  obtain ⟨a, ha⟩ := hy
  have hcover := unrestricted_empty_square_cover_of_original_prime_cover ha
  have hconductor :
      (∏ p ∈ ((Finset.Icc 1 y).filter Nat.Prime),
        selectedPrimePower ∅ p) = primorial y := by
    simpa [selectedPrimePower, selectedPrimeExponent] using
      closed_prime_product_eq_primorial y
  simpa [hconductor] using
    unrestricted_square_double_cover_forces_original_sequence_gap hcover

/-- Axiom-audited UNCONDITIONAL fourfold improvement of the previous local
`1 / 4` bound: the exact upstream original extended-real limsup is at least
one.  The infinite-limsup Erdős problem itself remains open. -/
theorem original_normalized_limsup_ge_one :
    (1 : EReal) ≤
      Filter.atTop.limsup
        (fun k : ℕ =>
          (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
             (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
            Real.log ((k : ℝ) + 1) : EReal)) := by
  change
    (1 : EReal) ≤
      Filter.atTop.limsup
        (fun k : ℕ =>
          (((Nat.nth AlmostPrime (k + 1) : ℝ) -
             (Nat.nth AlmostPrime k : ℝ)) /
            Real.log ((k : ℝ) + 1) : EReal))
  apply (le_limsup_iff).2
  intro b hb
  obtain ⟨a, hba, ha⟩ := EReal.exists_between_coe_real hb
  have haone : a < (1 : ℝ) :=
    EReal.coe_lt_coe_iff.mp (by simpa using ha)
  let c : ℝ := max a (1 / 2)
  have hcpositive : 0 < c :=
    lt_of_lt_of_le (by norm_num) (le_max_right a (1 / 2))
  have hcone : c < 1 := max_lt haone (by norm_num)
  have hac : a ≤ c := le_max_left a (1 / 2)
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventual_original_sequence_gaps_at_twice_primorial.and
      (eventually_original_primorial_crt_cost c hcpositive hcone))
  apply Filter.frequently_atTop.mpr
  intro K
  let y := threshold + Nat.nth AlmostPrime (K + 2) + 1
  have hythreshold : threshold ≤ y := by dsimp [y]; omega
  obtain ⟨⟨N, k, _hlower, hupper, hkN, _hprevious, _hnext, hgap⟩,
    hcost⟩ := hthreshold y hythreshold
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
  have hkinitial : K ≤ k := by omega
  refine ⟨k, hkinitial, ?_⟩
  have hlocation : k + 1 ≤ 2 * primorial y + 1 := by omega
  have hcast : (k : ℝ) + 1 ≤ (((2 * primorial y + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hlocation
  have hsmallpositive : 0 < (k : ℝ) + 1 := by positivity
  have hlargepositive : 0 < (((2 * primorial y + 1 : ℕ) : ℝ)) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hsmallpositive hlargepositive hcast
  have hscaled : c * Real.log ((k : ℝ) + 1) ≤ (y : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog hcpositive.le).trans hcost
  have hdenominator : 0 < Real.log ((k : ℝ) + 1) := by
    apply Real.log_pos
    have hsuccessor : 1 < k + 1 := by omega
    exact_mod_cast hsuccessor
  have hmonotone : Nat.nth AlmostPrime k ≤ Nat.nth AlmostPrime (k + 1) :=
    (Nat.nth_monotone almostPrime_infinite) (by omega)
  have hgapreal :
      (y : ℝ) < (Nat.nth AlmostPrime (k + 1) : ℝ) -
        (Nat.nth AlmostPrime k : ℝ) := by
    have hcastgap : (y : ℝ) <
        (Nat.nth AlmostPrime (k + 1) - Nat.nth AlmostPrime k : ℕ) := by
      exact_mod_cast hgap
    simpa [Nat.cast_sub hmonotone] using hcastgap
  have hratio :
      c <
        ((Nat.nth AlmostPrime (k + 1) : ℝ) -
          (Nat.nth AlmostPrime k : ℝ)) /
            Real.log ((k : ℝ) + 1) :=
    (lt_div_iff₀ hdenominator).mpr (hscaled.trans_lt hgapreal)
  exact hba.trans (EReal.coe_lt_coe_iff.mpr (hac.trans_lt hratio))


end Erdos1139
