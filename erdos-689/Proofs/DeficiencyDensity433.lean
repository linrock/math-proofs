import ReserveDensity433
import ManuscriptLocal

/-!
# Fixed smooth-core strata inside the actual initial deficiency

Fix a divisor `d` of the switched support product and a reduced residue `r`
for which `switchedHits S b (2 * d * r) = 0`. Prime values in that residue
up to `n / (2 * d)` produce distinct genuine targets `2 * d * p` in the
official closed interval. Every such target is initially deficient, so their
number is bounded by the actual `deficiency n (initialAssignment S b)`.

The exact density of this nonvacuous fixed stratum is
`1 / (φ(W) * (2 * d))`, by the already audited fixed-progression PNT and the
actual natural-floor/logarithmic cutoff lemmas. This proves each fixed smooth
core contribution without assuming the still-open infinite-core interchange,
exceptional-target bounds, or full initial-deficiency asymptotic.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The genuine prime parameter values in one fixed smooth-core residue stratum. -/
noncomputable def fixedDeficiencyPrimeStratum
    (S : Finset ℕ) (d r n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (n / (2 * d))).filter fun p =>
    p.Prime ∧ p % (∏ s ∈ S, s) = r % (∏ s ∈ S, s)

/-- All prime parameters in a missed residue keep the actual target missed. -/
theorem fixedDeficiencyPrimeStratum_switchedHits_zero
    {S : Finset ℕ} {b : ℕ → ℕ} {d r n p : ℕ}
    (hp : p ∈ fixedDeficiencyPrimeStratum S d r n)
    (hmiss : switchedHits S b (2 * d * r) = 0) :
    switchedHits S b (2 * d * p) = 0 := by
  have hresidue := (Finset.mem_filter.mp hp).2.2
  have hproduct : (2 * d * p) % (∏ s ∈ S, s) =
      (2 * d * r) % (∏ s ∈ S, s) := by
    calc
      (2 * d * p) % (∏ s ∈ S, s) =
          ((2 * d) % (∏ s ∈ S, s) *
            (p % (∏ s ∈ S, s))) % (∏ s ∈ S, s) :=
        Nat.mul_mod (2 * d) p _
      _ = ((2 * d) % (∏ s ∈ S, s) *
            (r % (∏ s ∈ S, s))) % (∏ s ∈ S, s) := by rw [hresidue]
      _ = (2 * d * r) % (∏ s ∈ S, s) :=
        (Nat.mul_mod (2 * d) r _).symm
  rw [switchedHits_eq_of_mod_product_eq hproduct, hmiss]

/-- A reduced fixed stratum contains no prime from the switched support. -/
theorem fixedDeficiencyPrimeStratum_not_mem_support
    {S : Finset ℕ} {d r n p : ℕ}
    (hcoprime : Nat.Coprime r (∏ s ∈ S, s))
    (hp : p ∈ fixedDeficiencyPrimeStratum S d r n) :
    p ∉ S := by
  let W := ∏ s ∈ S, s
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hresidue := (Finset.mem_filter.mp hp).2.2
  have hcoprime_p : Nat.Coprime p W := by
    change Nat.gcd p W = 1
    have hfirst : Nat.gcd p W = Nat.gcd (p % W) W := by
      rw [Nat.gcd_comm p W, Nat.gcd_rec]
    have hsecond : Nat.gcd r W = Nat.gcd (r % W) W := by
      rw [Nat.gcd_comm r W, Nat.gcd_rec]
    rw [hfirst, hresidue, ← hsecond]
    exact hcoprime
  intro hmem
  have hdiv : p ∣ W := Finset.dvd_prod_of_mem (fun s : ℕ => s) hmem
  exact (hprime.coprime_iff_not_dvd.mp hcoprime_p) hdiv

/-- Every member of the fixed prime stratum is an actual initially deficient target. -/
theorem fixedDeficiencyPrimeStratum_initially_deficient
    {S : Finset ℕ} {b : ℕ → ℕ} {d r n p : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hd : d ∣ ∏ s ∈ S, s)
    (hmiss : switchedHits S b (2 * d * r) = 0)
    (hp : p ∈ fixedDeficiencyPrimeStratum S d r n) :
    coverage n (initialAssignment S b) (2 * d * p) ≤ 1 := by
  have hprime := (Finset.mem_filter.mp hp).2.1
  exact initialAssignment_even_smooth_prime_coverage hsupport hd hprime
    (fixedDeficiencyPrimeStratum_switchedHits_zero hp hmiss)

/-- Distinct fixed-stratum primes inject into the genuine initial deficiency ledger. -/
theorem fixedDeficiencyPrimeStratum_card_le_initial_deficiency
    (S : Finset ℕ) (b : ℕ → ℕ) (d r n : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdpos : 0 < d)
    (hd : d ∣ ∏ s ∈ S, s)
    (hmiss : switchedHits S b (2 * d * r) = 0) :
    (fixedDeficiencyPrimeStratum S d r n).card ≤
      deficiency n (initialAssignment S b) := by
  classical
  have hcoeff : 0 < 2 * d := Nat.mul_pos (by norm_num) hdpos
  let embedding : ℕ ↪ ℕ :=
    ⟨fun p => 2 * d * p, fun p q heq => Nat.mul_left_cancel hcoeff heq⟩
  let targets := (fixedDeficiencyPrimeStratum S d r n).map embedding
  have hsubset : targets ⊆ Finset.Icc 1 n := by
    intro m hm
    obtain ⟨p, hp, heq⟩ := Finset.mem_map.mp hm
    subst m
    have hinterval := (Finset.mem_filter.mp hp).1
    have hp_pos := (Finset.mem_Icc.mp hinterval).1
    have hp_bound := (Finset.mem_Icc.mp hinterval).2
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr
        (ne_of_gt (Nat.mul_pos hcoeff (by omega)))
    · have hbound := (Nat.le_div_iff_mul_le hcoeff).mp hp_bound
      change 2 * d * p ≤ n
      simpa [Nat.mul_comm] using hbound
  calc
    (fixedDeficiencyPrimeStratum S d r n).card = targets.card :=
      (Finset.card_map embedding).symm
    _ = ∑ m ∈ targets, 1 := Finset.card_eq_sum_ones targets
    _ ≤ ∑ m ∈ targets,
        (2 - coverage n (initialAssignment S b) m) := by
          apply Finset.sum_le_sum
          intro m hm
          obtain ⟨p, hp, heq⟩ := Finset.mem_map.mp hm
          subst m
          have hdef := fixedDeficiencyPrimeStratum_initially_deficient
            hsupport hd hmiss hp
          change 1 ≤ 2 - coverage n (initialAssignment S b) (2 * d * p)
          omega
    _ ≤ ∑ m ∈ Finset.Icc 1 n,
        (2 - coverage n (initialAssignment S b) m) :=
          Finset.sum_le_sum_of_subset hsubset
    _ = deficiency n (initialAssignment S b) := rfl

/-- Each genuine fixed smooth-core stratum has its exact progression-PNT density. -/
theorem fixedDeficiencyPrimeStratum_asymptotic
    (S : Finset ℕ) (d r : ℕ)
    (hsupport : ∀ s ∈ S, 0 < s)
    (hdpos : 0 < d)
    (hcoprime : Nat.Coprime r (∏ s ∈ S, s)) :
    Tendsto
      (fun n : ℕ =>
        ((fixedDeficiencyPrimeStratum S d r n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop
      (nhds ((1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
        (((2 * d : ℕ) : ℝ)⁻¹))) := by
  let W := ∏ s ∈ S, s
  have hW : 0 < W := Finset.prod_pos hsupport
  have hcoeff : 0 < 2 * d := Nat.mul_pos (by norm_num) hdpos
  have hbase :=
    (prime_number_theorem_arithmetic_progressions W r hW hcoprime).comp
      (Nat.tendsto_div_const_atTop hcoeff.ne')
  have hscaled := hbase.mul (nat_div_prime_scale_ratio_tendsto (2 * d) hcoeff)
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (2 * (2 * d))] with n hn
  have hqge : 2 ≤ n / (2 * d) :=
    (Nat.le_div_iff_mul_le hcoeff).mpr hn
  have hqpos : (0 : ℝ) < (n / (2 * d) : ℕ) := by
    exact_mod_cast (by omega : 0 < n / (2 * d))
  have hlogne : Real.log ((n / (2 * d) : ℕ) : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one hqpos
    exact_mod_cast (by omega : n / (2 * d) ≠ 1)
  have hscale : (((n / (2 * d) : ℕ) : ℝ) /
      Real.log ((n / (2 * d) : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero (ne_of_gt hqpos) hlogne
  change
    ((((Finset.Icc 1 (n / (2 * d))).filter fun p =>
        p.Prime ∧ p % W = r % W).card : ℝ) /
      (((n / (2 * d) : ℕ) : ℝ) /
        Real.log ((n / (2 * d) : ℕ) : ℝ))) *
      ((((n / (2 * d) : ℕ) : ℝ) /
        Real.log ((n / (2 * d) : ℕ) : ℝ)) /
        ((n : ℝ) / Real.log n)) =
      ((fixedDeficiencyPrimeStratum S d r n).card : ℝ) /
        ((n : ℝ) / Real.log n)
  unfold fixedDeficiencyPrimeStratum
  change
    ((((Finset.Icc 1 (n / (2 * d))).filter fun p =>
        p.Prime ∧ p % W = r % W).card : ℝ) /
      (((n / (2 * d) : ℕ) : ℝ) /
        Real.log ((n / (2 * d) : ℕ) : ℝ))) *
      ((((n / (2 * d) : ℕ) : ℝ) /
        Real.log ((n / (2 * d) : ℕ) : ℝ)) /
        ((n : ℝ) / Real.log n)) =
      ((((Finset.Icc 1 (n / (2 * d))).filter fun p =>
        p.Prime ∧ p % W = r % W).card : ℝ)) /
        ((n : ℝ) / Real.log n)
  field_simp

/-- Every missed reduced smooth-core residue gives an actual asymptotic demand lower bound. -/
theorem initial_deficiency_eventual_lower_bound_of_fixed_stratum
    (S : Finset ℕ) (b : ℕ → ℕ) (d r : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdpos : 0 < d)
    (hd : d ∣ ∏ s ∈ S, s)
    (hcoprime : Nat.Coprime r (∏ s ∈ S, s))
    (hmiss : switchedHits S b (2 * d * r) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
        (((2 * d : ℕ) : ℝ)⁻¹) - ε ≤
        ((deficiency n (initialAssignment S b) : ℕ) : ℝ) /
          ((n : ℝ) / Real.log n) := by
  have hasymptotic := fixedDeficiencyPrimeStratum_asymptotic S d r
    (fun s hs => (hsupport s hs).pos) hdpos hcoprime
  have hbelow : ∀ᶠ n : ℕ in atTop,
      (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
        (((2 * d : ℕ) : ℝ)⁻¹) - ε <
        ((fixedDeficiencyPrimeStratum S d r n).card : ℝ) /
          ((n : ℝ) / Real.log n) :=
    (tendsto_order.mp hasymptotic).1 _ (sub_lt_self _ hε)
  filter_upwards [hbelow, eventually_ge_atTop 2] with n hn_lower hn
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 1 < n)
  have hden : 0 < (n : ℝ) / Real.log n :=
    div_pos (by exact_mod_cast (by omega : 0 < n)) (Real.log_pos hn_real)
  have hcard := fixedDeficiencyPrimeStratum_card_le_initial_deficiency
    S b d r n hsupport hdpos hd hmiss
  have hcard_real :
      ((fixedDeficiencyPrimeStratum S d r n).card : ℝ) ≤
        (deficiency n (initialAssignment S b) : ℝ) := by
    exact_mod_cast hcard
  exact (le_of_lt hn_lower).trans
    ((div_le_div_iff_of_pos_right hden).mpr hcard_real)

#print axioms fixedDeficiencyPrimeStratum_switchedHits_zero
#print axioms fixedDeficiencyPrimeStratum_not_mem_support
#print axioms fixedDeficiencyPrimeStratum_initially_deficient
#print axioms fixedDeficiencyPrimeStratum_card_le_initial_deficiency
#print axioms fixedDeficiencyPrimeStratum_asymptotic
#print axioms initial_deficiency_eventual_lower_bound_of_fixed_stratum

end Erdos689
