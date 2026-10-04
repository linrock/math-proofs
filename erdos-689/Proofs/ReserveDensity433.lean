module

public import PrimeProgressions433

@[expose] public section


/-!
# Exact robust-residue periodicity and unconditional fixed-support prime density

For every fixed positive auxiliary support, the manuscript's robust-residue
predicate is periodic modulo the support product. Summing the already audited
prime number theorem in fixed arithmetic progressions over its exact finite set
of robust unit residues gives the genuine prime-density constant
`card robustResidues / totient W`.

The final theorem also incorporates the actual moving reserve cutoff, proving
its precise additional factor `1 - 1 / (J + 1)`. The switched-set-uniform
Green--Tao estimate, two-form degree bound, remaining scalar surplus, and full
conjecture remain unproved.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The switched auxiliary-hit count depends only on the support-product residue. -/
theorem switchedHits_eq_of_mod_product_eq
    {S : Finset ℕ} {b : ℕ → ℕ} {m m' : ℕ}
    (hmod : m % (∏ s ∈ S, s) = m' % (∏ s ∈ S, s)) :
    switchedHits S b m = switchedHits S b m' := by
  unfold switchedHits
  congr 1
  ext s
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hs, hhit⟩
    refine ⟨hs, ?_⟩
    have hdiv : s ∣ ∏ t ∈ S, t :=
      Finset.dvd_prod_of_mem (fun t : ℕ => t) hs
    have hresidue : m % s = m' % s := by
      calc
        m % s = (m % (∏ t ∈ S, t)) % s :=
          (Nat.mod_mod_of_dvd m hdiv).symm
        _ = (m' % (∏ t ∈ S, t)) % s := by rw [hmod]
        _ = m' % s := Nat.mod_mod_of_dvd m' hdiv
    change b s % s = m % s at hhit
    change b s % s = m' % s
    exact hhit.trans hresidue
  · rintro ⟨hs, hhit⟩
    refine ⟨hs, ?_⟩
    have hdiv : s ∣ ∏ t ∈ S, t :=
      Finset.dvd_prod_of_mem (fun t : ℕ => t) hs
    have hresidue : m % s = m' % s := by
      calc
        m % s = (m % (∏ t ∈ S, t)) % s :=
          (Nat.mod_mod_of_dvd m hdiv).symm
        _ = (m' % (∏ t ∈ S, t)) % s := by rw [hmod]
        _ = m' % s := Nat.mod_mod_of_dvd m' hdiv
    change b s % s = m' % s at hhit
    change b s % s = m % s
    exact hhit.trans hresidue.symm

/-- Robustness itself depends only on the support-product residue. -/
theorem robustResidue_iff_of_mod_product_eq
    {S : Finset ℕ} {b : ℕ → ℕ} {J r r' : ℕ}
    (hmod : r % (∏ s ∈ S, s) = r' % (∏ s ∈ S, s)) :
    robustResidue S b J r ↔ robustResidue S b J r' := by
  let W := ∏ s ∈ S, s
  have hcoprime : Nat.Coprime r W ↔ Nat.Coprime r' W := by
    change Nat.gcd r W = 1 ↔ Nat.gcd r' W = 1
    have hfirst : Nat.gcd r W = Nat.gcd (r % W) W := by
      rw [Nat.gcd_comm r W, Nat.gcd_rec]
    have hsecond : Nat.gcd r' W = Nat.gcd (r' % W) W := by
      rw [Nat.gcd_comm r' W, Nat.gcd_rec]
    rw [hfirst, hsecond]
    change Nat.gcd (r % (∏ s ∈ S, s)) W = 1 ↔
      Nat.gcd (r' % (∏ s ∈ S, s)) W = 1
    rw [hmod]
  constructor
  · rintro ⟨hunit, hhits⟩
    refine ⟨hcoprime.mp hunit, ?_⟩
    intro j hj
    have hproduct : (j * r) % (∏ s ∈ S, s) =
        (j * r') % (∏ s ∈ S, s) := by
      calc
        (j * r) % (∏ s ∈ S, s) =
            (j % (∏ s ∈ S, s) * (r % (∏ s ∈ S, s))) %
              (∏ s ∈ S, s) := Nat.mul_mod j r _
        _ = (j % (∏ s ∈ S, s) * (r' % (∏ s ∈ S, s))) %
              (∏ s ∈ S, s) := by rw [hmod]
        _ = (j * r') % (∏ s ∈ S, s) := (Nat.mul_mod j r' _).symm
    rw [← switchedHits_eq_of_mod_product_eq hproduct]
    exact hhits j hj
  · rintro ⟨hunit, hhits⟩
    refine ⟨hcoprime.mpr hunit, ?_⟩
    intro j hj
    have hproduct : (j * r) % (∏ s ∈ S, s) =
        (j * r') % (∏ s ∈ S, s) := by
      calc
        (j * r) % (∏ s ∈ S, s) =
            (j % (∏ s ∈ S, s) * (r % (∏ s ∈ S, s))) %
              (∏ s ∈ S, s) := Nat.mul_mod j r _
        _ = (j % (∏ s ∈ S, s) * (r' % (∏ s ∈ S, s))) %
              (∏ s ∈ S, s) := by rw [hmod]
        _ = (j * r') % (∏ s ∈ S, s) := (Nat.mul_mod j r' _).symm
    rw [switchedHits_eq_of_mod_product_eq hproduct]
    exact hhits j hj

/-- A robust integer belongs to the exact finite robust-residue classification. -/
theorem mem_robustResidues_mod_iff {S : Finset ℕ}
    {b : ℕ → ℕ} {J p : ℕ}
    (hsupport : ∀ s ∈ S, 0 < s) :
    p % (∏ s ∈ S, s) ∈ robustResidues S b J ↔
      robustResidue S b J p := by
  classical
  have hproduct : 0 < ∏ s ∈ S, s :=
    Finset.prod_pos hsupport
  change p % (∏ s ∈ S, s) ∈
    (Finset.range (∏ s ∈ S, s)).filter (robustResidue S b J) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  have hequiv := robustResidue_iff_of_mod_product_eq
    (S := S) (b := b) (J := J) (r := p) (r' := p % (∏ s ∈ S, s))
    (by simp)
  constructor
  · exact fun h => hequiv.mpr h.2
  · exact fun h => ⟨Nat.mod_lt p hproduct, hequiv.mp h⟩

/-- The genuine primes at most `n` lying in any robust auxiliary residue. -/
noncomputable def robustPrimeTargets (S : Finset ℕ) (b : ℕ → ℕ)
    (J n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun p => p.Prime ∧ robustResidue S b J p

/-- Robust primes split exactly into disjoint fixed reduced progression classes. -/
theorem robustPrimeTargets_card_eq_sum_progressions
    (S : Finset ℕ) (b : ℕ → ℕ) (J n : ℕ)
    (hsupport : ∀ s ∈ S, 0 < s) :
    (robustPrimeTargets S b J n).card =
      ∑ r ∈ robustResidues S b J,
        ((Finset.Icc 1 n).filter fun p =>
          p.Prime ∧ p % (∏ s ∈ S, s) = r % (∏ s ∈ S, s)).card := by
  classical
  let W := ∏ s ∈ S, s
  let R := robustResidues S b J
  let classes : ℕ → Finset ℕ := fun r =>
    (Finset.Icc 1 n).filter fun p => p.Prime ∧ p % W = r % W
  have hunion : robustPrimeTargets S b J n = R.biUnion classes := by
    ext p
    simp only [robustPrimeTargets, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hinterval, hprime, hrobust⟩
      refine ⟨p % W, (mem_robustResidues_mod_iff hsupport).mpr hrobust, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hinterval, hprime, by simp⟩
    · rintro ⟨r, hr, hp⟩
      obtain ⟨hinterval, hprime, hmod⟩ := Finset.mem_filter.mp hp
      have hrobust_r : robustResidue S b J r :=
        (Finset.mem_filter.mp hr).2
      have hrobust_p :=
        (robustResidue_iff_of_mod_product_eq (S := S) (b := b) (J := J)
          hmod).mpr hrobust_r
      exact ⟨hinterval, hprime, hrobust_p⟩
  have hdisjoint : (↑R : Set ℕ).PairwiseDisjoint classes := by
    intro r hr r' hr' hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hfirst := (Finset.mem_filter.mp hp).2.2
    have hsecond := (Finset.mem_filter.mp hp').2.2
    have heq : r % W = r' % W := hfirst.symm.trans hsecond
    have hrlt : r < W :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hr'lt : r' < W :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr').1
    exact hne (by simpa [Nat.mod_eq_of_lt hrlt,
      Nat.mod_eq_of_lt hr'lt] using heq)
  rw [hunion, Finset.card_biUnion hdisjoint]

/-- Fixed-support robust primes have the exact manuscript density `|R|/φ(W)`. -/
theorem robustPrimeTargets_asymptotic
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ s ∈ S, 0 < s) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((robustPrimeTargets S b J n).card : ℝ) /
          ((n : ℝ) / Real.log n))
      Filter.atTop
      (nhds (((robustResidues S b J).card : ℝ) /
        (((∏ s ∈ S, s).totient : ℕ) : ℝ))) := by
  classical
  let W := ∏ s ∈ S, s
  have hpositive : 0 < W := Finset.prod_pos hsupport
  have hsum := tendsto_finsetSum (robustResidues S b J) (fun r hr =>
    prime_number_theorem_arithmetic_progressions W r hpositive
      (Finset.mem_filter.mp hr).2.1)
  convert hsum using 1
  · funext n
    rw [robustPrimeTargets_card_eq_sum_progressions S b J n hsupport]
    simp only [Nat.cast_sum, Finset.sum_div]
    rfl
  · simp [div_eq_mul_inv, W]

/-- Above its explicit finite cutoff, the actual reserve is an exact robust-prime band. -/
theorem canonicalReserve_eq_robustPrimeTargets_sdiff
    (S : Finset ℕ) (b : ℕ → ℕ) (J n : ℕ)
    (hn : 2 * (J + 1) ≤ n) :
    canonicalReserve S b n J =
      robustPrimeTargets S b J n \
        robustPrimeTargets S b J (n / (J + 1)) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hinterval, hprime, _, _, hrobust, hcutoff⟩ :=
      Finset.mem_filter.mp hp
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hinterval, hprime, hrobust⟩, ?_⟩
    intro hlow
    have hlower := (Finset.mem_Icc.mp (Finset.mem_filter.mp hlow).1).2
    have habove : n / (J + 1) < p :=
      (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ J)).mpr (by
        simpa [Nat.mul_comm] using hcutoff)
    omega
  · intro hp
    obtain ⟨htop, hnotlow⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hinterval, hprime, hrobust⟩ := Finset.mem_filter.mp htop
    have habove : n / (J + 1) < p := by
      by_contra hnotabove
      apply hnotlow
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hinterval).1, Nat.le_of_not_gt hnotabove⟩,
        hprime, hrobust⟩
    have hcutoff : n < (J + 1) * p := by
      have h := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ J)).mp habove
      simpa [Nat.mul_comm] using h
    have hnot_support : p ∉ S := by
      intro hsupport
      have hdiv : p ∣ ∏ s ∈ S, s :=
        Finset.dvd_prod_of_mem (fun s : ℕ => s) hsupport
      exact (hprime.coprime_iff_not_dvd.mp hrobust.1) hdiv
    have hnot_two : p ≠ 2 := by
      intro htwo
      subst p
      omega
    exact Finset.mem_filter.mpr
      ⟨hinterval, hprime, hnot_two, hnot_support, hrobust, hcutoff⟩

/-- The canonical protected reserve has the exact robust-prime interval count. -/
theorem canonicalReserve_card_eq_robustPrimeTargets_sub
    (S : Finset ℕ) (b : ℕ → ℕ) (J n : ℕ)
    (hn : 2 * (J + 1) ≤ n) :
    (canonicalReserve S b n J).card =
      (robustPrimeTargets S b J n).card -
        (robustPrimeTargets S b J (n / (J + 1))).card := by
  classical
  have hsubset : robustPrimeTargets S b J (n / (J + 1)) ⊆
      robustPrimeTargets S b J n := by
    intro p hp
    obtain ⟨hinterval, hprime, hrobust⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hinterval).1,
        (Finset.mem_Icc.mp hinterval).2.trans (Nat.div_le_self n (J + 1))⟩,
      hprime, hrobust⟩
  rw [canonicalReserve_eq_robustPrimeTargets_sdiff S b J n hn,
    Finset.card_sdiff_of_subset hsubset]

/-- Division by a fixed positive natural has the expected real scaling limit. -/
theorem nat_div_cast_ratio_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds ((k : ℝ)⁻¹)) := by
  have hnonneg : 0 ≤ (k : ℝ)⁻¹ := by positivity
  have h := (tendsto_nat_floor_mul_div_atTop hnonneg).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext n
  congr 1
  rw [← Nat.floor_div_eq_div (K := ℝ) n k]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- A fixed positive natural cutoff changes logarithms only by lower-order terms. -/
theorem nat_div_log_ratio_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log ((n / k : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (nhds 1) := by
  have hratio := nat_div_cast_ratio_tendsto k hk
  have hinv : (k : ℝ)⁻¹ ≠ 0 := by positivity
  have hlog := hratio.log hinv
  have hden := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero := hlog.div_atTop hden
  have hone : Tendsto
      (fun n : ℕ => Real.log (((n / k : ℕ) : ℝ) / (n : ℝ)) /
        Real.log (n : ℝ) + 1)
      atTop (nhds 1) := by
    simpa using hzero.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply hone.congr'
  filter_upwards [eventually_ge_atTop (max k 2)] with n hn
  have hnk : k ≤ n := (le_max_left k 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right k 2).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqpos : (0 : ℝ) < (n / k : ℕ) := by
    exact_mod_cast Nat.div_pos hnk hk
  have hlogne : Real.log (n : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one hnpos
    exact_mod_cast (by omega : n ≠ 1)
  rw [Real.log_div (ne_of_gt hqpos) (ne_of_gt hnpos)]
  field_simp
  ring

/-- Prime-counting normalization at a fixed integer cutoff scales by its inverse. -/
theorem nat_div_prime_scale_ratio_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        (((n / k : ℕ) : ℝ) / Real.log ((n / k : ℕ) : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds ((k : ℝ)⁻¹)) := by
  have hcast := nat_div_cast_ratio_tendsto k hk
  have hlog := nat_div_log_ratio_tendsto k hk
  have h := hcast.mul (hlog.inv₀ one_ne_zero)
  convert h using 1
  · funext n
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp

/-- Robust prime density at the fixed moving cutoff has its exact scale factor. -/
theorem robustPrimeTargets_scaled_asymptotic
    (S : Finset ℕ) (b : ℕ → ℕ) (J k : ℕ)
    (hsupport : ∀ s ∈ S, 0 < s) (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        ((robustPrimeTargets S b J (n / k)).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop
      (nhds ((((robustResidues S b J).card : ℝ) /
        (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ((k : ℝ)⁻¹))) := by
  have hbase := (robustPrimeTargets_asymptotic S b J hsupport).comp
    (Nat.tendsto_div_const_atTop hk.ne')
  have hscaled := hbase.mul (nat_div_prime_scale_ratio_tendsto k hk)
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (2 * k)] with n hn
  have hqge : 2 ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr hn
  have hqpos : (0 : ℝ) < (n / k : ℕ) := by
    exact_mod_cast (by omega : 0 < n / k)
  have hlogne : Real.log ((n / k : ℕ) : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one hqpos
    exact_mod_cast (by omega : n / k ≠ 1)
  have hscale : (((n / k : ℕ) : ℝ) /
      Real.log ((n / k : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero (ne_of_gt hqpos) hlogne
  change
    (((robustPrimeTargets S b J (n / k)).card : ℝ) /
      (((n / k : ℕ) : ℝ) / Real.log ((n / k : ℕ) : ℝ))) *
        ((((n / k : ℕ) : ℝ) / Real.log ((n / k : ℕ) : ℝ)) /
          ((n : ℝ) / Real.log n)) =
      ((robustPrimeTargets S b J (n / k)).card : ℝ) /
        ((n : ℝ) / Real.log n)
  calc
    _ = ((((robustPrimeTargets S b J (n / k)).card : ℝ) /
      (((n / k : ℕ) : ℝ) / Real.log ((n / k : ℕ) : ℝ))) *
        (((n / k : ℕ) : ℝ) / Real.log ((n / k : ℕ) : ℝ))) /
          ((n : ℝ) / Real.log n) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hscale]

/-- The actual protected reserve has the complete fixed-support density constant. -/
theorem canonicalReserve_asymptotic
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ s ∈ S, 0 < s) :
    Tendsto
      (fun n : ℕ =>
        ((canonicalReserve S b n J).card : ℝ) /
          ((n : ℝ) / Real.log n))
      atTop
      (nhds ((((robustResidues S b J).card : ℝ) /
        (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
          (1 - (((J + 1 : ℕ) : ℝ)⁻¹)))) := by
  classical
  have htop := robustPrimeTargets_asymptotic S b J hsupport
  have hbottom := robustPrimeTargets_scaled_asymptotic
    S b J (J + 1) hsupport (Nat.zero_lt_succ J)
  have hsub := htop.sub hbottom
  have hlimit :
      (((robustResidues S b J).card : ℝ) /
        (((∏ s ∈ S, s).totient : ℕ) : ℝ)) -
          (((robustResidues S b J).card : ℝ) /
            (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
              (((J + 1 : ℕ) : ℝ)⁻¹) =
        (((robustResidues S b J).card : ℝ) /
          (((∏ s ∈ S, s).totient : ℕ) : ℝ)) *
            (1 - (((J + 1 : ℕ) : ℝ)⁻¹)) := by ring
  rw [← hlimit]
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop (2 * (J + 1))] with n hn
  have hsubset : robustPrimeTargets S b J (n / (J + 1)) ⊆
      robustPrimeTargets S b J n := by
    intro p hp
    obtain ⟨hinterval, hprime, hrobust⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hinterval).1,
        (Finset.mem_Icc.mp hinterval).2.trans (Nat.div_le_self n (J + 1))⟩,
      hprime, hrobust⟩
  have hcard := canonicalReserve_card_eq_robustPrimeTargets_sub
    S b J n hn
  have hcast :
      ((canonicalReserve S b n J).card : ℝ) =
        ((robustPrimeTargets S b J n).card : ℝ) -
          ((robustPrimeTargets S b J (n / (J + 1))).card : ℝ) := by
    rw [hcard, Nat.cast_sub (Finset.card_le_card hsubset)]
  rw [hcast, sub_div]

end Erdos689

#print axioms Erdos689.switchedHits_eq_of_mod_product_eq
#print axioms Erdos689.robustResidue_iff_of_mod_product_eq
#print axioms Erdos689.mem_robustResidues_mod_iff
#print axioms Erdos689.robustPrimeTargets_card_eq_sum_progressions
#print axioms Erdos689.robustPrimeTargets_asymptotic
#print axioms Erdos689.canonicalReserve_eq_robustPrimeTargets_sdiff
#print axioms Erdos689.canonicalReserve_card_eq_robustPrimeTargets_sub
#print axioms Erdos689.nat_div_cast_ratio_tendsto
#print axioms Erdos689.nat_div_log_ratio_tendsto
#print axioms Erdos689.nat_div_prime_scale_ratio_tendsto
#print axioms Erdos689.robustPrimeTargets_scaled_asymptotic
#print axioms Erdos689.canonicalReserve_asymptotic
