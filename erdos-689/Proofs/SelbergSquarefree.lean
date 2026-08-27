import Mathlib

/-!
# The exact squarefree two-root Selberg denominator

The manuscript's moving exceptional prime cannot be absorbed into an
asymptotic whose modulus is fixed.  Its required finite identity instead
splits the *actual squarefree two-root denominator* into terms divisible by
that prime and terms coprime to it.  All definitions below use genuine
squarefree natural numbers and the exact prime weight `2 / (p - 2)`.
-/

open Finset

namespace Erdos689

/-- The genuine dimension-two Selberg factor on a squarefree integer. -/
noncomputable def twoRootSelbergWeight (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (2 : ℝ) / ((p : ℝ) - 2)

/-- The exact squarefree denominator with all primes dividing `M` excluded. -/
noncomputable def twoRootSelbergDenominator (M z : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ (Finset.Icc 1 z).filter
    (fun d => Squarefree d ∧ Nat.Coprime d M), twoRootSelbergWeight d

/-- The dimension-two weight of one prime is exactly its sieve local factor. -/
theorem twoRootSelbergWeight_prime {q : ℕ} (hq : q.Prime) :
    twoRootSelbergWeight q = (2 : ℝ) / ((q : ℝ) - 2) := by
  simp [twoRootSelbergWeight, hq.primeFactors]

/-- The true squarefree sieve weight is multiplicative on coprime factors. -/
theorem twoRootSelbergWeight_mul_of_coprime {a b : ℕ}
    (hab : Nat.Coprime a b) :
    twoRootSelbergWeight (a * b) =
      twoRootSelbergWeight a * twoRootSelbergWeight b := by
  unfold twoRootSelbergWeight
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

/-- Excluding divisibility by a prime is exactly enlarging the excluded modulus. -/
theorem squarefree_coprime_filter_exclude_prime (M q z : ℕ)
    (hq : q.Prime) :
    (((Finset.Icc 1 z).filter
      (fun d => Squarefree d ∧ Nat.Coprime d M)).filter
        (fun d => ¬ q ∣ d)) =
      (Finset.Icc 1 z).filter
        (fun d => Squarefree d ∧ Nat.Coprime d (M * q)) := by
  classical
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hd, hsquare, hM⟩, hqnot⟩
    exact ⟨hd, hsquare, Nat.coprime_mul_iff_right.mpr
      ⟨hM, (hq.coprime_iff_not_dvd.mpr hqnot).symm⟩⟩
  · rintro ⟨hd, hsquare, hMq⟩
    obtain ⟨hM, hqcop⟩ := Nat.coprime_mul_iff_right.mp hMq
    exact ⟨⟨hd, hsquare, hM⟩,
      hq.coprime_iff_not_dvd.mp hqcop.symm⟩

/-- The squarefree terms divisible by an outside prime are indexed exactly by
the smaller cutoff `z / q`; squarefreeness forces the remaining factor to be
coprime to `q`. -/
theorem twoRootSelbergDenominator_prime_dvd_part (M q z : ℕ)
    (hq : q.Prime) (hqM : Nat.Coprime q M) :
    (∑ d ∈ (((Finset.Icc 1 z).filter
      (fun d => Squarefree d ∧ Nat.Coprime d M)).filter (fun d => q ∣ d)),
        twoRootSelbergWeight d) =
      twoRootSelbergWeight q * twoRootSelbergDenominator (M * q) (z / q) := by
  classical
  unfold twoRootSelbergDenominator
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun k _ => q * k)
  · intro k hk
    obtain ⟨hkinterval, hksquare, hkMq⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkM, hkq⟩ := Nat.coprime_mul_iff_right.mp hkMq
    have hqk : Nat.Coprime q k := hkq.symm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, dvd_mul_right q k⟩
    · apply Finset.mem_Icc.mpr
      refine ⟨Nat.mul_pos hq.pos (Finset.mem_Icc.mp hkinterval).1, ?_⟩
      have hbound := (Nat.le_div_iff_mul_le hq.pos).mp
        (Finset.mem_Icc.mp hkinterval).2
      simpa [Nat.mul_comm] using hbound
    · exact Nat.squarefree_mul_iff.mpr ⟨hqk, hq.squarefree, hksquare⟩
    · exact hqM.mul_left hkM
  · intro k₁ hk₁ k₂ hk₂ heq
    exact Nat.eq_of_mul_eq_mul_left hq.pos heq
  · intro d hd
    obtain ⟨hdbase, hqd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdinterval, hdsquare, hdM⟩ := Finset.mem_filter.mp hdbase
    have hfactor : q * (d / q) = d := by
      simpa [Nat.mul_comm] using Nat.div_mul_cancel hqd
    have hsquarefactor : Squarefree (q * (d / q)) := by
      simpa [hfactor] using hdsquare
    obtain ⟨hqcop, hqsquare, hquotientsquare⟩ :=
      Nat.squarefree_mul_iff.mp hsquarefactor
    have hquotientM : Nat.Coprime (d / q) M := by
      have hproductM : Nat.Coprime (q * (d / q)) M := by
        simpa [hfactor] using hdM
      exact (Nat.coprime_mul_iff_left.mp hproductM).2
    refine ⟨d / q, Finset.mem_filter.mpr ⟨?_, hquotientsquare, ?_⟩,
      hfactor⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · have hdpos := (Finset.mem_Icc.mp hdinterval).1
        by_contra hnonpos
        have hzero : d / q = 0 :=
          Nat.lt_one_iff.mp (Nat.lt_of_not_ge hnonpos)
        simp [hzero] at hfactor
        omega
      · exact Nat.div_le_div_right (Finset.mem_Icc.mp hdinterval).2
    · exact Nat.coprime_mul_iff_right.mpr ⟨hquotientM, hqcop.symm⟩
  · intro k hk
    obtain ⟨hkinterval, hksquare, hkMq⟩ := Finset.mem_filter.mp hk
    have hqk : Nat.Coprime q k :=
      (Nat.coprime_mul_iff_right.mp hkMq).2.symm
    exact (twoRootSelbergWeight_mul_of_coprime hqk).symm

/-- Exact manuscript identity, valid for every cutoff and every outside
prime, including primes larger than the cutoff or varying with it. -/
theorem twoRootSelbergDenominator_exclude_prime (M q z : ℕ)
    (hq : q.Prime) (hqM : Nat.Coprime q M) :
    twoRootSelbergDenominator M z =
      twoRootSelbergDenominator (M * q) z +
        ((2 : ℝ) / ((q : ℝ) - 2)) *
          twoRootSelbergDenominator (M * q) (z / q) := by
  classical
  let T := (Finset.Icc 1 z).filter
    (fun d => Squarefree d ∧ Nat.Coprime d M)
  calc
    twoRootSelbergDenominator M z =
        (∑ d ∈ T.filter (fun d => ¬ q ∣ d), twoRootSelbergWeight d) +
          ∑ d ∈ T.filter (fun d => q ∣ d), twoRootSelbergWeight d := by
            unfold twoRootSelbergDenominator
            exact (Finset.sum_filter_not_add_sum_filter T
              (fun d => q ∣ d) twoRootSelbergWeight).symm
    _ = twoRootSelbergDenominator (M * q) z +
          twoRootSelbergWeight q *
            twoRootSelbergDenominator (M * q) (z / q) := by
            unfold T
            rw [squarefree_coprime_filter_exclude_prime M q z hq]
            congr 1
            exact twoRootSelbergDenominator_prime_dvd_part M q z hq hqM
    _ = _ := by rw [twoRootSelbergWeight_prime hq]

/-- When the excluded modulus is even, every genuine sieve factor is positive;
this rules out the singular local prime two instead of assigning it a fake
finite weight. -/
theorem twoRootSelbergWeight_pos_of_coprime_even {M d : ℕ}
    (hM : 2 ∣ M) (hd : Nat.Coprime d M) :
    0 < twoRootSelbergWeight d := by
  unfold twoRootSelbergWeight
  apply Finset.prod_pos
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hd2 : Nat.Coprime d 2 := Nat.Coprime.coprime_dvd_right hM hd
  have hnot2 : ¬ 2 ∣ d :=
    Nat.prime_two.coprime_iff_not_dvd.mp hd2.symm
  have hpne : p ≠ 2 := by
    intro heq
    apply hnot2
    simpa [heq] using hpd
  have hplt : 2 < p := by
    have hple := hpprime.two_le
    omega
  apply div_pos (by norm_num)
  exact sub_pos.mpr (by exact_mod_cast hplt)

/-- The exact denominator is nonnegative whenever its singular prime is
excluded. -/
theorem twoRootSelbergDenominator_nonneg {M : ℕ} (hM : 2 ∣ M)
    (z : ℕ) :
    0 ≤ twoRootSelbergDenominator M z := by
  classical
  unfold twoRootSelbergDenominator
  apply Finset.sum_nonneg
  intro d hd
  exact (twoRootSelbergWeight_pos_of_coprime_even hM
    (Finset.mem_filter.mp hd).2.2).le

/-- Every nonempty cutoff contains its positive squarefree unit term. -/
theorem twoRootSelbergDenominator_pos {M z : ℕ} (hM : 2 ∣ M)
    (hz : 1 ≤ z) :
    0 < twoRootSelbergDenominator M z := by
  classical
  unfold twoRootSelbergDenominator
  apply Finset.sum_pos
  · intro d hd
    exact twoRootSelbergWeight_pos_of_coprime_even hM
      (Finset.mem_filter.mp hd).2.2
  · refine ⟨1, Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hz⟩
    · exact IsUnit.squarefree (isUnit_one : IsUnit (1 : ℕ))
    · exact Nat.coprime_one_left M

/-- Increasing the finite cutoff never decreases a genuine even-modulus
squarefree denominator. -/
theorem twoRootSelbergDenominator_mono {M z z' : ℕ}
    (hM : 2 ∣ M) (hzz' : z ≤ z') :
    twoRootSelbergDenominator M z ≤ twoRootSelbergDenominator M z' := by
  classical
  unfold twoRootSelbergDenominator
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdinterval, hdsquare, hdM⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hdinterval).1,
        (Finset.mem_Icc.mp hdinterval).2.trans hzz'⟩, hdsquare, hdM⟩
  · intro d hd hnot
    exact (twoRootSelbergWeight_pos_of_coprime_even hM
      (Finset.mem_filter.mp hd).2.2).le

/-- The exact manuscript `5/3` comparison is completely uniform in the moving
outside prime, with no asymptotic in a growing modulus. -/
theorem twoRootSelbergDenominator_exclude_prime_uniform (M q z : ℕ)
    (hM : 2 ∣ M) (hq : q.Prime) (hqM : Nat.Coprime q M)
    (hqfive : 5 ≤ q) :
    twoRootSelbergDenominator M z ≤
      (5 / 3 : ℝ) * twoRootSelbergDenominator (M * q) z := by
  have hMeven : 2 ∣ M * q := dvd_mul_of_dvd_left hM q
  have hsmall := twoRootSelbergDenominator_mono hMeven
    (Nat.div_le_self z q)
  have hnonneg := twoRootSelbergDenominator_nonneg hMeven z
  have hfactor_nonneg : 0 ≤ (2 : ℝ) / ((q : ℝ) - 2) := by
    apply div_nonneg (by norm_num)
    have hqreal : (5 : ℝ) ≤ q := by exact_mod_cast hqfive
    linarith
  have hfactor_le : (2 : ℝ) / ((q : ℝ) - 2) ≤ 2 / 3 := by
    have hqreal : (5 : ℝ) ≤ q := by exact_mod_cast hqfive
    have hdenom : 0 < (q : ℝ) - 2 := by linarith
    apply (div_le_iff₀ hdenom).mpr
    norm_num
    linarith
  rw [twoRootSelbergDenominator_exclude_prime M q z hq hqM]
  have hfirst := mul_le_mul_of_nonneg_left hsmall hfactor_nonneg
  have hsecond := mul_le_mul_of_nonneg_right hfactor_le hnonneg
  nlinarith

/-- Equivalently, deleting any moving outside prime retains at least three
fifths of the entire fixed-modulus squarefree denominator. -/
theorem twoRootSelbergDenominator_exclude_prime_lower (M q z : ℕ)
    (hM : 2 ∣ M) (hq : q.Prime) (hqM : Nat.Coprime q M)
    (hqfive : 5 ≤ q) :
    (3 / 5 : ℝ) * twoRootSelbergDenominator M z ≤
      twoRootSelbergDenominator (M * q) z := by
  have h := twoRootSelbergDenominator_exclude_prime_uniform M q z
    hM hq hqM hqfive
  linarith

/-- A prime strictly above the sieve cutoff deletes no denominator term at
all; the same identity therefore covers both moving-prime regimes. -/
theorem twoRootSelbergDenominator_exclude_prime_above_cutoff (M q z : ℕ)
    (hq : q.Prime) (hqM : Nat.Coprime q M) (hzq : z < q) :
    twoRootSelbergDenominator M z =
      twoRootSelbergDenominator (M * q) z := by
  rw [twoRootSelbergDenominator_exclude_prime M q z hq hqM]
  simp [twoRootSelbergDenominator, Nat.div_eq_of_lt hzq]

#print axioms Erdos689.twoRootSelbergWeight_prime
#print axioms Erdos689.twoRootSelbergWeight_mul_of_coprime
#print axioms Erdos689.squarefree_coprime_filter_exclude_prime
#print axioms Erdos689.twoRootSelbergDenominator_prime_dvd_part
#print axioms Erdos689.twoRootSelbergDenominator_exclude_prime
#print axioms Erdos689.twoRootSelbergWeight_pos_of_coprime_even
#print axioms Erdos689.twoRootSelbergDenominator_nonneg
#print axioms Erdos689.twoRootSelbergDenominator_pos
#print axioms Erdos689.twoRootSelbergDenominator_mono
#print axioms Erdos689.twoRootSelbergDenominator_exclude_prime_uniform
#print axioms Erdos689.twoRootSelbergDenominator_exclude_prime_lower
#print axioms Erdos689.twoRootSelbergDenominator_exclude_prime_above_cutoff

end Erdos689
