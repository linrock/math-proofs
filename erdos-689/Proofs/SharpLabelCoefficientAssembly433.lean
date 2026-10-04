module

public import LabelGlobalCrt433

@[expose] public section


/-!
# Sharp fixed-label selector-cardinality and coefficient normalization

The corrected actual edge cutoff contributes `1/(a*d)`.  At a support
prime the unit-refined selector has respectively `p-4`/`p-3`, `p-1`, or
`p-1` admissible classes in its principal, left-only, or right-only state.
The exact local normalization converts those genuine class counts into the
already proved three-state fixed-label coefficient factors.
-/

open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The exact predicted *actual* support-unit-refined local selector
cardinality for each of the three coprime coefficient branches. -/
noncomputable def sharpLabelLocalSelectorCard
    (p z b a d : ℕ) : ℕ :=
  if p ∣ a then
    if (2 : ZMod p) * (z : ZMod p) = (b : ZMod p)
      then 0 else p - 1
  else if p ∣ d then
    if (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
      then 0 else p - 1
  else (fixedLabelNaturalAdmissibleResidues p z b).card

/-- The actual three-state switched coefficient factor selected by one
coprime support-divisor pair. -/
noncomputable def sharpLabelLocalCoefficientFactor
    (p z b a d : ℕ) : ℝ :=
  if p ∣ a then actualFixedLabelLeftFactor p z b
  else if p ∣ d then actualFixedLabelRightFactor p z b
  else actualFixedLabelPrincipalFactor p z b

/-- Exact one-prime normalization: restoring the true `a*d` endpoint
denominator converts the actual unit-refined selector count into its
genuine fixed-label coefficient factor. -/
theorem sharpLabelLocalCoefficientFactor_normalization
    (p z b a d : ℕ) (hp : p.Prime)
    (hdisjoint : ¬ (p ∣ a ∧ p ∣ d)) :
    sharpLabelLocalCoefficientFactor p z b a d *
      (if p ∣ a then (p : ℝ) else 1) *
      (if p ∣ d then (p : ℝ) else 1) *
      ((p : ℝ) - 1) ^ 2 =
        (sharpLabelLocalSelectorCard p z b a d : ℝ) * p := by
  have hpone : (p : ℝ) - 1 ≠ 0 := by
    have hcast : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  by_cases ha : p ∣ a
  · have hd : ¬ p ∣ d := fun h => hdisjoint ⟨ha, h⟩
    by_cases htarget :
        (2 : ZMod p) * (z : ZMod p) = (b : ZMod p)
    · simp [sharpLabelLocalCoefficientFactor,
        sharpLabelLocalSelectorCard, actualFixedLabelLeftFactor,
        ha, hd, htarget]
    · simp only [sharpLabelLocalCoefficientFactor,
        sharpLabelLocalSelectorCard, actualFixedLabelLeftFactor,
        ha, hd, htarget, ↓reduceIte, mul_one]
      rw [Nat.cast_sub hp.one_le]
      norm_num
      field_simp
  · by_cases hd : p ∣ d
    · by_cases htarget :
          (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
      · simp [sharpLabelLocalCoefficientFactor,
          sharpLabelLocalSelectorCard, actualFixedLabelRightFactor,
          ha, hd, htarget]
      · simp only [sharpLabelLocalCoefficientFactor,
          sharpLabelLocalSelectorCard, actualFixedLabelRightFactor,
          ha, hd, htarget, ↓reduceIte, mul_one]
        rw [Nat.cast_sub hp.one_le]
        norm_num
        field_simp
    · simp only [sharpLabelLocalCoefficientFactor,
        sharpLabelLocalSelectorCard, actualFixedLabelPrincipalFactor,
        ha, hd, ↓reduceIte, mul_one]
      field_simp

/-- The local coefficient multipliers over a squarefree prime support
recover the exact actual support divisor, not a formal surrogate. -/
theorem sharpLabel_support_divisor_prime_product
    (S : Finset ℕ) (a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p) :
    (∏ p ∈ S, if p ∣ a then (p : ℝ) else 1) = (a : ℝ) := by
  classical
  have hWpositive : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hapositive : 0 < a := Nat.pos_of_dvd_of_pos ha hWpositive
  have hWsq : Squarefree (∏ p ∈ S, p) :=
    Sieve.prodDistinctPrimes_squarefree S hsupport
  have hasq : Squarefree a := Squarefree.squarefree_of_dvd ha hWsq
  have hsubset : a.primeFactors ⊆ S := by
    rw [← Nat.primeFactors_prod hsupport]
    exact Nat.primeFactors_mono ha (Nat.ne_of_gt hWpositive)
  have hfilter : S.filter (fun p => p ∣ a) = a.primeFactors := by
    ext p
    constructor
    · intro h
      obtain ⟨hpS, hpdiv⟩ := Finset.mem_filter.mp h
      exact (Nat.mem_primeFactors_of_ne_zero
        (Nat.ne_of_gt hapositive)).mpr ⟨hsupport p hpS, hpdiv⟩
    · intro hp
      apply Finset.mem_filter.mpr
      exact ⟨hsubset hp, Nat.dvd_of_mem_primeFactors hp⟩
  calc
    (∏ p ∈ S, if p ∣ a then (p : ℝ) else 1) =
        ∏ p ∈ S.filter (fun p => p ∣ a), (p : ℝ) := by
      rw [Finset.prod_filter]
    _ = ∏ p ∈ a.primeFactors, (p : ℝ) := by rw [hfilter]
    _ = ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) :=
      (Finset.prod_natCast a.primeFactors (fun p : ℕ => p)).symm
    _ = (a : ℝ) := by rw [Nat.prod_primeFactors_of_squarefree hasq]

/-- Multiplying the exact three local branch identities over the entire
prime support restores *both* actual divisors and the true squared totient. -/
theorem sharpLabelLocalCoefficientFactor_product_normalization
    (S : Finset ℕ) (z a d : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d) :
    (∏ p ∈ S, sharpLabelLocalCoefficientFactor p z (b p) a d) *
      (a : ℝ) * (d : ℝ) *
        ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 =
          ((∏ p ∈ S,
            sharpLabelLocalSelectorCard p z (b p) a d : ℕ) : ℝ) *
              ((∏ p ∈ S, p : ℕ) : ℝ) := by
  rw [← sharpLabel_support_divisor_prime_product S a hsupport ha,
    ← sharpLabel_support_divisor_prime_product S d hsupport hd,
    prime_support_totient_real_product S hsupport,
    ← Finset.prod_pow,
    Finset.prod_natCast S
      (fun p => sharpLabelLocalSelectorCard p z (b p) a d),
    Finset.prod_natCast S (fun p : ℕ => p)]
  rw [← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  apply sharpLabelLocalCoefficientFactor_normalization
    p z (b p) a d (hsupport p hp)
  rintro ⟨hpa, hpd⟩
  exact ((hsupport p hp).coprime_iff_not_dvd.mp
    (hcoprime.coprime_dvd_left hpa)) hpd

/-- The product of the true local coefficient branches is exactly the
previously audited actual coprime double-divisor coefficient weight. -/
theorem sharpLabelLocalCoefficientFactor_product_eq_actualWeight
    (S : Finset ℕ) (z a d : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d) :
    (∏ p ∈ S, sharpLabelLocalCoefficientFactor p z (b p) a d) =
      actualFixedLabelDoubleCoefficientWeight S z b a d := by
  classical
  have hWpositive : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hapositive : 0 < a := Nat.pos_of_dvd_of_pos ha hWpositive
  have hdpositive : 0 < d := Nat.pos_of_dvd_of_pos hd hWpositive
  have hAsub : a.primeFactors ⊆ S := by
    rw [← Nat.primeFactors_prod hsupport]
    exact Nat.primeFactors_mono ha (Nat.ne_of_gt hWpositive)
  have hDsub : d.primeFactors ⊆ S := by
    rw [← Nat.primeFactors_prod hsupport]
    exact Nat.primeFactors_mono hd (Nat.ne_of_gt hWpositive)
  have hdisjoint := hcoprime.disjoint_primeFactors
  have hDremaining : d.primeFactors ⊆ S \ a.primeFactors :=
    Finset.subset_sdiff.mpr ⟨hDsub, hdisjoint.symm⟩
  have hAprod :
      (∏ p ∈ a.primeFactors,
        sharpLabelLocalCoefficientFactor p z (b p) a d) =
      ∏ p ∈ a.primeFactors, actualFixedLabelLeftFactor p z (b p) := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [sharpLabelLocalCoefficientFactor,
      Nat.dvd_of_mem_primeFactors hp]
  have hDprod :
      (∏ p ∈ d.primeFactors,
        sharpLabelLocalCoefficientFactor p z (b p) a d) =
      ∏ p ∈ d.primeFactors, actualFixedLabelRightFactor p z (b p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpa : ¬ p ∣ a := by
      intro hdiv
      have hmember := (Nat.mem_primeFactors_of_ne_zero
        (Nat.ne_of_gt hapositive)).mpr
          ⟨Nat.prime_of_mem_primeFactors hp, hdiv⟩
      exact Finset.disjoint_left.mp hdisjoint hmember hp
    simp [sharpLabelLocalCoefficientFactor, hpa, hpd]
  have hdiff :
      (S \ a.primeFactors) \ d.primeFactors =
        S \ (a.primeFactors ∪ d.primeFactors) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hremaining :
      (∏ p ∈ (S \ a.primeFactors) \ d.primeFactors,
        sharpLabelLocalCoefficientFactor p z (b p) a d) =
      ∏ p ∈ S \ (a.primeFactors ∪ d.primeFactors),
        actualFixedLabelPrincipalFactor p z (b p) := by
    rw [hdiff]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hpS, hpnot⟩ := Finset.mem_sdiff.mp hp
    have hpnotA : p ∉ a.primeFactors := by
      intro h
      exact hpnot (Finset.mem_union_left _ h)
    have hpnotD : p ∉ d.primeFactors := by
      intro h
      exact hpnot (Finset.mem_union_right _ h)
    have hpa : ¬ p ∣ a := by
      intro hdiv
      exact hpnotA ((Nat.mem_primeFactors_of_ne_zero
        (Nat.ne_of_gt hapositive)).mpr ⟨hsupport p hpS, hdiv⟩)
    have hpd : ¬ p ∣ d := by
      intro hdiv
      exact hpnotD ((Nat.mem_primeFactors_of_ne_zero
        (Nat.ne_of_gt hdpositive)).mpr ⟨hsupport p hpS, hdiv⟩)
    simp [sharpLabelLocalCoefficientFactor, hpa, hpd]
  unfold actualFixedLabelDoubleCoefficientWeight
  calc
    (∏ p ∈ S, sharpLabelLocalCoefficientFactor p z (b p) a d) =
      (∏ p ∈ S \ a.primeFactors,
        sharpLabelLocalCoefficientFactor p z (b p) a d) *
      ∏ p ∈ a.primeFactors,
        sharpLabelLocalCoefficientFactor p z (b p) a d :=
          (Finset.prod_sdiff hAsub).symm
    _ = ((∏ p ∈ (S \ a.primeFactors) \ d.primeFactors,
          sharpLabelLocalCoefficientFactor p z (b p) a d) *
        ∏ p ∈ d.primeFactors,
          sharpLabelLocalCoefficientFactor p z (b p) a d) *
        ∏ p ∈ a.primeFactors,
          sharpLabelLocalCoefficientFactor p z (b p) a d := by
      rw [Finset.prod_sdiff hDremaining]
    _ = _ := by
      rw [hremaining, hDprod, hAprod]
      split_ifs
      ring

/-- Once the independently stated *actual* unit-refined CRT selector-cardinality
identity is supplied, its true cardinality gives the exact previously proved
double-divisor coefficient weight, with both indispensable `1/a` and `1/d`
endpoint factors and the genuine squared support totient. -/
theorem sharpLabel_actual_selector_coefficient_normalization
    (S : Finset ℕ) (z a d q₀ r₀ : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d)
    (hcrt :
      (actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀).card =
        ∏ p ∈ S, sharpLabelLocalSelectorCard p z (b p) a d) :
    actualFixedLabelDoubleCoefficientWeight S z b a d =
      (((actualLabelFiberUnitSelectorResidues
        S b z a d q₀ r₀).card : ℕ) : ℝ) *
        (((∏ p ∈ S, p) : ℕ) : ℝ) /
          ((a : ℝ) * (d : ℝ) *
            ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2) := by
  have hWpositive : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hapositive : 0 < a := Nat.pos_of_dvd_of_pos ha hWpositive
  have hdpositive : 0 < d := Nat.pos_of_dvd_of_pos hd hWpositive
  have htotient : 0 < (∏ p ∈ S, p).totient :=
    Nat.totient_pos.mpr hWpositive
  have hdenominator :
      (0 : ℝ) < (a : ℝ) * (d : ℝ) *
        ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 := by
    exact mul_pos
      (mul_pos (by exact_mod_cast hapositive)
        (by exact_mod_cast hdpositive))
      (sq_pos_of_pos (by exact_mod_cast htotient))
  apply (eq_div_iff (ne_of_gt hdenominator)).mpr
  have hnormalization :=
    sharpLabelLocalCoefficientFactor_product_normalization
      S z a d b hsupport ha hd hcoprime
  rw [sharpLabelLocalCoefficientFactor_product_eq_actualWeight
    S z a d b hsupport ha hd hcoprime, ← hcrt] at hnormalization
  calc
    actualFixedLabelDoubleCoefficientWeight S z b a d *
        ((a : ℝ) * (d : ℝ) *
          ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2) =
      actualFixedLabelDoubleCoefficientWeight S z b a d *
        (a : ℝ) * (d : ℝ) *
          ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 := by ring
    _ = _ := hnormalization

/-- Because the genuine global CRT decomposition is already unconditional,
only identification of each actual local parameter-fiber cardinality with
its three-state branch cardinality remains in the sharp coefficient bridge. -/
theorem sharpLabel_actual_selector_normalization_of_local_cardinalities
    (S : Finset ℕ) (z a d q₀ r₀ : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d)
    (hlocal : ∀ p ∈ S,
      (actualLabelUnitLocalParameterResidues
        p z (b p) a d q₀ r₀).card =
          sharpLabelLocalSelectorCard p z (b p) a d) :
    actualFixedLabelDoubleCoefficientWeight S z b a d =
      (((actualLabelFiberUnitSelectorResidues
        S b z a d q₀ r₀).card : ℕ) : ℝ) *
        (((∏ p ∈ S, p) : ℕ) : ℝ) /
          ((a : ℝ) * (d : ℝ) *
            ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2) := by
  apply sharpLabel_actual_selector_coefficient_normalization
    S z a d q₀ r₀ b hsupport ha hd hcoprime
  rw [actualLabelFiberUnitSelectorResidues_card_eq_local_product
    S b z a d q₀ r₀ hsupport]
  apply Finset.prod_congr rfl
  intro p hp
  exact hlocal p hp

#print axioms Erdos689.sharpLabelLocalCoefficientFactor_normalization
#print axioms Erdos689.sharpLabel_support_divisor_prime_product
#print axioms Erdos689.sharpLabelLocalCoefficientFactor_product_normalization
#print axioms Erdos689.sharpLabelLocalCoefficientFactor_product_eq_actualWeight
#print axioms Erdos689.sharpLabel_actual_selector_coefficient_normalization
#print axioms Erdos689.sharpLabel_actual_selector_normalization_of_local_cardinalities

end Erdos689
