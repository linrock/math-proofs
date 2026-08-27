import LabelFiberSieve433
import AffineSieveDegreeSelectors433

/-!
# Actual three-state fixed-label coefficient cancellation

A fixed prime label forbids simultaneous divisibility of its two support
coefficients. Each switched prime therefore has three genuine alternatives:
it divides neither coefficient, the left coefficient, or the right
coefficient. This file counts the actual two-selector residue family and
factorizes the resulting coprime double-divisor sum.
-/

open scoped BigOperators

namespace Erdos689

/-- Actual moving half-target residues for a fixed unit label: both endpoints
must be nonzero and must avoid the genuine switched target. -/
noncomputable def fixedLabelAdmissibleResidues
    (K : Type*) [Field K] [Fintype K] (z b : K) : Finset K := by
  classical
  exact Finset.univ.filter fun x =>
    x ≠ 0 ∧ x + z ≠ 0 ∧
      (2 : K) * x ≠ b ∧ (2 : K) * (x + z) ≠ b

/-- The actual four forbidden classes are zero, the negated label, the
switched half-target, and its translate by the negated label. -/
theorem fixedLabelAdmissibleResidues_eq_erase
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (z b : K) (htwo : (2 : K) ≠ 0) :
    fixedLabelAdmissibleResidues K z b =
      (((Finset.univ.erase 0).erase (-z)).erase
        (b / 2)).erase (b / 2 - z) := by
  classical
  ext x
  simp only [fixedLabelAdmissibleResidues, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  have hfirst : (2 : K) * x ≠ b ↔ x ≠ b / 2 :=
    not_congr (fixedVertex_two_mul_eq_iff x b htwo)
  have hsecond : (2 : K) * (x + z) ≠ b ↔ x ≠ b / 2 - z := by
    constructor
    · intro h heq
      apply h
      apply (fixedVertex_two_mul_eq_iff (x + z) b htwo).mpr
      linear_combination heq
    · intro h heq
      apply h
      have hvalue :=
        (fixedVertex_two_mul_eq_iff (x + z) b htwo).mp heq
      linear_combination hvalue
  have hnonzero : x + z ≠ 0 ↔ x ≠ -z := by
    constructor
    · intro h heq
      apply h
      rw [heq]
      simp
    · intro h heq
      apply h
      linear_combination heq
  rw [hfirst, hsecond, hnonzero]
  tauto

/-- Distinct nonzero opposite classes cannot coincide in odd characteristic. -/
theorem fixedLabel_neg_ne_self
    {K : Type*} [Field K] (x : K)
    (htwo : (2 : K) ≠ 0) (hx : x ≠ 0) :
    -x ≠ x := by
  intro heq
  have hadd : x + x = 0 := by
    linear_combination -heq
  have hzero : (2 : K) * x = 0 := by
    simpa [two_mul] using hadd
  exact (mul_ne_zero htwo hx) hzero

/-- If the label equals the switched half-target, exactly three actual
finite-field classes are forbidden. -/
theorem fixedLabelAdmissibleResidues_card_of_eq_half
    {K : Type*} [Field K] [Fintype K]
    (b : K) (htwo : (2 : K) ≠ 0) (hb : b ≠ 0) :
    (fixedLabelAdmissibleResidues K (b / 2) b).card =
      Fintype.card K - 3 := by
  classical
  have hc : b / (2 : K) ≠ 0 := div_ne_zero hb htwo
  have hneg : -(b / (2 : K)) ≠ b / 2 :=
    fixedLabel_neg_ne_self (b / 2) htwo hc
  rw [fixedLabelAdmissibleResidues_eq_erase (b / 2) b htwo]
  rw [sub_self, Finset.erase_eq_of_notMem (by simp)]
  have hcmem : b / (2 : K) ∈
      (Finset.univ.erase 0).erase (-(b / 2)) := by
    simp [hc, Ne.symm hneg]
  have hnegmem : -(b / (2 : K)) ∈ Finset.univ.erase 0 := by
    simp [hc]
  rw [Finset.card_erase_of_mem hcmem,
    Finset.card_erase_of_mem hnegmem,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),
    Finset.card_univ]
  omega

/-- If the label is the negated switched half-target, exactly three actual
finite-field classes are forbidden. -/
theorem fixedLabelAdmissibleResidues_card_of_eq_neg_half
    {K : Type*} [Field K] [Fintype K]
    (b : K) (htwo : (2 : K) ≠ 0) (hb : b ≠ 0) :
    (fixedLabelAdmissibleResidues K (-(b / 2)) b).card =
      Fintype.card K - 3 := by
  classical
  have hc : b / (2 : K) ≠ 0 := div_ne_zero hb htwo
  have hdouble : b / 2 - -(b / 2) ≠ 0 := by
    intro h
    have hmul : (2 : K) * (b / 2) = 0 := by
      linear_combination h
    exact (mul_ne_zero htwo hc) hmul
  have hneq : b / 2 - -(b / 2) ≠ b / 2 := by
    intro h
    apply hc
    linear_combination h
  rw [fixedLabelAdmissibleResidues_eq_erase (-(b / 2)) b htwo]
  simp only [neg_neg, sub_neg_eq_add, Finset.erase_idem]
  have hdouble' : b / 2 + b / 2 ≠ (0 : K) := by
    simpa [sub_neg_eq_add] using hdouble
  have hneq' : b / 2 + b / 2 ≠ b / 2 := by
    simpa [sub_neg_eq_add] using hneq
  have hdoublemem : b / 2 + b / 2 ∈
      (Finset.univ.erase 0).erase (b / 2) := by
    simp [hdouble', hneq']
  have hcmem : b / (2 : K) ∈ Finset.univ.erase 0 := by
    simp [hc]
  rw [Finset.card_erase_of_mem hdoublemem,
    Finset.card_erase_of_mem hcmem,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),
    Finset.card_univ]
  omega

/-- Outside the two exceptional label classes, all four genuine forbidden
finite-field classes are distinct. -/
theorem fixedLabelAdmissibleResidues_card_of_generic
    {K : Type*} [Field K] [Fintype K]
    (z b : K) (htwo : (2 : K) ≠ 0) (hb : b ≠ 0)
    (hz : z ≠ 0) (hplus : z ≠ b / 2)
    (hminus : z ≠ -(b / 2)) :
    (fixedLabelAdmissibleResidues K z b).card =
      Fintype.card K - 4 := by
  classical
  have hc : b / (2 : K) ≠ 0 := div_ne_zero hb htwo
  have hnegzero : -z ≠ 0 := neg_ne_zero.mpr hz
  have hcneg : b / (2 : K) ≠ -z := by
    intro heq
    apply hminus
    linear_combination heq
  have hshiftzero : b / 2 - z ≠ (0 : K) := by
    intro heq
    apply hplus
    exact (sub_eq_zero.mp heq).symm
  have hshiftneg : b / 2 - z ≠ -z := by
    intro heq
    apply hc
    linear_combination heq
  have hshiftc : b / 2 - z ≠ b / 2 := by
    intro heq
    apply hz
    exact sub_eq_self.mp heq
  rw [fixedLabelAdmissibleResidues_eq_erase z b htwo]
  have hshiftmem : b / 2 - z ∈
      ((Finset.univ.erase 0).erase (-z)).erase (b / 2) := by
    simp [hshiftzero, hshiftneg, hshiftc]
  have hcmem : b / (2 : K) ∈
      (Finset.univ.erase 0).erase (-z) := by
    simp [hc, hcneg]
  have hnegmem : -z ∈ Finset.univ.erase (0 : K) := by
    simp [hnegzero]
  rw [Finset.card_erase_of_mem hshiftmem,
    Finset.card_erase_of_mem hcmem,
    Finset.card_erase_of_mem hnegmem,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),
    Finset.card_univ]
  omega

/-- Exact genuine fixed-label finite-field selector count: `p-3` for either
exceptional label and `p-4` for every other unit label. -/
theorem fixedLabelAdmissibleResidues_card_zmod
    (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hpodd : p ≠ 2)
    (z b : ZMod p) (hz : z ≠ 0) (hb : b ≠ 0) :
    (fixedLabelAdmissibleResidues (ZMod p) z b).card =
      if z = b / 2 ∨ z = -(b / 2) then p - 3 else p - 4 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  split_ifs with hexceptional
  · rcases hexceptional with hplus | hminus
    · subst z
      simpa using fixedLabelAdmissibleResidues_card_of_eq_half b htwo hb
    · subst z
      simpa using fixedLabelAdmissibleResidues_card_of_eq_neg_half b htwo hb
  · have hplus : z ≠ b / 2 := fun h => hexceptional (Or.inl h)
    have hminus : z ≠ -(b / 2) := fun h => hexceptional (Or.inr h)
    simpa using fixedLabelAdmissibleResidues_card_of_generic
      z b htwo hb hz hplus hminus

/-- Natural-indexed genuine finite-field fixed-label selector. -/
noncomputable def fixedLabelNaturalAdmissibleResidues
    (p z b : ℕ) : Finset (ZMod p) :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    fixedLabelAdmissibleResidues (ZMod p)
      (z : ZMod p) (b : ZMod p)
  else ∅

/-- The natural-indexed genuine fixed-label selector has the exact
exceptional/generic `p-3`/`p-4` cardinality. -/
theorem fixedLabelNaturalAdmissibleResidues_card
    (p z b : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hz : (z : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0) :
    (fixedLabelNaturalAdmissibleResidues p z b).card =
      if (2 : ZMod p) * (z : ZMod p) = (b : ZMod p) ∨
          (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
        then p - 3 else p - 4 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  unfold fixedLabelNaturalAdmissibleResidues
  simp only [hp, ↓reduceDIte]
  rw [fixedLabelAdmissibleResidues_card_zmod
    p hp hpodd (z : ZMod p) (b : ZMod p) hz hb]
  congr 1
  rw [fixedVertex_two_mul_eq_iff (z : ZMod p) (b : ZMod p) htwo,
    fixedVertex_two_mul_eq_iff (-(z : ZMod p)) (b : ZMod p) htwo,
    neg_eq_iff_eq_neg]

/-- Principal coefficient state: neither support divisor contains the prime;
its weight is the actual double-selector finite-field cardinality. -/
noncomputable def actualFixedLabelPrincipalFactor
    (p z b : ℕ) : ℝ :=
  (p : ℝ) * ((fixedLabelNaturalAdmissibleResidues p z b).card : ℝ) /
    ((p : ℝ) - 1) ^ 2

/-- Left-only divisor state: its actual switched selector forbids precisely
the positive exceptional label class. -/
noncomputable def actualFixedLabelLeftFactor
    (p z b : ℕ) : ℝ :=
  if (2 : ZMod p) * (z : ZMod p) = (b : ZMod p)
    then 0 else 1 / ((p : ℝ) - 1)

/-- Right-only divisor state: its actual switched selector forbids precisely
the negative exceptional label class. -/
noncomputable def actualFixedLabelRightFactor
    (p z b : ℕ) : ℝ :=
  if (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
    then 0 else 1 / ((p : ℝ) - 1)

/-- Generic three-state cancellation has two genuine exceptional
coefficient branches in addition to its `p-4` principal residues. -/
theorem fixedLabel_generic_three_state_factor_identity
    {s : ℝ} (hone : s ≠ 1) :
    s * (s - 4) / (s - 1) ^ 2 +
      1 / (s - 1) + 1 / (s - 1) =
        1 - 3 / (s - 1) ^ 2 := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hone
  field_simp
  ring

/-- The sum of the three *actual* fixed-label coefficient branches is exactly
the previously audited normalized switched local factor. -/
theorem actualFixedLabel_three_state_sum_eq
    (p z b : ℕ) (hp : p.Prime) (hlarge : 3 < p)
    (hz : (z : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0) :
    actualFixedLabelPrincipalFactor p z b +
      actualFixedLabelLeftFactor p z b +
      actualFixedLabelRightFactor p z b =
        normalizedSwitchedFactor p
          (decide ((2 : ZMod p) * (z : ZMod p) = (b : ZMod p) ∨
            (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p))) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have hp4 : 4 ≤ p := by omega
  have hone : (p : ℝ) ≠ 1 := by
    exact_mod_cast (show p ≠ 1 by omega)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  have hhalf : (b : ZMod p) / 2 ≠ 0 := div_ne_zero hb htwo
  have hdistinct : -((b : ZMod p) / 2) ≠ (b : ZMod p) / 2 :=
    fixedLabel_neg_ne_self ((b : ZMod p) / 2) htwo hhalf
  unfold actualFixedLabelPrincipalFactor actualFixedLabelLeftFactor
    actualFixedLabelRightFactor
  rw [fixedLabelNaturalAdmissibleResidues_card p z b hp hpodd hz hb]
  by_cases hplus : (2 : ZMod p) * (z : ZMod p) = (b : ZMod p)
  · have hminus : (2 : ZMod p) * (-(z : ZMod p)) ≠ (b : ZMod p) := by
      intro heq
      have hplus' :=
        (fixedVertex_two_mul_eq_iff (z : ZMod p) (b : ZMod p) htwo).mp hplus
      have hminus' :=
        (fixedVertex_two_mul_eq_iff (-(z : ZMod p)) (b : ZMod p) htwo).mp heq
      exact hdistinct
        (hminus'.symm.trans (congrArg Neg.neg hplus')).symm
    simp only [hplus, hminus, true_or, ↓reduceIte, decide_true,
      normalizedSwitchedFactor, add_zero]
    rw [Nat.cast_sub hp3]
    norm_num
    simpa [one_div] using fixedVertex_generic_switched_factor_identity hone
  · by_cases hminus : (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
    · simp only [hplus, hminus, or_true, ↓reduceIte, decide_true,
        normalizedSwitchedFactor, add_zero]
      rw [Nat.cast_sub hp3]
      norm_num
      simpa [one_div] using fixedVertex_generic_switched_factor_identity hone
    · simp only [hplus, hminus, or_self, ↓reduceIte, decide_false,
        normalizedSwitchedFactor, Bool.false_eq]
      rw [Nat.cast_sub hp4]
      norm_num
      simpa [one_div] using fixedLabel_generic_three_state_factor_identity hone

/-- Exact three-state subset expansion: the two chosen support subsets are
disjoint, and their complement supplies the principal coefficient state. -/
theorem fixedLabel_disjoint_powerset_three_state_sum
    (S : Finset ℕ) (left right principal : ℕ → ℝ) :
    (∑ A ∈ S.powerset, ∑ D ∈ S.powerset,
      if Disjoint A D then
        (∏ p ∈ A, left p) * (∏ p ∈ D, right p) *
          ∏ p ∈ S \ (A ∪ D), principal p
      else 0) =
        ∏ p ∈ S, (left p + right p + principal p) := by
  classical
  calc
    (∑ A ∈ S.powerset, ∑ D ∈ S.powerset,
      if Disjoint A D then
        (∏ p ∈ A, left p) * (∏ p ∈ D, right p) *
          ∏ p ∈ S \ (A ∪ D), principal p
      else 0) =
        ∑ A ∈ S.powerset,
          (∏ p ∈ A, left p) *
            ∑ D ∈ (S \ A).powerset,
              (∏ p ∈ D, right p) *
                ∏ p ∈ (S \ A) \ D, principal p := by
      apply Finset.sum_congr rfl
      intro A hA
      have hfilter :
          S.powerset.filter (fun D => Disjoint A D) =
            (S \ A).powerset := by
        ext D
        simp [Finset.subset_sdiff, disjoint_comm]
      rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      have hdiff : S \ (A ∪ D) = (S \ A) \ D := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto
      rw [hdiff]
      ring
    _ = ∑ A ∈ S.powerset,
          (∏ p ∈ A, left p) *
            ∏ p ∈ S \ A, (right p + principal p) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [← Finset.prod_add right principal (S \ A)]
    _ = ∏ p ∈ S, (left p + (right p + principal p)) :=
      (Finset.prod_add left (fun p => right p + principal p) S).symm
    _ = ∏ p ∈ S, (left p + right p + principal p) := by
      apply Finset.prod_congr rfl
      intro p _
      ring

/-- Exact reindexing of the genuine coprime double support-divisor sum into
its three independent per-prime coefficient states. -/
theorem fixedLabel_coprime_double_divisor_sum_eq_product
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (left right principal : ℕ → ℝ) :
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      ∑ d ∈ (∏ p ∈ S, p).divisors,
        if Nat.Coprime a d then
          (∏ p ∈ a.primeFactors, left p) *
            (∏ p ∈ d.primeFactors, right p) *
              ∏ p ∈ S \ (a.primeFactors ∪ d.primeFactors), principal p
        else 0) =
      ∏ p ∈ S, (left p + right p + principal p) := by
  classical
  calc
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      ∑ d ∈ (∏ p ∈ S, p).divisors,
        if Nat.Coprime a d then
          (∏ p ∈ a.primeFactors, left p) *
            (∏ p ∈ d.primeFactors, right p) *
              ∏ p ∈ S \ (a.primeFactors ∪ d.primeFactors), principal p
        else 0) =
      ∑ A ∈ S.powerset, ∑ D ∈ S.powerset,
        if Disjoint A D then
          (∏ p ∈ A, left p) * (∏ p ∈ D, right p) *
            ∏ p ∈ S \ (A ∪ D), principal p
        else 0 := by
      rw [affineSelector_sum_divisors_eq_powerset S hprime]
      apply Finset.sum_congr rfl
      intro A hA
      rw [affineSelector_sum_divisors_eq_powerset S hprime]
      apply Finset.sum_congr rfl
      intro D hD
      have hAsub : A ⊆ S := Finset.mem_powerset.mp hA
      have hDsub : D ⊆ S := Finset.mem_powerset.mp hD
      have hAprime : ∀ p ∈ A, p.Prime :=
        fun p hp => hprime p (hAsub hp)
      have hDprime : ∀ p ∈ D, p.Prime :=
        fun p hp => hprime p (hDsub hp)
      have hApos : 0 < ∏ p ∈ A, p :=
        Finset.prod_pos fun p hp => (hAprime p hp).pos
      have hDpos : 0 < ∏ p ∈ D, p :=
        Finset.prod_pos fun p hp => (hDprime p hp).pos
      have hcoprime :
          Nat.Coprime (∏ p ∈ A, p) (∏ p ∈ D, p) ↔
            Disjoint A D := by
        rw [← Nat.disjoint_primeFactors
          (Nat.ne_of_gt hApos) (Nat.ne_of_gt hDpos),
          Nat.primeFactors_prod hAprime,
          Nat.primeFactors_prod hDprime]
      simp only [hcoprime,
        Nat.primeFactors_prod hAprime,
        Nat.primeFactors_prod hDprime]
    _ = _ := fixedLabel_disjoint_powerset_three_state_sum
      S left right principal

/-- The genuine coefficient weight for a fixed label and a support-divisor
pair. Simultaneous divisibility contributes zero, exactly as forced by a
label coprime to the support. -/
noncomputable def actualFixedLabelDoubleCoefficientWeight
    (S : Finset ℕ) (z : ℕ) (b : ℕ → ℕ) (a d : ℕ) : ℝ :=
  if Nat.Coprime a d then
    (∏ p ∈ a.primeFactors,
      actualFixedLabelLeftFactor p z (b p)) *
    (∏ p ∈ d.primeFactors,
      actualFixedLabelRightFactor p z (b p)) *
    ∏ p ∈ S \ (a.primeFactors ∪ d.primeFactors),
      actualFixedLabelPrincipalFactor p z (b p)
  else 0

/-- The complete genuine coprime *double* support-divisor coefficient sum
factors exactly into the three-state fixed-label switched local factors. -/
theorem actualFixedLabel_double_divisor_coefficient_sum_eq_product
    (S : Finset ℕ) (z : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, (z : ZMod p) ≠ 0)
    (hb : ∀ p ∈ S, (b p : ZMod p) ≠ 0) :
    (∑ c ∈ ((∏ p ∈ S, p).divisors.product
          (∏ p ∈ S, p).divisors),
      actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2) =
        ∏ p ∈ S,
          normalizedSwitchedFactor p
            (decide ((2 : ZMod p) * (z : ZMod p) = (b p : ZMod p) ∨
              (2 : ZMod p) * (-(z : ZMod p)) = (b p : ZMod p))) := by
  classical
  have hsum :
      (∑ c ∈ ((∏ p ∈ S, p).divisors.product
          (∏ p ∈ S, p).divisors),
        actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2) =
        ∑ a ∈ (∏ p ∈ S, p).divisors,
          ∑ d ∈ (∏ p ∈ S, p).divisors,
            actualFixedLabelDoubleCoefficientWeight S z b a d := by
    exact Finset.sum_product'
      (∏ p ∈ S, p).divisors (∏ p ∈ S, p).divisors
      (actualFixedLabelDoubleCoefficientWeight S z b)
  rw [hsum]
  unfold actualFixedLabelDoubleCoefficientWeight
  rw [fixedLabel_coprime_double_divisor_sum_eq_product S
    (fun p hp => (hsupport p hp).1)
    (fun p => actualFixedLabelLeftFactor p z (b p))
    (fun p => actualFixedLabelRightFactor p z (b p))
    (fun p => actualFixedLabelPrincipalFactor p z (b p))]
  apply Finset.prod_congr rfl
  intro p hp
  calc
    actualFixedLabelLeftFactor p z (b p) +
        actualFixedLabelRightFactor p z (b p) +
        actualFixedLabelPrincipalFactor p z (b p) =
      actualFixedLabelPrincipalFactor p z (b p) +
        actualFixedLabelLeftFactor p z (b p) +
        actualFixedLabelRightFactor p z (b p) := by ring
    _ = _ := actualFixedLabel_three_state_sum_eq p z (b p)
      (hsupport p hp).1 (hsupport p hp).2 (hz p hp) (hb p hp)

/-- The actual three-state, coprime double support-divisor coefficient sum
is at most one, uniformly in the switched support, target assignment, and
unit prime label. This is the fixed-label analogue of the previously proved
one-divisor/two-state fixed-vertex cancellation. -/
theorem actualFixedLabel_double_divisor_coefficient_sum_le_one
    (S : Finset ℕ) (z : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, (z : ZMod p) ≠ 0)
    (hb : ∀ p ∈ S, (b p : ZMod p) ≠ 0) :
    (∑ c ∈ ((∏ p ∈ S, p).divisors.product
          (∏ p ∈ S, p).divisors),
      actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2) ≤ 1 := by
  rw [actualFixedLabel_double_divisor_coefficient_sum_eq_product
    S z b hsupport hz hb]
  exact fixedLabel_normalizedSwitchedFactor_product_le_one S
    (fun p hp => (hsupport p hp).2)
    (fun p => decide
      ((2 : ZMod p) * (z : ZMod p) = (b p : ZMod p) ∨
        (2 : ZMod p) * (-(z : ZMod p)) = (b p : ZMod p)))

/-- The same exact fixed-label double-divisor coefficient sum retains the
absolute universal half lower bound as well. -/
theorem actualFixedLabel_double_divisor_coefficient_sum_ge_half
    (S : Finset ℕ) (z : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, (z : ZMod p) ≠ 0)
    (hb : ∀ p ∈ S, (b p : ZMod p) ≠ 0) :
    (1 / 2 : ℝ) ≤
      ∑ c ∈ ((∏ p ∈ S, p).divisors.product
          (∏ p ∈ S, p).divisors),
        actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2 := by
  rw [actualFixedLabel_double_divisor_coefficient_sum_eq_product
    S z b hsupport hz hb]
  exact normalized_switched_selector_product_lower S hsupport
    (fun p => decide
      ((2 : ZMod p) * (z : ZMod p) = (b p : ZMod p) ∨
        (2 : ZMod p) * (-(z : ZMod p)) = (b p : ZMod p)))

#print axioms Erdos689.fixedLabelAdmissibleResidues_eq_erase
#print axioms Erdos689.fixedLabel_neg_ne_self
#print axioms Erdos689.fixedLabelAdmissibleResidues_card_of_eq_half
#print axioms Erdos689.fixedLabelAdmissibleResidues_card_of_eq_neg_half
#print axioms Erdos689.fixedLabelAdmissibleResidues_card_of_generic
#print axioms Erdos689.fixedLabelAdmissibleResidues_card_zmod
#print axioms Erdos689.fixedLabelNaturalAdmissibleResidues_card
#print axioms Erdos689.fixedLabel_generic_three_state_factor_identity
#print axioms Erdos689.actualFixedLabel_three_state_sum_eq
#print axioms Erdos689.fixedLabel_disjoint_powerset_three_state_sum
#print axioms Erdos689.fixedLabel_coprime_double_divisor_sum_eq_product
#print axioms Erdos689.actualFixedLabel_double_divisor_coefficient_sum_eq_product
#print axioms Erdos689.actualFixedLabel_double_divisor_coefficient_sum_le_one
#print axioms Erdos689.actualFixedLabel_double_divisor_coefficient_sum_ge_half

end Erdos689
