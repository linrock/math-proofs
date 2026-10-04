module

public import ActualRightCoefficientAssembly433
public import ActualRightVertexDegree433

@[expose] public section


/-!
# Genuine fixed-left support-unit selectors

The original left-vertex fiber has moving prime forms `q` and
`2*d*q-x`, together with the switched targets `2*x` and `4*d*q`.
Its finite-field selector is, after negating its second form, exactly
the already audited fixed-right selector with coefficient `2*d`.
Because every support prime exceeds three, multiplication by two does
not change the coefficient-prime branches.  Consequently the genuine
left selectors satisfy the same sharp `1/d` coefficient normalization
as the right selectors, without discarding either support-unit test.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The actual fixed-left finite-field selector, containing both genuine
prime-support unit exclusions and both original switched targets. -/
noncomputable def actualLeftVertexLocalResidues
    (p x bp d : ℕ) : Finset (ZMod p) := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    Finset.univ.filter fun q : ZMod p =>
      q ≠ 0 ∧
        ((2 * d : ℕ) : ZMod p) * q - (x : ZMod p) ≠ 0 ∧
        (2 : ZMod p) * (((2 * d : ℕ) : ZMod p) * q) ≠ (bp : ZMod p) ∧
        (2 : ZMod p) * (x : ZMod p) ≠ (bp : ZMod p)
  else ∅

/-- Negating the second nonzero affine form identifies the genuine
fixed-left selector exactly with the fixed-right selector at `2*d`. -/
theorem actualLeftVertexLocalResidues_eq_right_double
    (p x bp d : ℕ) :
    actualLeftVertexLocalResidues p x bp d =
      actualRightVertexLocalResidues p x bp (2 * d) := by
  classical
  unfold actualLeftVertexLocalResidues actualRightVertexLocalResidues
  split_ifs with hp
  · ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hneg :
        ((2 * d : ℕ) : ZMod p) * q - (x : ZMod p) ≠ 0 ↔
          (x : ZMod p) - ((2 * d : ℕ) : ZMod p) * q ≠ 0 := by
      rw [sub_ne_zero, sub_ne_zero]
      exact ne_comm
    tauto
  · rfl

/-- At every genuine support prime, the fixed-left local selector has
the same cardinality as the right selector at coefficient `d` itself:
the factor two cannot introduce a new coefficient-prime branch. -/
theorem actualLeftVertexLocalResidues_card_eq_right
    (p x bp d : ℕ)
    (hp : p.Prime)
    (hpodd : 3 < p)
    (hb : ¬ p ∣ bp)
    (hfixed : (2 : ZMod p) * (x : ZMod p) ≠ (bp : ZMod p)) :
    (actualLeftVertexLocalResidues p x bp d).card =
      (actualRightVertexLocalResidues p x bp d).card := by
  rw [actualLeftVertexLocalResidues_eq_right_double]
  have htwo : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  by_cases hd : p ∣ d
  · have hdouble : p ∣ 2 * d := dvd_mul_of_dvd_right hd 2
    rw [actualRightVertexLocalResidues_card_divisible
      p x bp (2 * d) hp hdouble hb hfixed]
    rw [actualRightVertexLocalResidues_card_divisible
      p x bp d hp hd hb hfixed]
  · have hdouble : ¬ p ∣ 2 * d := by
      rw [hp.dvd_mul]
      exact not_or.mpr ⟨htwo, hd⟩
    rw [actualRightVertexLocalResidues_card_principal
      p x bp (2 * d) hp hdouble hfixed]
    rw [actualRightVertexLocalResidues_card_principal
      p x bp d hp hd hfixed]

/-- The genuine natural-coordinate fixed-left selector imposes every
finite-field support-unit and switched-target condition simultaneously. -/
noncomputable def actualLeftVertexUnitSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (x d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (∏ p ∈ S, p)).filter fun q : ℕ =>
    ∀ p : S, (q : ZMod (p : ℕ)) ∈
      actualLeftVertexLocalResidues (p : ℕ) x (b p) d

/-- Globally the actual left selector is exactly the right selector with
the true doubled moving coefficient; no CRT approximation is involved. -/
theorem actualLeftVertexUnitSelectorResidues_eq_right_double
    (S : Finset ℕ) (b : ℕ → ℕ) (x d : ℕ) :
    actualLeftVertexUnitSelectorResidues S b x d =
      actualRightVertexUnitSelectorResidues S b x (2 * d) := by
  classical
  unfold actualLeftVertexUnitSelectorResidues
    actualRightVertexUnitSelectorResidues
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hlocal⟩
    refine ⟨hq, fun p => ?_⟩
    rw [← actualLeftVertexLocalResidues_eq_right_double]
    exact hlocal p
  · rintro ⟨hq, hlocal⟩
    refine ⟨hq, fun p => ?_⟩
    rw [actualLeftVertexLocalResidues_eq_right_double]
    exact hlocal p

/-- Exact natural-coordinate CRT cardinality for all genuine fixed-left
support-unit and switched selectors. -/
theorem actualLeftVertexUnitSelectorResidues_card_eq_local_product
    (S : Finset ℕ) (b : ℕ → ℕ) (x d : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    (actualLeftVertexUnitSelectorResidues S b x d).card =
      ∏ p ∈ S, (actualLeftVertexLocalResidues p x (b p) d).card := by
  rw [actualLeftVertexUnitSelectorResidues_eq_right_double,
    actualRightVertexUnitSelectorResidues_card_eq_local_product
      S b x (2 * d) hprime]
  apply Finset.prod_congr rfl
  intro p hp
  rw [actualLeftVertexLocalResidues_eq_right_double]

/-- The entire genuine fixed-left CRT selector has the same cardinality
as the audited fixed-right selector at the undoubled support divisor. -/
theorem actualLeftVertexUnitSelectorResidues_card_eq_right
    (S : Finset ℕ) (b : ℕ → ℕ) (x d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p)) :
    (actualLeftVertexUnitSelectorResidues S b x d).card =
      (actualRightVertexUnitSelectorResidues S b x d).card := by
  rw [actualLeftVertexUnitSelectorResidues_card_eq_local_product
    S b x d (fun p hp => (hsupport p hp).1),
    actualRightVertexUnitSelectorResidues_card_eq_local_product
      S b x d (fun p hp => (hsupport p hp).1)]
  apply Finset.prod_congr rfl
  intro p hp
  exact actualLeftVertexLocalResidues_card_eq_right
    p x (b p) d (hsupport p hp).1 (hsupport p hp).2
    (hb p hp) (hfixed p hp)

/-- The full actual fixed-left selector sum, retaining the indispensable
`1/d` coefficient from the original endpoint, is uniformly at most one. -/
theorem actualLeftVertexUnitSelector_normalized_sum_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (x : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p)) :
    (∑ d ∈ (∏ p ∈ S, p).divisors,
      (((actualLeftVertexUnitSelectorResidues S b x d).card : ℕ) : ℝ) *
        ((∏ p ∈ S, p : ℕ) : ℝ) /
          ((d : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)) ≤ 1 := by
  calc
    (∑ d ∈ (∏ p ∈ S, p).divisors,
      (((actualLeftVertexUnitSelectorResidues S b x d).card : ℕ) : ℝ) *
        ((∏ p ∈ S, p : ℕ) : ℝ) /
          ((d : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)) =
      ∑ d ∈ (∏ p ∈ S, p).divisors,
        (((actualRightVertexUnitSelectorResidues S b x d).card : ℕ) : ℝ) *
          ((∏ p ∈ S, p : ℕ) : ℝ) /
            ((d : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [actualLeftVertexUnitSelectorResidues_card_eq_right
        S b x d hsupport hb hfixed]
    _ ≤ 1 := actualRightVertexUnitSelector_normalized_sum_le_one
      S b x hsupport hb hfixed

/-- The old switched-only left selector genuinely overcounts: over the
support prime five it has four classes, while the actual support-unit
selector has exactly two. -/
theorem actualLeftVertexUnitSelector_old_selector_counterexample :
    (actualLeftFiberSelectorResidues {5} (fun _ => 1) 1 1).card = 4 ∧
      (actualLeftVertexUnitSelectorResidues {5} (fun _ => 1) 1 1).card = 2 := by
  constructor
  · decide
  · rw [actualLeftVertexUnitSelectorResidues_card_eq_right
      {5} (fun _ => 1) 1 1]
    · exact actualRightVertexUnitSelector_old_selector_counterexample.2
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      exact ⟨by norm_num, by norm_num⟩
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      norm_num
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      decide

#print axioms Erdos689.actualLeftVertexLocalResidues_eq_right_double
#print axioms Erdos689.actualLeftVertexLocalResidues_card_eq_right
#print axioms Erdos689.actualLeftVertexUnitSelectorResidues_eq_right_double
#print axioms Erdos689.actualLeftVertexUnitSelectorResidues_card_eq_local_product
#print axioms Erdos689.actualLeftVertexUnitSelectorResidues_card_eq_right
#print axioms Erdos689.actualLeftVertexUnitSelector_normalized_sum_le_one
#print axioms Erdos689.actualLeftVertexUnitSelector_old_selector_counterexample

end Erdos689
