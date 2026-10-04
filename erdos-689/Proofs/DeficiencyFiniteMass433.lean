module

public import DeficiencyUpper433

@[expose] public section


/-!
# Sharp mass bound for arbitrary finite actual deficiency strata

Every admissible even smooth-core/reduced-residue family embeds into one
genuine finite exponent rectangle.  Its exact fixed-progression density is
therefore at most the rectangle's normalized coefficient, which is at most
one.  This is the sharp finite-core component of the missing deficiency
upper asymptotic; no covering or unproved analytic estimate is assumed.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Every finite dyadic truncation has mass at most its exact full mass one. -/
theorem truncatedDyadicDeficiencyCoefficient_le_one (E : ℕ) :
    truncatedDyadicDeficiencyCoefficient E ≤ 1 := by
  have hbase : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hshift : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ (k + 1)) := by
    simpa [pow_succ] using hbase.mul_right ((2 : ℝ)⁻¹)
  have hbound := hshift.sum_le_tsum (Finset.range E)
    (fun k hk => by positivity)
  rw [dyadic_deficiency_coefficient_tsum] at hbound
  exact hbound

/-- The truncated dyadic coefficient is nonnegative. -/
theorem truncatedDyadicDeficiencyCoefficient_nonneg (E : ℕ) :
    0 ≤ truncatedDyadicDeficiencyCoefficient E := by
  unfold truncatedDyadicDeficiencyCoefficient
  exact Finset.sum_nonneg fun k hk => by positivity

/-- Every fixed-prime truncated selector has mass at most its exact full mass
one. -/
theorem truncatedSmoothDeficiencySelector_le_one
    (s E : ℕ) (hs : 1 < s) :
    truncatedSmoothDeficiencySelector s E ≤ 1 := by
  have hsreal : (1 : ℝ) < s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := lt_trans (by norm_num) hsreal
  have hbase : Summable (fun e : ℕ => ((s : ℝ)⁻¹) ^ e) :=
    summable_geometric_of_lt_one (by positivity)
      ((inv_lt_one₀ hspos).mpr hsreal)
  have hshift : Summable (fun e : ℕ => ((s : ℝ)⁻¹) ^ (e + 1)) := by
    simpa [pow_succ] using hbase.mul_right ((s : ℝ)⁻¹)
  have hbound := hshift.sum_le_tsum (Finset.range E)
    (fun e he => by positivity)
  have hnormalized := deficiency_local_selector_eq_one s hs
  unfold truncatedSmoothDeficiencySelector
  linarith

/-- Every fixed-prime truncated selector is nonnegative. -/
theorem truncatedSmoothDeficiencySelector_nonneg
    (s E : ℕ) (hs : 1 < s) :
    0 ≤ truncatedSmoothDeficiencySelector s E := by
  have hsreal : (1 : ℝ) < s := by exact_mod_cast hs
  have hstwo : (2 : ℝ) ≤ s := by exact_mod_cast (by omega : 2 ≤ s)
  unfold truncatedSmoothDeficiencySelector
  apply add_nonneg
  · exact div_nonneg (by linarith) (by linarith)
  · exact Finset.sum_nonneg fun e he => by positivity

/-- Every genuine finite smooth-coefficient rectangle has total normalized
mass at most one. -/
theorem truncatedInitialDeficiencyCoefficient_le_one
    (S : Finset ℕ) (E : ℕ)
    (hsupport : ∀ s ∈ S, 1 < s) :
    truncatedInitialDeficiencyCoefficient S E ≤ 1 := by
  have hdyadic := truncatedDyadicDeficiencyCoefficient_le_one E
  have hdyadic_nonneg := truncatedDyadicDeficiencyCoefficient_nonneg E
  have hproduct :
      (∏ s ∈ S, truncatedSmoothDeficiencySelector s E) ≤ 1 := by
    exact Finset.prod_le_one₀
      (fun s hs => truncatedSmoothDeficiencySelector_nonneg s E (hsupport s hs))
      (fun s hs => truncatedSmoothDeficiencySelector_le_one s E (hsupport s hs))
  have hproduct_nonneg :
      0 ≤ (∏ s ∈ S, truncatedSmoothDeficiencySelector s E) :=
    Finset.prod_nonneg fun s hs =>
      truncatedSmoothDeficiencySelector_nonneg s E (hsupport s hs)
  unfold truncatedInitialDeficiencyCoefficient
  nlinarith

/-- Every actual even support-smooth coefficient is exactly its dyadic/support
prime-factor exponent encoding. -/
theorem deficiencySmoothCoefficient_eq_smoothRectangleCore
    {S : Finset ℕ} {c : ℕ}
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hc : deficiencySmoothCoefficient S c) :
    c = smoothRectangleCore S (c.factorization 2 - 1)
      (fun p : {p : ℕ // p ∈ S} => c.factorization p) := by
  classical
  let k : ℕ := c.factorization 2 - 1
  let v : {p : ℕ // p ∈ S} → ℕ := fun p => c.factorization p
  have hcore := smoothRectangleCore_smooth S k v hsupport
  apply Nat.eq_of_factorization_eq (ne_of_gt hc.1) (ne_of_gt hcore.1)
  intro q
  by_cases hqprime : q.Prime
  · by_cases hqtwo : q = 2
    · subst q
      rw [smoothRectangleCore_factorization_two S k v hsupport hodd]
      have hpositive := Nat.prime_two.factorization_pos_of_dvd
        (ne_of_gt hc.1) hc.2.1
      dsimp [k]
      omega
    · by_cases hqS : q ∈ S
      · let q' : {p : ℕ // p ∈ S} := ⟨q, hqS⟩
        have heq := smoothRectangleCore_factorization_support
          S k v q' hsupport hodd
        exact heq.symm
      · have hcnot : ¬ q ∣ c := by
          intro hdiv
          rcases hc.2.2 q hqprime hdiv with htwo | hmem
          · exact hqtwo htwo
          · exact hqS hmem
        have hcorenot : ¬ q ∣ smoothRectangleCore S k v := by
          intro hdiv
          rcases hcore.2.2 q hqprime hdiv with htwo | hmem
          · exact hqtwo htwo
          · exact hqS hmem
        rw [Nat.factorization_eq_zero_of_not_dvd hcnot,
          Nat.factorization_eq_zero_of_not_dvd hcorenot]
  · rw [Nat.factorization_eq_zero_of_not_prime c hqprime,
      Nat.factorization_eq_zero_of_not_prime
        (smoothRectangleCore S k v) hqprime]

/-- Every finite admissible smooth-core/residue family lies inside the actual
exponent rectangle whose side is the largest core in the family. -/
theorem admissibleSmoothDeficiencyCoreFamily_subset_rectangle
    (S : Finset ℕ) (b : ℕ → ℕ) (F : Finset (ℕ × ℕ))
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hfamily : ∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) :
    F ⊆ smoothRectangleFamily S b (F.sup Prod.fst) := by
  classical
  intro u hu
  obtain ⟨hsmooth, hr, hcoprime, hmiss⟩ := hfamily u hu
  let E : ℕ := F.sup Prod.fst
  let k : ℕ := u.1.factorization 2 - 1
  let v : {p : ℕ // p ∈ S} → ℕ := fun p => u.1.factorization p
  have hcore : u.1 = smoothRectangleCore S k v :=
    deficiencySmoothCoefficient_eq_smoothRectangleCore hsupport hodd hsmooth
  have hcorebound : u.1 ≤ E := Finset.le_sup (f := Prod.fst) hu
  have hklt : k < E := by
    have hfactor := Nat.factorization_lt 2 (ne_of_gt hsmooth.1)
    dsimp [k]
    omega
  have hvbound : v ∈ smoothRectangleExponentVectors S E := by
    unfold smoothRectangleExponentVectors
    apply Fintype.mem_piFinset.mpr
    intro p
    apply Finset.mem_range.mpr
    have hfactor := Nat.factorization_lt (p : ℕ) (ne_of_gt hsmooth.1)
    dsimp [v]
    omega
  unfold smoothRectangleFamily
  apply Finset.mem_image.mpr
  refine ⟨((k, v), u.2), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_range.mpr hklt, hvbound⟩
      · exact Finset.mem_range.mpr hr
    · constructor
      · exact hcoprime
      · rw [← hcore]
        exact hmiss
  · exact Prod.ext hcore.symm rfl

/-- Sharp full mass bound for every finite family of actual admissible even
smooth cores and missed reduced residues. -/
theorem admissibleSmoothDeficiencyCoreFamily_weight_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (F : Finset (ℕ × ℕ))
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p)
    (hfamily : ∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) :
    (∑ v ∈ F,
      (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹)) ≤ 1 := by
  classical
  let E : ℕ := F.sup Prod.fst
  have hsubset := admissibleSmoothDeficiencyCoreFamily_subset_rectangle
    S b F hsupport hodd hfamily
  calc
    (∑ v ∈ F,
      (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹)) ≤
      ∑ v ∈ smoothRectangleFamily S b E,
        (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro v hv hnot
          positivity
    _ = truncatedInitialDeficiencyCoefficient S E :=
      smoothRectangleFamily_weight_eq S b E hsupport hodd hb
    _ ≤ 1 := truncatedInitialDeficiencyCoefficient_le_one S E
      (fun p hp => (hsupport p hp).one_lt)

/-- The complete actual moving smooth-core/reduced-residue family has sharp
total prime-progression coefficient at most one at every finite endpoint. -/
theorem initialDeficiencySmoothCoreFamily_weight_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    (∑ v ∈ initialDeficiencySmoothCoreFamily S b n,
      (1 / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹)) ≤ 1 :=
  admissibleSmoothDeficiencyCoreFamily_weight_le_one S b
    (initialDeficiencySmoothCoreFamily S b n) hsupport hodd hb
    (fun _v hv => initialDeficiencySmoothCoreFamily_admissible hv)

#print axioms Erdos689.truncatedDyadicDeficiencyCoefficient_le_one
#print axioms Erdos689.truncatedDyadicDeficiencyCoefficient_nonneg
#print axioms Erdos689.truncatedSmoothDeficiencySelector_le_one
#print axioms Erdos689.truncatedSmoothDeficiencySelector_nonneg
#print axioms Erdos689.truncatedInitialDeficiencyCoefficient_le_one
#print axioms Erdos689.deficiencySmoothCoefficient_eq_smoothRectangleCore
#print axioms Erdos689.admissibleSmoothDeficiencyCoreFamily_subset_rectangle
#print axioms Erdos689.admissibleSmoothDeficiencyCoreFamily_weight_le_one
#print axioms Erdos689.initialDeficiencySmoothCoreFamily_weight_le_one

end Erdos689
