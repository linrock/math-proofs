module

public import Mathlib
public import SelbergSquarefreeComparison

@[expose] public section


/-!
# Sharp fixed-modulus normalization of the genuine two-root denominator

Complete residue blocks contain exactly `φ(M)` integers coprime to `M`.
Bounding every reciprocal in the `k`-th block below by `1 / ((k + 1) * M)`
gives the sharp leading factor `φ(M) / M`, with no prime asymptotic, Mertens
estimate, or modulus-uniform error.  Combined with the genuine squarefree
denominator comparison, this yields its explicit logarithm-squared lower bound.
-/

open Finset

namespace Erdos689

/-- One complete length-`M` block of natural numbers coprime to `M`. -/
def coprimeResidueBlock (M k : ℕ) : Finset ℕ :=
  (Finset.Ico (k * M) ((k + 1) * M)).filter (fun n => Nat.Coprime n M)

/-- Every complete residue block has precisely Euler's totient many members. -/
theorem coprimeResidueBlock_card (M k : ℕ) :
    (coprimeResidueBlock M k).card = M.totient := by
  simpa [coprimeResidueBlock, Nat.coprime_comm, Nat.add_mul] using
    Nat.filter_coprime_Ico_eq_totient M (k * M)

/-- Distinct complete residue blocks are disjoint, even before sieving. -/
theorem coprimeResidueBlocks_pairwise_disjoint (M K : ℕ) :
    ((Finset.range K) : Set ℕ).PairwiseDisjoint (coprimeResidueBlock M) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  have hni' := Finset.mem_Ico.mp
    (Finset.mem_filter.mp hni).1
  have hnj' := Finset.mem_Ico.mp
    (Finset.mem_filter.mp hnj).1
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hbound := Nat.mul_le_mul_right M (show i + 1 ≤ j by omega)
    omega
  · have hbound := Nat.mul_le_mul_right M (show j + 1 ≤ i by omega)
    omega

/-- Every integer in an admissible block for `M ≥ 2` is strictly positive. -/
theorem coprimeResidueBlock_pos {M k n : ℕ} (hM : 2 ≤ M)
    (hn : n ∈ coprimeResidueBlock M k) :
    0 < n := by
  have hcoprime := (Finset.mem_filter.mp hn).2
  by_contra hnonpositive
  have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnonpositive
  subst n
  have hMone : M = 1 := by simpa using hcoprime
  omega

/-- The reciprocal sum in a complete block has its exact totient-over-block
lower bound. -/
theorem coprimeResidueBlock_harmonic_lower (M k : ℕ) (hM : 2 ≤ M) :
    (M.totient : ℝ) / (((k + 1) * M : ℕ) : ℝ) ≤
      ∑ n ∈ coprimeResidueBlock M k, (n : ℝ)⁻¹ := by
  calc
    (M.totient : ℝ) / (((k + 1) * M : ℕ) : ℝ) =
        ∑ _n ∈ coprimeResidueBlock M k,
          ((((k + 1) * M : ℕ) : ℝ))⁻¹ := by
            simp [coprimeResidueBlock_card, div_eq_mul_inv]
    _ ≤ ∑ n ∈ coprimeResidueBlock M k, (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          have hnpos : (0 : ℝ) < n := by
            exact_mod_cast coprimeResidueBlock_pos hM hn
          have hnupper : (n : ℝ) ≤ (((k + 1) * M : ℕ) : ℝ) := by
            exact_mod_cast
              (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).2.le
          exact inv_anti₀ hnpos hnupper

/-- All complete residue blocks up to `⌊L/M⌋` lie in the original positive
coprime interval; no incomplete last block is assumed. -/
theorem coprimeResidueBlocks_subset_coprime_interval (M L : ℕ)
    (hM : 2 ≤ M) :
    ((Finset.range (L / M)).biUnion (coprimeResidueBlock M)) ⊆
      (Finset.Icc 1 L).filter (fun n => Nat.Coprime n M) := by
  intro n hn
  obtain ⟨k, hk, hnblock⟩ := Finset.mem_biUnion.mp hn
  have hklt := Finset.mem_range.mp hk
  have hninterval := (Finset.mem_filter.mp hnblock).1
  have hncoprime := (Finset.mem_filter.mp hnblock).2
  have hnpos := coprimeResidueBlock_pos hM hnblock
  have hblockupper := (Finset.mem_Ico.mp hninterval).2
  have hblocksbound := Nat.mul_le_mul_right M
    (show k + 1 ≤ L / M by omega)
  have hfloorbound := Nat.div_mul_le_self L M
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hnpos, by omega⟩, hncoprime⟩

/-- Complete residue blocks give the exact totient-normalized finite harmonic
lower bound for every fixed excluded modulus. -/
theorem coprime_harmonic_ge_totient_mul_harmonic (M L : ℕ)
    (hM : 2 ≤ M) :
    ((M.totient : ℝ) / M) * (harmonic (L / M) : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 L).filter (fun n => Nat.Coprime n M),
        (n : ℝ)⁻¹ := by
  classical
  let K := L / M
  have hseries : (harmonic K : ℝ) =
      ∑ k ∈ Finset.range K, (((k + 1 : ℕ) : ℝ))⁻¹ := by
    unfold harmonic
    push_cast
    rfl
  have hdisjoint := coprimeResidueBlocks_pairwise_disjoint M K
  calc
    ((M.totient : ℝ) / M) * (harmonic (L / M) : ℝ) =
        ∑ k ∈ Finset.range K,
          (M.totient : ℝ) / (((k + 1) * M : ℕ) : ℝ) := by
            change ((M.totient : ℝ) / M) * (harmonic K : ℝ) = _
            rw [hseries, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            field_simp
    _ ≤ ∑ k ∈ Finset.range K,
          ∑ n ∈ coprimeResidueBlock M k, (n : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro k hk
            exact coprimeResidueBlock_harmonic_lower M k hM
    _ = ∑ n ∈ (Finset.range K).biUnion (coprimeResidueBlock M),
          (n : ℝ)⁻¹ := (Finset.sum_biUnion hdisjoint).symm
    _ ≤ ∑ n ∈ (Finset.Icc 1 L).filter (fun n => Nat.Coprime n M),
          (n : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact coprimeResidueBlocks_subset_coprime_interval M L hM
            · intro n hn hnot
              positivity

/-- Explicit sharp-modulus harmonic bound with only a finite cutoff loss. -/
theorem coprime_harmonic_ge_totient_mul_log (M L : ℕ)
    (hM : 2 ≤ M) :
    ((M.totient : ℝ) / M) * Real.log ((L / M + 1 : ℕ) : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 L).filter (fun n => Nat.Coprime n M),
        (n : ℝ)⁻¹ := by
  have hfactor : 0 ≤ (M.totient : ℝ) / M := by positivity
  exact (mul_le_mul_of_nonneg_left (log_add_one_le_harmonic (L / M))
    hfactor).trans (coprime_harmonic_ge_totient_mul_harmonic M L hM)

/-- The genuine squarefree two-root Selberg denominator has the sharp
excluded-modulus factor `(φ(M) / M)^2` and its complete explicit logarithmic
lower bound, for every even `M ≥ 2` and every finite cutoff. -/
theorem twoRootSelbergDenominator_ge_totient_log_sq (M L : ℕ)
    (hMeven : 2 ∣ M) (hM : 2 ≤ M) :
    (((M.totient : ℝ) / M) ^ 2) *
        (Real.log ((L / M + 1 : ℕ) : ℝ)) ^ 2 ≤
      twoRootSelbergDenominator M (L ^ 2) := by
  have hlog_nonneg : 0 ≤ Real.log ((L / M + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.le_add_left 1 (L / M)
  have hfactor_nonneg : 0 ≤ (M.totient : ℝ) / M := by positivity
  have hblock := coprime_harmonic_ge_totient_mul_log M L hM
  have hsquare := pow_le_pow_left₀
    (mul_nonneg hfactor_nonneg hlog_nonneg) hblock 2
  calc
    (((M.totient : ℝ) / M) ^ 2) *
        (Real.log ((L / M + 1 : ℕ) : ℝ)) ^ 2 =
      (((M.totient : ℝ) / M) *
        Real.log ((L / M + 1 : ℕ) : ℝ)) ^ 2 := by ring
    _ ≤ (∑ n ∈ (Finset.Icc 1 L).filter (fun n => Nat.Coprime n M),
        (n : ℝ)⁻¹) ^ 2 := hsquare
    _ ≤ twoRootSelbergDenominator M (L ^ 2) :=
      coprime_harmonic_sq_le_twoRootSelbergDenominator L M hMeven

/-- Deleting a completely arbitrary moving outside prime preserves the sharp
*fixed-modulus* totient normalization, uniformly losing at most `3/5`. -/
theorem twoRootSelbergDenominator_excluded_prime_ge_totient_log_sq
    (M q L : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M)
    (hq : q.Prime) (hqM : Nat.Coprime q M) (hqfive : 5 ≤ q) :
    (3 / 5 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log ((L / M + 1 : ℕ) : ℝ)) ^ 2 ≤
      twoRootSelbergDenominator (M * q) (L ^ 2) := by
  have hbase := twoRootSelbergDenominator_ge_totient_log_sq M L hMeven hM
  have hmove := twoRootSelbergDenominator_exclude_prime_lower M q (L ^ 2)
    hMeven hq hqM hqfive
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (show (0 : ℝ) ≤ 3 / 5 by norm_num)
  nlinarith

#print axioms Erdos689.coprimeResidueBlock_card
#print axioms Erdos689.coprimeResidueBlocks_pairwise_disjoint
#print axioms Erdos689.coprimeResidueBlock_pos
#print axioms Erdos689.coprimeResidueBlock_harmonic_lower
#print axioms Erdos689.coprimeResidueBlocks_subset_coprime_interval
#print axioms Erdos689.coprime_harmonic_ge_totient_mul_harmonic
#print axioms Erdos689.coprime_harmonic_ge_totient_mul_log
#print axioms Erdos689.twoRootSelbergDenominator_ge_totient_log_sq
#print axioms Erdos689.twoRootSelbergDenominator_excluded_prime_ge_totient_log_sq

end Erdos689
