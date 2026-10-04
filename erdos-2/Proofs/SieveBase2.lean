module

public import UniformResidue2
public import ProgressionUpdate2
public import CoveringModel2
public import FiniteLcm2
public import Mathlib


@[expose] public section

/-!
# Base stage of the probability sieve on $A$-smooth moduli

When all prime factors of $N$ are at most $A$, the uniform probability weight
`UniformResidue.uniform N` satisfies `HasProgressionBounds N` and assigns mass
at most $\sum_{d \in D,\, P^+(d) \le A} 1/d$ to the covered set.
-/

open scoped BigOperators

namespace Erdos2.SieveBase

theorem uniform_base_stage (N : ℕ) [NeZero N] (D : Finset ℕ)
    (r : ℕ → ℤ) (A : ℕ) (hsmall : ∀ q ∈ N.primeFactors, q ≤ A) :
    ∃ w : ProductProbability.ProbabilityWeight (ZMod N),
      ProgressionUpdate.HasProgressionBounds N w.value ∧
      FiniteWeight.mass w.value (CoveringModel.coveredSet D r N) ≤
        ∑ d ∈ D.filter (fun d => ∀ q ∈ d.primeFactors, q ≤ A), 1 / (d : ℝ) := by
  classical
  let S := D.filter (fun d => d ∣ N)
  let hdiv : ∀ i : S, i.val ∣ N := fun i => (Finset.mem_filter.mp i.property).2
  let C : S → Finset (ZMod N) := fun i =>
    Finset.univ.filter (fun z : ZMod N =>
      ZMod.castHom (hdiv i) (ZMod i.val) z = (r i.val : ZMod i.val))
  let U := (Finset.univ : Finset S).biUnion C
  refine ⟨UniformResidue.uniform N, ?_, ?_⟩
  · intro d hd a
    simpa only [ProgressionUpdate.residueMass, ProgressionUpdate.residueClass,
      FiniteWeight.mass] using UniformResidue.uniform_progression_bound hd a
  · have hcovered : CoveringModel.coveredSet D r N ⊆ U := by
      intro z hz
      obtain ⟨d, hdD, hdN, hclass⟩ := (CoveringModel.mem_coveredSet D r N z).mp hz
      let i : S := ⟨d, Finset.mem_filter.mpr ⟨hdD, hdN⟩⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hclass
    have hmass : FiniteWeight.mass (UniformResidue.uniform N).value
        (CoveringModel.coveredSet D r N) ≤
        FiniteWeight.mass (UniformResidue.uniform N).value U := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hcovered
        (fun z _ _ => (UniformResidue.uniform N).nonneg z)
    have hsum : FiniteWeight.mass (UniformResidue.uniform N).value U ≤
        ∑ d ∈ S, 1 / (d : ℝ) := by
      calc
        _ ≤ ∑ i : S, 1 / (i.val : ℝ) :=
          UniformResidue.uniform_union_mass_le (Finset.univ : Finset S)
            (fun i : S => i.val) (fun i : S => r i.val) hdiv
        _ = ∑ d ∈ S, 1 / (d : ℝ) :=
          Finset.sum_coe_sort S (fun d : ℕ => 1 / (d : ℝ))
    have hsubset : S ⊆ D.filter (fun d => ∀ q ∈ d.primeFactors, q ≤ A) := by
      intro d hd
      obtain ⟨hdD, hdN⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hdD,
        FiniteLcm.primeFactors_le_of_dvd (NeZero.ne N) hdN hsmall⟩
    calc
      _ ≤ FiniteWeight.mass (UniformResidue.uniform N).value U := hmass
      _ ≤ ∑ d ∈ S, 1 / (d : ℝ) := hsum
      _ ≤ ∑ d ∈ D.filter (fun d => ∀ q ∈ d.primeFactors, q ≤ A), 1 / (d : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => by positivity)

end Erdos2.SieveBase
