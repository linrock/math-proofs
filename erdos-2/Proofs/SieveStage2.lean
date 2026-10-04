module

public import SieveStep2
public import LateMoment2


@[expose] public section

/-!
# Single-prime inductive stage of the probability sieve

Combines the Chinese Remainder Theorem covering decomposition
(`coveredSet_crt_step`), the progression-bound preservation theorem
(`crtUpdate_preserves_progressionBounds`), and the late second-moment bound
(`late_secondMoment_le_uniformCost`) to advance the sieve from `ZMod Q` to
`ZMod (Q * p ^ γ)`.
-/

open scoped BigOperators
namespace Erdos2.SieveStage

theorem one_prime_stage {Q p γ : ℕ} [NeZero Q] [NeZero p]
    (hp : p.Prime) (hpQ : ¬p ∣ Q)
    (D : Finset ℕ) (r : ℕ → ℤ)
    (w : ProductProbability.ProbabilityWeight (ZMod Q))
    (hw : ProgressionUpdate.HasProgressionBounds Q w.value) (C : ℝ)
    (hprod : (∏ q ∈ Q.primeFactors, EulerMoment.factorBound (q : ℝ)) ≤
      C * Real.log (p : ℝ) ^ 6) :
    ∃ v : ProductProbability.ProbabilityWeight (ZMod (Q * p ^ γ)),
      ProgressionUpdate.HasProgressionBounds (Q * p ^ γ) v.value ∧
      FiniteWeight.mass v.value (CoveringModel.coveredSet D r (Q * p ^ γ)) ≤
        FiniteWeight.mass w.value (CoveringModel.coveredSet D r Q) +
          C * Real.log (p : ℝ) ^ 6 / ((p : ℝ) - 1) ^ 2 := by
  classical
  let hc : Q.Coprime (p ^ γ) :=
    (hp.coprime_iff_not_dvd.mpr hpQ).symm.pow_right γ
  let B := CoveringModel.lateFiber Q p γ r
  let e := (ZMod.chineseRemainder hc).toEquiv
  let u := ProductProbability.update w B
  let v := ProgressionUpdate.crtUpdate hc w B
  refine ⟨v, ProgressionUpdate.crtUpdate_preserves_progressionBounds hp hpQ w B hw, ?_⟩
  have hsubset : (CoveringModel.coveredSet D r (Q * p ^ γ)).image e ⊆
      (CoveringModel.coveredSet D r Q).product Finset.univ ∪ SieveStep.fiberSet B := by
    intro xy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hxy
    exact CoveringModel.coveredSet_crt_step D r hp hpQ z hz
  have hmass : FiniteWeight.mass v.value
      (CoveringModel.coveredSet D r (Q * p ^ γ)) =
      FiniteWeight.mass u.value
        ((CoveringModel.coveredSet D r (Q * p ^ γ)).image e) := by
    unfold FiniteWeight.mass
    rw [Finset.sum_image e.injective.injOn]
    rfl
  have hsecond := LateMoment.late_secondMoment_le_uniformCost (γ := γ) hp w hw r C hprod
  calc
    _ = FiniteWeight.mass u.value
        ((CoveringModel.coveredSet D r (Q * p ^ γ)).image e) := hmass
    _ ≤ FiniteWeight.mass u.value
        ((CoveringModel.coveredSet D r Q).product Finset.univ ∪ SieveStep.fiberSet B) :=
      Finset.sum_mono_set_of_nonneg u.nonneg hsubset
    _ ≤ _ := SieveStep.updated_covered_mass_le w B
      (CoveringModel.coveredSet D r Q) _ hsecond

end Erdos2.SieveStage
