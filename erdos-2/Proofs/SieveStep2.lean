module

public import ProductUpdate2
public import FiniteWeight2


@[expose] public section

/-!
# Abstract product-step covered-mass bound

Bounds the updated probability mass of `S.product Finset.univ ∪ fiberSet B`
by the old covered mass `mass w S` plus any upper bound `b` on the fiber
second moment.
-/

open scoped BigOperators
namespace Erdos2.SieveStep

open ProductProbability

variable {Ω β Γ : Type*} [Fintype Ω] [Fintype β] [Fintype Γ]
  [DecidableEq Ω] [DecidableEq β] [DecidableEq Γ] [Nonempty β]

noncomputable def fiberSet (B : Ω → Finset β) : Finset (Ω × β) := by
  classical
  exact Finset.univ.filter (fun z => z.2 ∈ B z.1)

omit [DecidableEq Ω] [Nonempty β] in
theorem mass_fiberSet_eq (v : Ω × β → ℝ) (B : Ω → Finset β) :
    FiniteWeight.mass v (fiberSet B) = ∑ x : Ω, ∑ y ∈ B x, v (x,y) := by
  classical
  unfold FiniteWeight.mass fiberSet
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_mem_eq]

noncomputable def transport (e : Ω ≃ Γ) (w : ProbabilityWeight Ω) :
    ProbabilityWeight Γ where
  value x := w.value (e.symm x)
  nonneg x := w.nonneg _
  normalized := by
    rw [FiniteWeight.total_transport]
    exact w.normalized

theorem transport_mass (e : Ω ≃ Γ) (w : ProbabilityWeight Ω) (S : Finset Ω) :
    FiniteWeight.mass (transport e w).value (S.image e) =
      FiniteWeight.mass w.value S :=
  FiniteWeight.mass_transport e w.value S

theorem updated_covered_mass_le (w : ProbabilityWeight Ω)
    (B : Ω → Finset β) (S : Finset Ω) (b : ℝ)
    (hsecond : (∑ x : Ω, w.value x * (Fiber.fraction (B x)) ^ 2) ≤ b) :
    FiniteWeight.mass (update w B).value
      (S.product Finset.univ ∪ fiberSet B) ≤ FiniteWeight.mass w.value S + b := by
  apply FiniteWeight.step_mass_le w.value (update w B).value
    (update w B).nonneg
    (fun x => Fiber.sum_updatedWeight_eq (B x) (w.value x)) S (fiberSet B) b
  rw [mass_fiberSet_eq]
  exact (update_bad_mass_le_secondMoment w B).trans hsecond

theorem exists_updated_point_outside (w : ProbabilityWeight Ω)
    (B : Ω → Finset β) (S : Finset Ω) (b : ℝ)
    (hsecond : (∑ x : Ω, w.value x * (Fiber.fraction (B x)) ^ 2) ≤ b)
    (hsmall : FiniteWeight.mass w.value S + b < 1) :
    ∃ z : Ω × β, z ∉ S.product Finset.univ ∪ fiberSet B := by
  apply FiniteWeight.exists_outside_of_mass_lt_one (update w B).value _
    (update w B).normalized
  exact lt_of_le_of_lt (updated_covered_mass_le w B S b hsecond) hsmall

end Erdos2.SieveStep
