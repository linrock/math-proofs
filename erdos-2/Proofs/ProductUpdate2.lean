module

public import FiberUpdate2
public import Mathlib


@[expose] public section

/-!
# Product-space probability updates

Lifts the half-cap fiber update `Fiber.updatedWeight` to a normalized
probability weight `update w B` on `Ω × β`, preserving cylinder masses on `Ω`,
bounding rectangle masses by a factor of $2 |T| / |\beta|$, and bounding the
new covered fiber mass by the second moment $\sum_x w(x) (|B(x)| / |\beta|)^2$.
-/

open scoped BigOperators
namespace Erdos2.ProductProbability

structure ProbabilityWeight (Ω : Type*) [Fintype Ω] where
  value : Ω → ℝ
  nonneg : ∀ x, 0 ≤ value x
  normalized : ∑ x, value x = 1

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Nonempty β]

noncomputable def update (w : ProbabilityWeight Ω) (B : Ω → Finset β) :
    ProbabilityWeight (Ω × β) where
  value x := Fiber.updatedWeight (B x.1) (w.value x.1) x.2
  nonneg x := Fiber.updatedWeight_nonneg _ _ (w.nonneg x.1) _
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fiber.sum_updatedWeight_eq]
    exact w.normalized

theorem update_atom_le (w : ProbabilityWeight Ω) (B : Ω → Finset β)
    (x : Ω) (y : β) :
    (update w B).value (x,y) ≤ 2 * w.value x / Fintype.card β :=
  Fiber.updatedWeight_le_two _ _ (w.nonneg x) _

theorem update_preserves_cylinder (w : ProbabilityWeight Ω)
    (B : Ω → Finset β) (S : Finset Ω) :
    (∑ x ∈ S, ∑ y : β, (update w B).value (x,y)) =
      ∑ x ∈ S, w.value x :=
  Fiber.preserves_baseEvent_mass S B w.value

theorem update_bad_mass_le_secondMoment (w : ProbabilityWeight Ω)
    (B : Ω → Finset β) :
    (∑ x : Ω, ∑ y ∈ B x, (update w B).value (x,y)) ≤
      ∑ x : Ω, w.value x * (Fiber.fraction (B x)) ^ 2 :=
  Fiber.bad_mass_across_fibers_le_secondMoment Finset.univ B w.value
    (fun x _ => w.nonneg x)

theorem update_rectangle_mass_le (w : ProbabilityWeight Ω)
    (B : Ω → Finset β) (S : Finset Ω) (T : Finset β) :
    (∑ x ∈ S, ∑ y ∈ T, (update w B).value (x,y)) ≤
      (2 * (T.card : ℝ) / Fintype.card β) * (∑ x ∈ S, w.value x) := by
  calc
    _ ≤ ∑ x ∈ S, ∑ _y ∈ T, 2 * w.value x / Fintype.card β := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact update_atom_le w B x y
    _ = ∑ x ∈ S, (2 * (T.card : ℝ) / Fintype.card β) * w.value x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [Finset.mul_sum]

end Erdos2.ProductProbability
