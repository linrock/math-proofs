module

public import Mathlib


@[expose] public section

/-!
# Finite-set to arbitrary-finite-index adapter

Transfers the uniform noncoverage bound on finite sets `D : Finset ℕ` of
moduli above `B` to arbitrary finite indexed families `m : ι → ℕ` of distinct
positive moduli.
-/

namespace Erdos2.FiniteIndex

/-- Finite-modulus-set noncoverage with one residue assigned to each modulus. -/
def FiniteSetNoncoveringBound : Prop :=
  ∃ B : ℕ, ∀ D : Finset ℕ, (∀ d ∈ D, B < d) → ∀ r : ℕ → ℤ,
    ∃ z : ℤ, ∀ d ∈ D, ¬Int.ModEq (d : ℤ) (r d) z

/-- Literal numerical consumer required by the ideal statement adapter. -/
def UniformNumericalBound : Prop :=
  ∃ B : ℕ, ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (r : ι → ℤ),
    Function.Injective m → (∀ i, 0 < m i) →
    (∀ z : ℤ, ∃ i, Int.ModEq (m i : ℤ) (r i) z) →
    ∃ i, m i ≤ B

/-- Transfer the finite-set core to arbitrary finite indexed covering systems.
The supplied positivity hypothesis is retained verbatim in the consumer. -/
theorem uniformNumericalBound_of_finiteSetNoncovering
    (hnoncovering : FiniteSetNoncoveringBound) : UniformNumericalBound := by
  classical
  obtain ⟨B, hB⟩ := hnoncovering
  refine ⟨B, ?_⟩
  intro ι _ m r hinj _hpos hcover
  by_contra hsmall
  have hlarge : ∀ i, B < m i := by
    intro i
    by_contra hi
    exact hsmall ⟨i, Nat.le_of_not_gt hi⟩
  let D : Finset ℕ := Finset.univ.image m
  let R : ℕ → ℤ := Function.extend m r (fun _ => 0)
  have hD : ∀ d ∈ D, B < d := by
    intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact hlarge i
  obtain ⟨z, hz⟩ := hB D hD R
  obtain ⟨i, hi⟩ := hcover z
  have hmem : m i ∈ D := Finset.mem_image_of_mem m (Finset.mem_univ i)
  have hR : R (m i) = r i := hinj.extend_apply r (fun _ => 0) i
  apply hz (m i) hmem
  simpa only [hR] using hi

end Erdos2.FiniteIndex
