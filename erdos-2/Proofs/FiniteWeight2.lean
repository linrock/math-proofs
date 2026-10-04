module

public import Mathlib


@[expose] public section

/-!
# Finite probability-weight bookkeeping

Provides additive mass helpers (`mass_union_le`, `cylinder_mass_eq`,
`step_mass_le`) and the noncoverage principle `exists_outside_of_mass_lt_one`:
if a normalized probability weight assigns mass strictly less than $1$ to $S$,
some element lies outside $S$.
-/

open scoped BigOperators
namespace Erdos2.FiniteWeight

def mass {Ω : Type*} (w : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ x ∈ S, w x

theorem mass_nonneg {Ω : Type*} (w : Ω → ℝ) (S : Finset Ω)
    (hw : ∀ x, 0 ≤ w x) : 0 ≤ mass w S :=
  Finset.sum_nonneg (fun x _ => hw x)

theorem mass_union_le {Ω : Type*} [DecidableEq Ω] (w : Ω → ℝ)
    (S T : Finset Ω) (hw : ∀ x, 0 ≤ w x) :
    mass w (S ∪ T) ≤ mass w S + mass w T := by
  have heq := Finset.sum_union_inter (f := w) (s₁ := S) (s₂ := T)
  have hnonneg := mass_nonneg w (S ∩ T) hw
  simp only [mass] at *
  linarith

theorem mass_transport {Ω Γ : Type*} [DecidableEq Ω] [DecidableEq Γ]
    (e : Ω ≃ Γ) (w : Ω → ℝ) (S : Finset Ω) :
    mass (fun y => w (e.symm y)) (S.image e) = mass w S := by
  unfold mass
  rw [Finset.sum_image e.injective.injOn]
  simp only [e.symm_apply_apply]

theorem total_transport {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (e : Ω ≃ Γ) (w : Ω → ℝ) :
    (∑ y : Γ, w (e.symm y)) = ∑ x : Ω, w x :=
  e.symm.sum_comp w

theorem cylinder_mass_eq {Ω β : Type*} [Fintype β]
    [DecidableEq Ω] [DecidableEq β]
    (w : Ω → ℝ) (v : Ω × β → ℝ)
    (hfiber : ∀ x, ∑ y : β, v (x,y) = w x) (S : Finset Ω) :
    mass v (S.product Finset.univ) = mass w S := by
  unfold mass
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  exact hfiber x

theorem step_mass_le {Ω β : Type*} [Fintype β]
    [DecidableEq Ω] [DecidableEq β]
    (w : Ω → ℝ) (v : Ω × β → ℝ)
    (hv : ∀ z, 0 ≤ v z)
    (hfiber : ∀ x, ∑ y : β, v (x,y) = w x)
    (S : Finset Ω) (T : Finset (Ω × β)) (b : ℝ)
    (hnew : mass v T ≤ b) :
    mass v (S.product Finset.univ ∪ T) ≤ mass w S + b := by
  calc
    _ ≤ mass v (S.product Finset.univ) + mass v T := mass_union_le v _ _ hv
    _ = mass w S + mass v T := by rw [cylinder_mass_eq w v hfiber S]
    _ ≤ _ := add_le_add le_rfl hnew

theorem exists_outside_of_mass_lt_one {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (S : Finset Ω) (hnorm : ∑ x : Ω, w x = 1)
    (hsmall : mass w S < 1) : ∃ x, x ∉ S := by
  by_contra h
  push Not at h
  have hS : S = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  rw [hS] at hsmall
  simp only [mass, hnorm] at hsmall
  linarith

end Erdos2.FiniteWeight
