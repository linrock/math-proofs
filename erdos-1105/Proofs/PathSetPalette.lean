module

public import Mathlib.Tactic

@[expose] public section

/-! A one- or two-color palette whose labels are both realized when needed. -/

namespace ErdosProblems.PathSetLower

/-- Give one distinguished edge color one when there are two palette labels;
give all other edges color zero. With one palette label every edge is zero. -/
noncomputable def twoPaletteColor {E : Type*} [DecidableEq E] {ε : ℕ}
    (hε : 0 < ε) (e₁ : E) : E → Fin ε :=
  fun e =>
    if h₂ : ε = 2 then
      if e = e₁ then Fin.cast h₂.symm (1 : Fin 2)
      else Fin.cast h₂.symm (0 : Fin 2)
    else ⟨0, hε⟩

/-- Two different available edges realize every label in a palette of size
one or two. -/
theorem twoPaletteColor_surjective_on_pair {E : Type*} [DecidableEq E]
    {ε : ℕ} (hε : 0 < ε) (hε₂ : ε ≤ 2)
    (e₀ e₁ : E) (hne : e₀ ≠ e₁) :
    ∀ z : Fin ε, ∃ e : E, (e = e₀ ∨ e = e₁) ∧
      twoPaletteColor hε e₁ e = z := by
  intro z
  by_cases h₂ : ε = 2
  · subst ε
    fin_cases z
    · refine ⟨e₀, Or.inl rfl, ?_⟩
      simp [twoPaletteColor, hne]
    · refine ⟨e₁, Or.inr rfl, ?_⟩
      simp [twoPaletteColor]
  · have h₁ : ε = 1 := by omega
    subst ε
    fin_cases z
    exact ⟨e₀, Or.inl rfl, by simp [twoPaletteColor]⟩

end ErdosProblems.PathSetLower
