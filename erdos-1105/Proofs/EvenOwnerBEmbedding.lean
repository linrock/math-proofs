module

public import Mathlib.Data.Fin.Embedding
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Finite `B`-side vertex placement preserving a distinguished edge and owner endpoint.
-/
namespace ErdosProblems.EvenExceptionExchange

/-- Keep the distinguished new B edge in positions zero/one and retain any
specified actual owner endpoint. A third distinct endpoint is at position two.
All sizes and endpoint coincidences are included. -/
theorem exists_b_embedding_with_owner
    (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (u v w : Fin b) (huv : u ≠ v) :
    ∃ f : Fin (a + 1) ↪ Fin b,
      f ⟨0, by omega⟩ = u ∧ f ⟨1, by omega⟩ = v ∧
      w ∈ Set.range f ∧
      (w ≠ u → w ≠ v → f ⟨2, by omega⟩ = w) := by
  classical
  let x0 : Fin b := ⟨0, by omega⟩
  let x1 : Fin b := ⟨1, by omega⟩
  let x2 : Fin b := ⟨2, by omega⟩
  have h01 : x0 ≠ x1 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x0, x1] at hv
    omega
  have h02 : x0 ≠ x2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x0, x2] at hv
    omega
  have h12 : x1 ≠ x2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x1, x2] at hv
    omega
  let σ : Equiv.Perm (Fin b) := Equiv.swap x0 u
  have hσ0 : σ x0 = u := Equiv.swap_apply_left x0 u
  let z : Fin b := σ.symm v
  have hz0 : z ≠ x0 := by
    intro h
    apply huv
    calc
      u = σ x0 := hσ0.symm
      _ = σ z := congrArg σ h.symm
      _ = v := σ.apply_symm_apply v
  let τ : Equiv.Perm (Fin b) := Equiv.swap x1 z
  have hτ0 : τ x0 = x0 :=
    Equiv.swap_apply_of_ne_of_ne h01 hz0.symm
  have hτ1 : τ x1 = z := Equiv.swap_apply_left x1 z
  let π : Equiv.Perm (Fin b) := τ.trans σ
  have hπ0 : π x0 = u := by
    change σ (τ x0) = u
    rw [hτ0]
    exact hσ0
  have hπ1 : π x1 = v := by
    change σ (τ x1) = v
    rw [hτ1]
    exact σ.apply_symm_apply v
  let e : Fin (a + 1) ↪ Fin b := (Fin.castLEEmb hab).trans π.toEmbedding
  have he0 : e ⟨0, by omega⟩ = u := by
    change π x0 = u
    exact hπ0
  have he1 : e ⟨1, by omega⟩ = v := by
    change π x1 = v
    exact hπ1
  by_cases hwu : w = u
  · refine ⟨e, he0, he1, ?_, ?_⟩
    · exact ⟨⟨0, by omega⟩, he0.trans hwu.symm⟩
    · intro hne _
      exact (hne hwu).elim
  by_cases hwv : w = v
  · refine ⟨e, he0, he1, ?_, ?_⟩
    · exact ⟨⟨1, by omega⟩, he1.trans hwv.symm⟩
    · intro _ hne
      exact (hne hwv).elim
  let t : Fin b := π.symm w
  have ht0 : x0 ≠ t := by
    intro h
    apply hwu
    calc
      w = π t := (π.apply_symm_apply w).symm
      _ = π x0 := congrArg π h.symm
      _ = u := hπ0
  have ht1 : x1 ≠ t := by
    intro h
    apply hwv
    calc
      w = π t := (π.apply_symm_apply w).symm
      _ = π x1 := congrArg π h.symm
      _ = v := hπ1
  let γ : Equiv.Perm (Fin b) := Equiv.swap x2 t
  have hγ0 : γ x0 = x0 := Equiv.swap_apply_of_ne_of_ne h02 ht0
  have hγ1 : γ x1 = x1 := Equiv.swap_apply_of_ne_of_ne h12 ht1
  have hγ2 : γ x2 = t := Equiv.swap_apply_left x2 t
  let f : Fin (a + 1) ↪ Fin b :=
    (Fin.castLEEmb hab).trans (γ.trans π).toEmbedding
  have hf0 : f ⟨0, by omega⟩ = u := by
    change π (γ x0) = u
    rw [hγ0]
    exact hπ0
  have hf1 : f ⟨1, by omega⟩ = v := by
    change π (γ x1) = v
    rw [hγ1]
    exact hπ1
  have hf2 : f ⟨2, by omega⟩ = w := by
    change π (γ x2) = w
    rw [hγ2]
    exact π.apply_symm_apply w
  exact ⟨f, hf0, hf1, ⟨⟨2, by omega⟩, hf2⟩, fun _ _ => hf2⟩

end ErdosProblems.EvenExceptionExchange
