module

public import PathUpperEligibleBirthDescent
public import Mathlib.Data.Nat.Find

@[expose] public section

/-!
All color values and `χ` are original; the entire inside palette excludes `U`,
and initial-slot deletions and current connectedness are retained.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Add every ELIGIBLE ORIGINAL color of an ORIGINAL inside-X edge crossing the deletion
of the SAME ORIGINAL selected slots in A. No current representative is used. -/
noncomputable def eligibleInteriorClosureNext
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (A : Finset (EligibleInteriorColor χ U X)) :
    Finset (EligibleInteriorColor χ U X) := by
  classical
  exact A ∪ Finset.univ.filter (fun c =>
    ∃ f : HostEdge n, EdgeInside X f.val ∧ χ f = c.val ∧
      ∃ z w : X, f.val = s(z.val, w.val) ∧
        ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
          (EligibleInteriorColorDeletion χ U X s₀ (A : Set (EligibleInteriorColor χ U X)))).Reachable z w)

/-- The literal finite-palette recurrence, starting from the supplied seed. -/
noncomputable def eligibleInteriorClosureStages
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X)) :
    ℕ → Finset (EligibleInteriorColor χ U X)
  | 0 => S₀
  | i + 1 => eligibleInteriorClosureNext χ U X s₀ (eligibleInteriorClosureStages χ U X s₀ S₀ i)

theorem eligibleInteriorClosureStages_mono
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X)) :
    Monotone (eligibleInteriorClosureStages χ U X s₀ S₀) := by
  classical
  intro i j hij
  exact Nat.le_induction (m := i)
    (P := fun k _ => eligibleInteriorClosureStages χ U X s₀ S₀ i ⊆
      eligibleInteriorClosureStages χ U X s₀ S₀ k)
    (by intro c hc; exact hc)
    (fun k _ ih c hc => by
      change c ∈ eligibleInteriorClosureStages χ U X s₀ S₀ k ∪ Finset.univ.filter _
      exact Finset.mem_union.mpr (Or.inl (ih hc)))
    j hij

/-- Derived recurrence/rank facts needed by the original-slot descent caller.
The witness assertion excludes the outside sentinel N+1. -/
structure EligibleInteriorCumulativeBirthRank
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X))
    (N : ℕ) (ρ : EligibleInteriorColor χ U X → ℕ) : Prop where
  cumulative_monotone : Monotone (eligibleInteriorClosureStages χ U X s₀ S₀)
  seed_subset : ∀ i, S₀ ⊆ eligibleInteriorClosureStages χ U X s₀ S₀ i
  bounded : ∀ c, ρ c ≤ N + 1
  zero_iff : ∀ c, ρ c = 0 ↔ c ∈ S₀
  mem_iff : ∀ c j, j ≤ N →
    (ρ c ≤ j ↔ c ∈ eligibleInteriorClosureStages χ U X s₀ S₀ j)
  outside_iff : ∀ c, ρ c = N + 1 ↔ c ∉ eligibleInteriorClosureStages χ U X s₀ S₀ N
  lower_eq : ∀ j, 0 < j → j ≤ N + 1 →
    {c : EligibleInteriorColor χ U X | ρ c < j} =
      (eligibleInteriorClosureStages χ U X s₀ S₀ (j - 1) : Set (EligibleInteriorColor χ U X))
  birth_witness : ∀ c, 0 < ρ c → ρ c ≤ N →
    ∃ f : HostEdge n, EdgeInside X f.val ∧ χ f = c.val ∧
      ∃ z w : X, f.val = s(z.val, w.val) ∧
        ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
          (EligibleInteriorColorDeletion χ U X s₀ {d | ρ d < ρ c})).Reachable z w

/-- Construct least membership ranks through N, assign outside colors N+1,
and derive every positive birth witness directly from the actual recurrence. -/
theorem exists_original_eligible_interior_cumulative_birth_rank
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X))
    (N : ℕ) :
    ∃ ρ : EligibleInteriorColor χ U X → ℕ, EligibleInteriorCumulativeBirthRank χ U X s₀ S₀ N ρ := by
  classical
  let A := eligibleInteriorClosureStages χ U X s₀ S₀
  let ρ : EligibleInteriorColor χ U X → ℕ := fun c =>
    if hc : c ∈ A N then
      Nat.find (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩)
    else N + 1
  have hmono : Monotone A := eligibleInteriorClosureStages_mono χ U X s₀ S₀
  have hmem : ∀ c j, j ≤ N → (ρ c ≤ j ↔ c ∈ A j) := by
    intro c j hj
    by_cases hc : c ∈ A N
    · have hρ : ρ c = Nat.find (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) := by
        simp only [ρ, dite_eq_left hc]
      rw [hρ]
      constructor
      · intro hle
        exact hmono hle (Nat.find_spec (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩))
      · intro hborn
        exact Nat.find_min' (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) hborn
    · have hρ : ρ c = N + 1 := by simp only [ρ, dite_eq_right hc]
      constructor
      · intro hle
        omega
      · intro hborn
        exact False.elim (hc (hmono hj hborn))
  have hlower : ∀ j, 0 < j → j ≤ N + 1 →
      {c : EligibleInteriorColor χ U X | ρ c < j} =
        (A (j - 1) : Set (EligibleInteriorColor χ U X)) := by
    intro j hj hNj
    ext c
    change ρ c < j ↔ c ∈ A (j - 1)
    have hpre : j - 1 ≤ N := by omega
    constructor
    · intro hc
      exact (hmem c (j - 1) hpre).mp (by omega)
    · intro hc
      have hle := (hmem c (j - 1) hpre).mpr hc
      omega
  refine ⟨ρ, ?_⟩
  refine
    { cumulative_monotone := hmono
      seed_subset := ?_
      bounded := ?_
      zero_iff := ?_
      mem_iff := hmem
      outside_iff := ?_
      lower_eq := hlower
      birth_witness := ?_ }
  · intro i
    exact hmono (Nat.zero_le i)
  · intro c
    by_cases hc : c ∈ A N
    · have hρ : ρ c = Nat.find (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) := by
        simp only [ρ, dite_eq_left hc]
      have hle := Nat.find_min' (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) hc
      omega
    · simpa only [ρ, dite_eq_right hc] using (Nat.le_refl (N + 1))
  · intro c
    have hzero := hmem c 0 (Nat.zero_le N)
    change ρ c ≤ 0 ↔ c ∈ S₀ at hzero
    constructor
    · intro hc
      exact hzero.mp (by omega)
    · intro hc
      have hle := hzero.mpr hc
      omega
  · intro c
    constructor
    · intro hsent hc
      have hle := (hmem c N (Nat.le_refl N)).mpr hc
      omega
    · intro hc
      have hcA : c ∉ A N := hc
      simp only [ρ, dite_eq_right hcA]
  · intro c hpos hNc
    have hcA : c ∈ A (ρ c) := (hmem c (ρ c) hNc).mp (Nat.le_refl (ρ c))
    have hpre : ρ c - 1 ≤ N := by omega
    have hcNot : c ∉ A (ρ c - 1) := by
      intro hc
      have hle := (hmem c (ρ c - 1) hpre).mpr hc
      omega
    have hsucc : ρ c = (ρ c - 1) + 1 := by omega
    rw [hsucc] at hcA
    change c ∈ A (ρ c - 1) ∪ Finset.univ.filter _ at hcA
    rcases Finset.mem_union.mp hcA with hcOld | hcNew
    · exact False.elim (hcNot hcOld)
    · have hw := (Finset.mem_filter.mp hcNew).2
      rcases hw with ⟨f, hf, hfc, z, w, hfv, hcross⟩
      refine ⟨f, hf, hfc, z, w, hfv, ?_⟩
      rw [hlower (ρ c) hpos (by omega)]
      exact hcross

end ErdosProblems.PathUpperReduction
