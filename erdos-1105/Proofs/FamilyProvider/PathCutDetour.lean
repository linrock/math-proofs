module

public import EndpointProvider.TwoConnector58

@[expose] public section

/-!
Its exact Erdos58.TwoConnector.trim_between_sets is applied, not reproved. The short deletion-walk lift follows that module's path_avoiding_deleted body,
but uses only the single deletion premise needed here, rather than all deletions.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Deletion connectivity at one internal position of an injective ordering
gives a simple detour across that position. The detour contacts the entire
ordered vertex range only at its two attachments. No adjacency of successive
ordered vertices, ambient finiteness, or connectivity after other deletions is
assumed. -/
theorem exists_internal_cut_detour
    {V : Type*} {G : SimpleGraph V} {s : ℕ}
    (p : Fin (s + 1) → V) (hp : Function.Injective p)
    (i : Fin (s + 1)) (hi0 : (0 : Fin (s + 1)) < i)
    (hilast : i < Fin.last s)
    (hdel : (G.induce {w | w ≠ p i}).Connected) :
    ∃ a b : Fin (s + 1), a < i ∧ i < b ∧
      ∃ q : G.Walk (p a) (p b), q.IsPath ∧
        (∀ z, z ∈ q.support → z ≠ p i) ∧
        (∀ j, p j ∈ q.support → j = a ∨ j = b) ∧
        (∀ z, z ∈ q.support → z ∈ Set.range p → z = p a ∨ z = p b) := by
  classical
  have h0 : p (0 : Fin (s + 1)) ≠ p i := by
    intro h
    exact (ne_of_lt hi0) (hp h)
  have hlast : p (Fin.last s) ≠ p i := by
    intro h
    exact (ne_of_gt hilast) (hp h)
  obtain ⟨deleted⟩ := hdel ⟨p 0, h0⟩ ⟨p (Fin.last s), hlast⟩
  let initial : G.Walk (p 0) (p (Fin.last s)) :=
    deleted.map (Embedding.induce {w | w ≠ p i}).toHom
  have initial_avoids : ∀ z, z ∈ initial.bypass.support → z ≠ p i := by
    intro z hz
    have hzinitial := initial.support_bypass_subset_support hz
    change z ∈ (deleted.map (Embedding.induce {w | w ≠ p i}).toHom).support at hzinitial
    rw [Walk.support_map] at hzinitial
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hzinitial
    exact u.property
  let A : Set V := p '' {j | j < i}
  let B : Set V := p '' {j | i < j}
  have hA0 : p (0 : Fin (s + 1)) ∈ A := ⟨0, hi0, rfl⟩
  have hBlast : p (Fin.last s) ∈ B := ⟨Fin.last s, hilast, rfl⟩
  obtain ⟨u, hu, v, hv, q, hq, hsub, hA, hB⟩ :=
    Erdos58.TwoConnector.trim_between_sets initial.bypass initial.bypass_isPath
      A B hA0 hBlast
  change u ∈ p '' {j | j < i} at hu
  change v ∈ p '' {j | i < j} at hv
  rcases hu with ⟨a, ha, rfl⟩
  rcases hv with ⟨b, hb, rfl⟩
  have hcontacts : ∀ j, p j ∈ q.support → j = a ∨ j = b := by
    intro j hj
    rcases lt_trichotomy j i with hji | hji | hij
    · exact Or.inl (hp (hA (p j) hj ⟨j, hji, rfl⟩))
    · subst j
      exact (initial_avoids (p i) (hsub (p i) hj) rfl).elim
    · exact Or.inr (hp (hB (p j) hj ⟨j, hij, rfl⟩))
  refine ⟨a, b, ha, hb, q, hq, ?_, hcontacts, ?_⟩
  · intro z hz
    exact initial_avoids z (hsub z hz)
  · intro z hz hzp
    rcases hzp with ⟨j, rfl⟩
    rcases hcontacts j hz with hja | hjb
    · exact Or.inl (congrArg p hja)
    · exact Or.inr (congrArg p hjb)

end ErdosProblems.PathUpperReduction
