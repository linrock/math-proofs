module

public import CycleChordPath1105
public import CycleEdgeContact1105
public import CycleInsertion1105
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Contact-predecessor cover contradiction and cycle insertion: combines
`CycleChordPath1105`, `CycleEdgeContact1105`, and `CycleInsertion1105` to
extend a cycle through a fresh vertex when the seed cover lower bound holds.
-/

namespace ErdosProblems.PathUpperReduction.KernelCycleInsertion1105

open SimpleGraph Finset

/-- A strict actual seed-cover gap forces an actual predecessor chord and
therefore a spanning original path with two actual contacts to the new vertex.
The contact count is the count on the FULL supplied cycle range. -/
theorem spanning_contact_path_of_cover_gap
    {V : Type*} [DecidableEq V] {n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : (cycleGraph (n + 3)).Copy G)
    (z : V) (K : Finset V) (j t : ℕ)
    (hK : ∀ v ∈ K, v ∈ Set.range c)
    (hcover : ∀ X : Finset V,
      (∀ u ∈ K, ∀ v ∈ K, G.Adj u v → u ∈ X ∨ v ∈ X) → t ≤ X.card)
    (hcount : (Finset.univ.filter (fun i : Fin (n + 3) => G.Adj z (c i))).card = j)
    (hgap : n + 3 - j < t) :
    ∃ p : (pathGraph (n + 3)).Copy G,
      G.Adj z (p 0) ∧ G.Adj z (p (Fin.last (n + 2))) ∧
      Set.range p = Set.range c := by
  classical
  let N : Finset (Fin (n + 3)) := univ.filter (fun i => G.Adj z (c i))
  let P : Finset (Fin (n + 3)) := univ.filter (fun i => G.Adj z (c (i + 1)))
  let σ : Equiv.Perm (Fin (n + 3)) := finRotate (n + 3)
  have hPN : P.image σ = N := by
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hadj := (Finset.mem_filter.mp hi).2
      simpa only [σ, finRotate_apply] using hadj
    · intro ha
      refine ⟨σ.symm a, ?_, σ.apply_symm_apply a⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have he : σ.symm a + 1 = a := by
        simpa only [σ, finRotate_apply] using σ.apply_symm_apply a
      rw [he]
      exact (Finset.mem_filter.mp ha).2
  have hPcard : P.card = j := by
    calc
      P.card = (P.image σ).card := (Finset.card_image_of_injective P σ.injective).symm
      _ = N.card := congrArg Finset.card hPN
      _ = j := hcount
  let Q : Finset (Fin (n + 3)) := univ \ P
  let X : Finset V := Q.image c
  have hXcard : X.card = n + 3 - j := by
    calc
      X.card = Q.card := Finset.card_image_of_injective Q c.injective
      _ = (univ : Finset (Fin (n + 3))).card - P.card :=
        Finset.card_sdiff_of_subset (Finset.subset_univ P)
      _ = n + 3 - j := by rw [Finset.card_univ, Fintype.card_fin, hPcard]
  have hex : ∃ r s : Fin (n + 3), r ∈ P ∧ s ∈ P ∧ G.Adj (c r) (c s) := by
    by_contra hno
    have hind (r s : Fin (n + 3)) (hr : r ∈ P) (hs : s ∈ P) :
        ¬G.Adj (c r) (c s) := by
      intro hadj
      exact hno ⟨r, s, hr, hs, hadj⟩
    have hXcover : ∀ u ∈ K, ∀ v ∈ K, G.Adj u v → u ∈ X ∨ v ∈ X := by
      intro u hu v hv huv
      obtain ⟨r, rfl⟩ := hK u hu
      obtain ⟨s, rfl⟩ := hK v hv
      by_cases hr : r ∈ Q
      · exact Or.inl (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
      by_cases hs : s ∈ Q
      · exact Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
      have hrP : r ∈ P := by
        by_contra hnot
        exact hr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      have hsP : s ∈ P := by
        by_contra hnot
        exact hs (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      exact (hind r s hrP hsP huv).elim
    have hbound := hcover X hXcover
    rw [hXcard] at hbound
    omega
  obtain ⟨r, s, hr, hs, hrsAdj⟩ := hex
  have hrs : r ≠ s := by
    intro he
    exact hrsAdj.ne (congrArg c he)
  obtain ⟨p, hp0, hpLast, hpRange⟩ :=
    CycleChordPath1105.path_of_actual_cycle_chord G c r s hrs hrsAdj
  refine ⟨p, ?_, ?_, hpRange⟩
  · rw [hp0]
    exact (Finset.mem_filter.mp hr).2
  · rw [hpLast]
    exact (Finset.mem_filter.mp hs).2

/-- The derived spanning contact path closes through the ACTUAL fresh vertex.
The new cycle support is exactly the complete old Copy range plus that vertex,
so a later restoration can reuse its genuine full-prefix contact count. -/
theorem cycle_with_exact_support_of_cover_gap
    {V : Type*} [DecidableEq V] {n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : (cycleGraph (n + 3)).Copy G)
    (z : V) (K : Finset V) (j t : ℕ)
    (hK : ∀ v ∈ K, v ∈ Set.range c)
    (hcover : ∀ X : Finset V,
      (∀ u ∈ K, ∀ v ∈ K, G.Adj u v → u ∈ X ∨ v ∈ X) → t ≤ X.card)
    (hcount : (Finset.univ.filter (fun i : Fin (n + 3) => G.Adj z (c i))).card = j)
    (hgap : n + 3 - j < t) (hz : z ∉ Set.range c) :
    ∃ D : G.Walk z z, D.IsCycle ∧ D.length = n + 4 ∧
      ∀ v : V, v ∈ D.support ↔ v = z ∨ v ∈ Set.range c := by
  classical
  obtain ⟨p, hleft, hright, hprange⟩ :=
    spanning_contact_path_of_cover_gap G c z K j t hK hcover hcount hgap
  obtain ⟨P, hP, hPLength, hPSupport⟩ :=
    CycleEdgeContact1105.walk_of_path_copy G p
  have hzP : z ∉ P.support := by
    intro hmem
    have hrange := (hPSupport z).mp hmem
    rw [hprange] at hrange
    exact hz hrange
  let D : G.Walk z z := SimpleGraph.Walk.cons hleft (P.concat hright.symm)
  obtain ⟨hD, hDLength⟩ := CycleInsertion1105.cycle_of_fresh_endpoint_contact
    G P hP z (by omega) hzP hleft hright.symm
  refine ⟨D, hD, ?_, ?_⟩
  · change (SimpleGraph.Walk.cons hleft (P.concat hright.symm)).length = n + 4
    omega
  · intro v
    simp only [D, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    rw [hPSupport v, hprange]
    constructor
    · rintro (hv | hv | hv)
      · exact Or.inl hv
      · exact Or.inr hv
      · exact Or.inl hv
    · rintro (hv | hv)
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)

end ErdosProblems.PathUpperReduction.KernelCycleInsertion1105
