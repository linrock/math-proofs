module

public import CommonOutsideNeighbors1105
public import CycleChordPath1105
public import EndpointAttachment1105
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Two distinguished actual outsiders suffice for the same
original-graph cover assembly. Only their successor contacts toggle; arbitrary
other outsiders need no degree or toggle hypothesis. Their contacts are forced
inside the first outsider's actual contact set by original path freedom. No common half, desired cover, chord-free half, supplied path or coloring
assumption is introduced.
-/

namespace ErdosProblems.PathUpperReduction.TwoOutsiderCycleCover1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CommonOutsideNeighbors1105
open ErdosProblems.PathUpperReduction.CycleChordPath1105
open ErdosProblems.PathUpperReduction.EndpointAttachment1105

/-- Only the two distinguished outsiders require alternating contacts.
All other actual outsiders may have smaller contact sets and lower degrees. -/
theorem exists_actual_cover_of_two_outsider_toggles {V : Type*} {n d : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (hsize : n + 3 = 2 * d) (hfree : (pathGraph (n + 5)).Free G)
    (u v : V) (hu : u ∉ Set.range c) (hv : v ∉ Set.range c) (hne : u ≠ v)
    (htoggleu : ∀ i : Fin (n + 3), G.Adj u (c (i + 1)) ↔ ¬G.Adj u (c i))
    (htogglev : ∀ i : Fin (n + 3), G.Adj v (c (i + 1)) ↔ ¬G.Adj v (c i))
    (houtside : ∀ x y, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y) :
    ∃ A : Finset V, A.card = d ∧ G.IsVertexCover (A : Set V) := by
  classical
  let P : Fin (n + 3) → Prop := fun i => G.Adj u (c i)
  let N : Finset (Fin (n + 3)) := Finset.univ.filter P
  let M : Finset (Fin (n + 3)) := Finset.univ.filter (fun i => ¬P i)
  let σ : Equiv.Perm (Fin (n + 3)) := finRotate (n + 3)
  have hσtoggle (i : Fin (n + 3)) : P (σ i) ↔ ¬P i := by
    simpa only [P, σ, finRotate_apply] using htoggleu i
  have himage : N.image σ = M := by
    ext j
    simp only [N, M, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩ hσi
      exact (hσtoggle i).mp hσi hi
    · intro hj
      refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
      by_contra hi
      have hP := (hσtoggle (σ.symm j)).mpr hi
      rw [σ.apply_symm_apply] at hP
      exact hj hP
  have hMcard : M.card = N.card := by
    rw [← himage]
    exact Finset.card_image_of_injective N σ.injective
  have hsum : N.card + M.card = n + 3 := by
    simpa only [N, M, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) P)
  have hNcard : N.card = d := by omega
  have hcontained (z : V) (hz : z ∉ Set.range c) (i : Fin (n + 3)) :
      G.Adj z (c i) → G.Adj u (c i) := by
    intro hzi
    by_cases hzu : z = u
    · subst z
      exact hzi
    · by_contra hnui
      have hus : G.Adj u (c (i + 1)) := (htoggleu i).mpr hnui
      exact (successor_contacts_incompatible_of_free G c hfree z u hz hu hzu i)
        ⟨hzi, hus⟩
  have hcommonv (i : Fin (n + 3)) : G.Adj v (c i) ↔ G.Adj u (c i) := by
    have he := outside_contact_sets_agree_of_toggles G c hfree v u hv hu hne.symm
      htogglev htoggleu
    exact Set.ext_iff.mp he i
  let A : Finset V := N.image c
  have hAcard : A.card = d := by
    calc A.card = N.card := Finset.card_image_of_injective N c.injective
         _ = d := hNcard
  have hAmem (i : Fin (n + 3)) : c i ∈ A ↔ P i := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have he : j = i := c.injective hji
      subst j
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  have hnoBB (r s : Fin (n + 3)) (hr : ¬P r) (hs : ¬P s) :
      ¬G.Adj (c r) (c s) := by
    intro hchord
    have hrs : r ≠ s := by
      intro he
      exact hchord.ne (congrArg c he)
    obtain ⟨p, hp0, hplast, hprange⟩ :=
      path_of_actual_cycle_chord G c r s hrs hchord
    have hup : u ∉ Set.range p := by rw [hprange]; exact hu
    have hvp : v ∉ Set.range p := by rw [hprange]; exact hv
    have hleft : G.Adj u (p 0) := by
      rw [hp0]
      exact (htoggleu r).mpr hr
    have hright : G.Adj (p (Fin.last (n + 2))) v := by
      rw [hplast]
      exact ((hcommonv (s + 1)).mpr ((htoggleu s).mpr hs)).symm
    exact (endpoint_contacts_incompatible_of_free G (n + 2) hfree p u v
      hup hvp hne) ⟨hleft, hright⟩
  refine ⟨A, hAcard, ?_⟩
  intro x y hxy
  by_cases hxA : x ∈ A
  · exact Or.inl hxA
  by_cases hyA : y ∈ A
  · exact Or.inr hyA
  exfalso
  by_cases hxc : x ∈ Set.range c
  · obtain ⟨r, rfl⟩ := hxc
    have hr : ¬P r := fun h => hxA ((hAmem r).mpr h)
    by_cases hyc : y ∈ Set.range c
    · obtain ⟨s, rfl⟩ := hyc
      exact hnoBB r s (hr) (fun h => hyA ((hAmem s).mpr h)) hxy
    · exact hr (hcontained y hyc r hxy.symm)
  · by_cases hyc : y ∈ Set.range c
    · obtain ⟨s, rfl⟩ := hyc
      exact hyA ((hAmem s).mpr (hcontained x hxc s hxy))
    · exact houtside x y hxc hyc hxy

end ErdosProblems.PathUpperReduction.TwoOutsiderCycleCover1105
