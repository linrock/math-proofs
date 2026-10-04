module

public import MonochromaticPairs546


@[expose] public section

/-!
# Gluing a deleted vertex set into a monochromatic pair

This is the graph-copy interface used in Sudakov's Lemma 3.1. A selected finite
vertex set can be mapped into the clique side of a monochromatic pair, while
an existing non-induced copy of the deleted graph maps the remaining vertices
into its reservoir. All edges across the two parts are available.
-/

namespace Erdos546

open SimpleGraph

/-- Glue a supplied residual copy into the reservoir of a monochromatic pair.
The complement is a complement of the selected vertex set, not of the graph. -/
theorem isContained_of_monoPair_deleted_copy {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (A : Finset V) (X Y : Finset W)
    (hp : MonoPair H X Y) (hcard : A.card ≤ X.card)
    (hcopy : (G.induce ((A : Set V)ᶜ)).IsContained (H.induce (Y : Set W))) :
    G.IsContained H := by
  classical
  obtain ⟨c⟩ := hcopy
  let a : A ↪ X :=
    (Function.Embedding.nonempty_of_card_le (by simpa using hcard)).some
  let f : V → W := fun v =>
    if hv : v ∈ A then (a ⟨v, hv⟩ : W)
    else (c ⟨v, hv⟩ : W)
  have hX : ∀ v, v ∈ A → f v ∈ X := by
    intro v hv
    simp [f, hv]
  have hY : ∀ v, v ∉ A → f v ∈ Y := by
    intro v hv
    simp [f, hv]
  have hf : Function.Injective f := by
    intro v w h
    by_cases hv : v ∈ A
    · by_cases hw : w ∈ A
      · have he : a ⟨v, hv⟩ = a ⟨w, hw⟩ :=
          Subtype.ext (by simpa [f, hv, hw] using h)
        exact congrArg Subtype.val (a.injective he)
      · have hwY : f v ∈ Y := by
          rw [h]
          exact hY w hw
        exact (Finset.disjoint_left.mp hp.1 (hX v hv) hwY).elim
    · by_cases hw : w ∈ A
      · have hvY : f w ∈ Y := h ▸ hY v hv
        exact (Finset.disjoint_left.mp hp.1 (hX w hw) hvY).elim
      · have he : c ⟨v, hv⟩ = c ⟨w, hw⟩ :=
          Subtype.ext (by simpa [f, hv, hw] using h)
        exact congrArg Subtype.val (c.injective he)
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro v w hvw
  by_cases hv : v ∈ A
  · by_cases hw : w ∈ A
    · exact hp.2.1 (hX v hv) (hX w hw) (fun he => hvw.ne (hf he))
    · exact hp.2.2 (f v) (hX v hv) (f w) (hY w hw)
  · by_cases hw : w ∈ A
    · exact (hp.2.2 (f w) (hX w hw) (f v) (hY v hv)).symm
    · have he : (G.induce ((A : Set V)ᶜ)).Adj ⟨v, hv⟩ ⟨w, hw⟩ := hvw
      simpa [f, hv, hw] using c.toHom.map_adj he

/-- The construction still applies when no vertices are selected for the clique. -/
theorem isContained_of_monoPair_empty_deleted_copy {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (X Y : Finset W)
    (_hp : MonoPair H X Y)
    (hcopy : (G.induce ((∅ : Set V)ᶜ)).IsContained (H.induce (Y : Set W))) :
    G.IsContained H := by
  have hG : G.IsContained (G.induce ((∅ : Set V)ᶜ)) := by
    refine ⟨⟨⟨fun v => ⟨v, by simp⟩, ?_⟩, ?_⟩⟩
    · intro v w hvw
      exact hvw
    · intro v w he
      exact congrArg Subtype.val he
  exact hG.trans (hcopy.trans ⟨SimpleGraph.Copy.induce H (Y : Set W)⟩)

/-- When every source vertex is selected, the deleted graph has no vertices,
so no nonempty reservoir or separate residual-copy premise is needed. -/
theorem isContained_of_monoPair_card {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (X Y : Finset W)
    (hp : MonoPair H X Y) (hcard : Fintype.card V ≤ X.card) : G.IsContained H := by
  classical
  let _ : IsEmpty ↥(((Finset.univ : Finset V) : Set V)ᶜ) :=
    ⟨fun v => by simpa using v.property⟩
  apply isContained_of_monoPair_deleted_copy G H Finset.univ X Y hp
  · simpa using hcard
  · exact SimpleGraph.IsContained.of_isEmpty

end Erdos546
