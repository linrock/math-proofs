module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import PathSetIncidence

@[expose] public section

/-!
Any complete-graph coloring whose edges outside a fixed small prefix use only
an `ε`-color palette excludes a rainbow long path.
-/

namespace ErdosProblems.PathSetLower

open SimpleGraph

def pathEdge (m : ℕ) (i : Fin m) : (pathGraph (m + 1)).edgeSet :=
  ⟨s(i.castSucc, i.succ), by
    rw [mem_edgeSet]
    apply pathGraph_adj.mpr
    left
    simp⟩

theorem pathEdge_injective (m : ℕ) : Function.Injective (pathEdge m) := by
  intro i j he
  have hs := congrArg Subtype.val he
  change s(i.castSucc, i.succ) = s(j.castSucc, j.succ) at hs
  rcases Sym2.eq_iff.mp hs with h | h
  · apply Fin.ext
    have hv := congrArg Fin.val h.1
    simpa using hv
  · have hv₁ := congrArg Fin.val h.1
    have hv₂ := congrArg Fin.val h.2
    simp at hv₁ hv₂
    omega

/-- A copied path cannot be rainbow when all edges away from a prefix of
`t` host vertices have colors in one palette of size `ε`, with
`2t + ε < m` where `m` is the number of path edges. -/
theorem noRainbowPath_of_smallOutsidePalette {m n t ε : ℕ} {C : Type*}
    (hε : 0 < ε) (hgap : 2 * t + ε < m)
    (χ : TopEdgeLabeling (Fin n) C) (palette : Fin ε → C)
    (hχ : ∀ a b : Fin n, (hab : a ≠ b) →
      t ≤ a.val → t ≤ b.val →
      ∃ z : Fin ε, χ.get a b ((top_adj a b).2 hab) = palette z) :
    ∀ f : (pathGraph (m + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ := by
  classical
  intro f hrainbow
  change Function.Injective (EdgeLabeling.pullback χ f.toHom) at hrainbow
  let S : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun v => (f v).val < t)
  have hS : S.card ≤ t := by
    let g : S → Fin t := fun v =>
      ⟨(f v.1).val, (Finset.mem_filter.mp v.2).2⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply f.injective
      apply Fin.ext
      change (⟨(f a.1).val, _⟩ : Fin t) = ⟨(f b.1).val, _⟩ at hab
      exact congrArg (fun x : Fin t => x.val) hab
    simpa using Fintype.card_le_of_injective g hg
  have hcolor (i : Fin m) (hi : i ∈ pathAvoiding m S) :
      ∃ z : Fin ε,
        (EdgeLabeling.pullback χ f.toHom) (pathEdge m i) = palette z := by
    have hav : ¬ (i.castSucc ∈ S ∨ i.succ ∈ S) := by
      exact (Finset.mem_filter.mp
        (show i ∈ Finset.univ.filter
          (fun q : Fin m => ¬ (q.castSucc ∈ S ∨ q.succ ∈ S)) from hi)).2
    have hl : t ≤ (f i.castSucc).val := by
      have hn : ¬ (f i.castSucc).val < t := by
        intro hlt
        exact hav (Or.inl (by simp [S, hlt]))
      omega
    have hr : t ≤ (f i.succ).val := by
      have hn : ¬ (f i.succ).val < t := by
        intro hlt
        exact hav (Or.inr (by simp [S, hlt]))
      omega
    have hne : f i.castSucc ≠ f i.succ := by
      apply f.injective.ne
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    obtain ⟨z, hz⟩ := hχ (f i.castSucc) (f i.succ) hne hl hr
    refine ⟨z, ?_⟩
    simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
      EdgeLabeling.get, pathEdge] using hz
  let color (i : Fin m) : Fin ε :=
    if hi : i ∈ pathAvoiding m S then Classical.choose (hcolor i hi)
    else ⟨0, hε⟩
  have hcolor_eq (i : Fin m) (hi : i ∈ pathAvoiding m S) :
      (EdgeLabeling.pullback χ f.toHom) (pathEdge m i) = palette (color i) := by
    dsimp [color]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hcolor i hi)
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    pathAvoiding_repeated_color m t ε S color hS hgap
  have hpull :
      (EdgeLabeling.pullback χ f.toHom) (pathEdge m i) =
        (EdgeLabeling.pullback χ f.toHom) (pathEdge m j) := by
    rw [hcolor_eq i hi, hcolor_eq j hj, heq]
  exact hij ((pathEdge_injective m) (hrainbow hpull))

end ErdosProblems.PathSetLower
