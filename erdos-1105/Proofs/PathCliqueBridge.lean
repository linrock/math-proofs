module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import PathIndexIncidence

@[expose] public section

/-! The common outside color in the path clique construction forces a repeat. -/

namespace ErdosProblems.PathCliqueLower

open SimpleGraph

def pathEdgeGeneral (r : ℕ) (p : Fin (r + 1)) : (pathGraph (r + 2)).edgeSet :=
  ⟨s(p.castSucc, p.succ), by
    rw [mem_edgeSet]
    apply pathGraph_adj.mpr
    left
    simp⟩

theorem pathEdgeGeneral_injective (r : ℕ) :
    Function.Injective (pathEdgeGeneral r) := by
  intro p q he
  have hs := congrArg Subtype.val he
  change s(p.castSucc, p.succ) = s(q.castSucc, q.succ) at hs
  rcases Sym2.eq_iff.mp hs with h | h
  · apply Fin.ext
    have hv := congrArg Fin.val h.1
    simpa using hv
  · have hv₁ := congrArg Fin.val h.1
    have hv₂ := congrArg Fin.val h.2
    simp at hv₁ hv₂
    omega

theorem pathEdgeGeneral_commonColor {r n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (z : C)
    (hχ : ∀ a b : Fin n, (hab : a ≠ b) →
      (r ≤ a.val ∨ r ≤ b.val) →
      χ.get a b ((top_adj a b).2 hab) = z)
    (f : (pathGraph (r + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (p : Fin (r + 1))
    (houtside : r ≤ (f p.castSucc).val ∨ r ≤ (f p.succ).val) :
    (EdgeLabeling.pullback χ f.toHom) (pathEdgeGeneral r p) = z := by
  have hsource : p.castSucc ≠ p.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  have hne : f p.castSucc ≠ f p.succ := f.injective.ne hsource
  have hfresh := hχ (f p.castSucc) (f p.succ) hne houtside
  simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
    EdgeLabeling.get, pathEdgeGeneral] using hfresh

/-- If all complete-graph edges touching vertices outside the first `r` labels
have one common color, no path on `r + 2` vertices is rainbow. -/
theorem noRainbowPath_of_commonOutsideColor {r n : ℕ} {C : Type*}
    (hr : 1 ≤ r) (χ : TopEdgeLabeling (Fin n) C) (z : C)
    (hχ : ∀ a b : Fin n, (hab : a ≠ b) →
      (r ≤ a.val ∨ r ≤ b.val) →
      χ.get a b ((top_adj a b).2 hab) = z) :
    ∀ f : (pathGraph (r + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ := by
  intro f hf
  change Function.Injective (EdgeLabeling.pullback χ f.toHom) at hf
  obtain ⟨i, j, hij, hi, hj⟩ := two_vertices_outside_prefix f f.injective
  obtain ⟨p, q, hpq, hp, hq⟩ :=
    two_incident_path_edges_succ (m := r + 1) (by omega) i j hij
  have hcolor (t : Fin (r + 1))
      (ht : i = t.castSucc ∨ i = t.succ ∨ j = t.castSucc ∨ j = t.succ) :
      (EdgeLabeling.pullback χ f.toHom) (pathEdgeGeneral r t) = z := by
    apply pathEdgeGeneral_commonColor χ z hχ f t
    rcases ht with ht | ht | ht | ht
    · exact Or.inl (by simpa [ht] using hi)
    · exact Or.inr (by simpa [ht] using hi)
    · exact Or.inl (by simpa [ht] using hj)
    · exact Or.inr (by simpa [ht] using hj)
  exact hpq ((pathEdgeGeneral_injective r) (hf ((hcolor p hp).trans (hcolor q hq).symm)))

end ErdosProblems.PathCliqueLower
