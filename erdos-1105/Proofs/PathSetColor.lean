module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import PathIncidentCount
public import PathSetPalette

@[expose] public section

/-!
Yuan's fixed-set coloring gives each complete-graph edge meeting the first
`t` vertices its own label, and uses one or two fresh labels on the other
edges. The palette is realized by two explicit edges among the host vertices
outside the fixed set.
-/

namespace ErdosProblems.PathSetLower

open SimpleGraph

def completeEdge {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  ⟨s(u, v), (top_adj u v).2 huv⟩

theorem completeEdge_not_incident {t n : ℕ}
    (u v : Fin n) (huv : u ≠ v)
    (hu : t ≤ u.val) (hv : t ≤ v.val) :
    completeEdge u v huv ∉ incidentEdgeFinset t n := by
  intro hmem
  have hval : u.val < t ∨ v.val < t :=
    (mem_incidentEdgeFinset_mk t n u v ((top_adj u v).2 huv)).mp hmem
  omega

def hostAt {t n : ℕ} (h : t + 3 ≤ n) (i : Fin 3) : Fin n :=
  ⟨t + i.val, by omega⟩

/-- An outside edge that receives color zero. -/
def outsideZeroEdge {t n : ℕ} (h : t + 3 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  completeEdge (hostAt h 0) (hostAt h 2) (by
    intro he
    have hv := congrArg Fin.val he
    simp [hostAt] at hv)

/-- A distinct outside edge that receives color one if there are two labels. -/
def outsideOneEdge {t n : ℕ} (h : t + 3 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  completeEdge (hostAt h 0) (hostAt h 1) (by
    intro he
    have hv := congrArg Fin.val he
    simp [hostAt] at hv)

theorem outsideZeroEdge_not_incident {t n : ℕ} (h : t + 3 ≤ n) :
    outsideZeroEdge h ∉ incidentEdgeFinset t n := by
  apply completeEdge_not_incident
  · simp [hostAt]
  · simp [hostAt]

theorem outsideOneEdge_not_incident {t n : ℕ} (h : t + 3 ≤ n) :
    outsideOneEdge h ∉ incidentEdgeFinset t n := by
  apply completeEdge_not_incident
  · simp [hostAt]
  · simp [hostAt]

theorem outsideEdges_ne {t n : ℕ} (h : t + 3 ≤ n) :
    outsideZeroEdge h ≠ outsideOneEdge h := by
  intro he
  have hs := congrArg Subtype.val he
  change s(hostAt h 0, hostAt h 2) = s(hostAt h 0, hostAt h 1) at hs
  rcases Sym2.eq_iff.mp hs with hsame | hswap
  · have hv := congrArg Fin.val hsame.2
    simp [hostAt] at hv
  · have hv := congrArg Fin.val hswap.1
    simp [hostAt] at hv

abbrev RawSetColors (t n ε : ℕ) : Type :=
  (incidentEdgeFinset t n) ⊕ Fin ε

noncomputable def rawSetColor {t n ε : ℕ} (hε : 0 < ε)
    (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    TopEdgeLabeling (Fin n) (RawSetColors t n ε) := by
  classical
  exact fun e =>
    if he : e ∈ incidentEdgeFinset t n then
      Sum.inl ⟨e, he⟩
    else Sum.inr (twoPaletteColor hε e₁ e)

theorem rawSetColor_surjective {t n ε : ℕ}
    (hε : 0 < ε) (hε₂ : ε ≤ 2)
    (e₀ e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (h₀ : e₀ ∉ incidentEdgeFinset t n)
    (h₁ : e₁ ∉ incidentEdgeFinset t n)
    (hne : e₀ ≠ e₁) :
    Function.Surjective (rawSetColor (t := t) hε e₁) := by
  classical
  intro z
  cases z with
  | inl e =>
      refine ⟨e.1, ?_⟩
      simp [rawSetColor, e.2]
  | inr q =>
      obtain ⟨e, he, hq⟩ :=
        twoPaletteColor_surjective_on_pair hε hε₂ e₀ e₁ hne q
      refine ⟨e, ?_⟩
      rcases he with rfl | rfl
      · simp [rawSetColor, h₀, hq]
      · simp [rawSetColor, h₁, hq]

theorem rawSetColors_card (t n ε : ℕ) (h : t ≤ n) :
    Fintype.card (RawSetColors t n ε) =
      t.choose 2 + t * (n - t) + ε := by
  classical
  change Fintype.card ((incidentEdgeFinset t n) ⊕ Fin ε) =
    t.choose 2 + t * (n - t) + ε
  rw [Fintype.card_sum, Fintype.card_coe (incidentEdgeFinset t n),
    Fintype.card_fin, incidentEdgeFinset_card t n h]

theorem rawSetColor_get_outside {t n ε : ℕ}
    (hε : 0 < ε) (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (u v : Fin n) (huv : u ≠ v)
    (hu : t ≤ u.val) (hv : t ≤ v.val) :
    (rawSetColor (t := t) hε e₁).get u v ((top_adj u v).2 huv) =
      Sum.inr (twoPaletteColor hε e₁ (completeEdge u v huv)) := by
  have hnot := completeEdge_not_incident u v huv hu hv
  change (rawSetColor (t := t) hε e₁) (completeEdge u v huv) =
    Sum.inr (twoPaletteColor hε e₁ (completeEdge u v huv))
  simp only [rawSetColor, dite_eq_right hnot]

noncomputable def setColor {t n ε : ℕ} (h : t ≤ n) (hε : 0 < ε)
    (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    TopEdgeLabeling (Fin n) (Fin (t.choose 2 + t * (n - t) + ε)) :=
  fun e => Fin.cast (rawSetColors_card t n ε h)
    ((Fintype.equivFin (RawSetColors t n ε)) (rawSetColor (t := t) hε e₁ e))

theorem setColor_surjective {t n ε : ℕ} (h : t ≤ n)
    (hε : 0 < ε) (hε₂ : ε ≤ 2)
    (e₀ e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (h₀ : e₀ ∉ incidentEdgeFinset t n)
    (h₁ : e₁ ∉ incidentEdgeFinset t n)
    (hne : e₀ ≠ e₁) :
    Function.Surjective (setColor h hε e₁) := by
  classical
  intro z
  let d : RawSetColors t n ε :=
    (Fintype.equivFin (RawSetColors t n ε)).symm
      (Fin.cast (rawSetColors_card t n ε h).symm z)
  obtain ⟨e, he⟩ := rawSetColor_surjective (t := t) hε hε₂ e₀ e₁ h₀ h₁ hne d
  refine ⟨e, ?_⟩
  change Fin.cast (rawSetColors_card t n ε h)
    ((Fintype.equivFin (RawSetColors t n ε)) (rawSetColor (t := t) hε e₁ e)) = z
  rw [he]
  simp [d]

/-- The exact fresh palette inside the relabeled `Fin` color type. -/
noncomputable def freshSetColor {t n ε : ℕ} (h : t ≤ n) (z : Fin ε) :
    Fin (t.choose 2 + t * (n - t) + ε) :=
  Fin.cast (rawSetColors_card t n ε h)
    ((Fintype.equivFin (RawSetColors t n ε)) (Sum.inr z))

theorem setColor_get_outside {t n ε : ℕ} (h : t ≤ n)
    (hε : 0 < ε) (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (u v : Fin n) (huv : u ≠ v)
    (hu : t ≤ u.val) (hv : t ≤ v.val) :
    (setColor h hε e₁).get u v ((top_adj u v).2 huv) =
      freshSetColor h (twoPaletteColor hε e₁ (completeEdge u v huv)) := by
  have hraw := rawSetColor_get_outside hε e₁ u v huv hu hv
  simpa [setColor, freshSetColor, EdgeLabeling.get] using
    congrArg (fun c : RawSetColors t n ε =>
      Fin.cast (rawSetColors_card t n ε h)
        ((Fintype.equivFin (RawSetColors t n ε)) c)) hraw

end ErdosProblems.PathSetLower
