module

public import CycleNewColors
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
The exact finite palette of a complete-graph coloring after deleting a vertex,
and transfer of no-rainbow copies to that deletion. This is the induction
interface for the cycle upper bound; no structural bound on new colors is used.
-/

namespace ErdosProblems.AntiRamseyCycleNewColors

open SimpleGraph

variable {m : ℕ} {C : Type*} [DecidableEq C]

/-- Pull back a complete-graph coloring while skipping one vertex. -/
def deletedColoring (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (v : Fin (m + 1)) : TopEdgeLabeling (Fin m) C :=
  TopEdgeLabeling.pullback χ v.succAboveEmb

/-- The edges avoiding `v` are exactly the images of the edges of the
complete graph on `Fin m` under the skipped-vertex embedding. -/
theorem avoidingEdges_eq_image (v : Fin (m + 1)) :
    (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin (m + 1))).edgeSet =>
      v ∉ e.val)) =
    (Finset.univ : Finset ((⊤ : SimpleGraph (Fin m)).edgeSet)).image
      (SimpleGraph.Embedding.completeGraph v.succAboveEmb).toHom.mapEdgeSet := by
  ext e
  constructor
  · intro he
    have hnot : v ∉ e.val := (Finset.mem_filter.mp he).2
    rcases e with ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | hf a b =>
      have ha : a ≠ v := by
        intro hav
        apply hnot
        rw [← hav]
        exact Sym2.mem_mk_left a b
      have hb : b ≠ v := by
        intro hbv
        apply hnot
        rw [← hbv]
        exact Sym2.mem_mk_right a b
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq ha
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hb
      have hab : a ≠ b := by
        have hadj : (⊤ : SimpleGraph (Fin (m + 1))).Adj a b :=
          (SimpleGraph.mem_edgeSet ⊤).mp hz
        exact (SimpleGraph.top_adj a b).mp hadj
      have hij : i ≠ j := by
        intro h
        apply hab
        calc
          a = v.succAbove i := hi.symm
          _ = v.succAbove j := by rw [h]
          _ = b := hj
      let e' : (⊤ : SimpleGraph (Fin m)).edgeSet :=
        ⟨s(i, j), (SimpleGraph.mem_edgeSet ⊤).mpr
          ((SimpleGraph.top_adj i j).mpr hij)⟩
      apply Finset.mem_image.mpr
      refine ⟨e', Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      change Sym2.map v.succAbove (s(i, j)) = s(a, b)
      simp only [Sym2.map_mk, hi, hj]
  · intro he
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change v ∉ Sym2.map v.succAbove e'.val
    induction e'.val using Sym2.inductionOn with
    | hf i j =>
      simp only [Sym2.map_mk, Sym2.mem_iff, not_or]
      exact ⟨Fin.ne_succAbove v i, Fin.ne_succAbove v j⟩

/-- The deletion color set in the recurrence is the realized palette of the
pulled-back complete-graph labeling. -/
theorem colorsAfterDeleting_eq_usedColors_deletedColoring
    (χ : TopEdgeLabeling (Fin (m + 1)) C) (v : Fin (m + 1)) :
    colorsAfterDeleting χ v = usedColors (deletedColoring χ v) := by
  let f : (⊤ : SimpleGraph (Fin (m + 1))).edgeSet → C := χ
  let g : (⊤ : SimpleGraph (Fin m)).edgeSet → C := deletedColoring χ v
  rw [colorsAfterDeleting, avoidingEdges_eq_image]
  change ((Finset.univ : Finset ((⊤ : SimpleGraph (Fin m)).edgeSet)).image
      (SimpleGraph.Embedding.completeGraph v.succAboveEmb).toHom.mapEdgeSet).image f =
    (Finset.univ : Finset ((⊤ : SimpleGraph (Fin m)).edgeSet)).image g
  rw [Finset.image_image]
  rfl

/-- Relabel precisely the colors realized by an edge labeling to a
`Fin p` palette, where `p` is their number. -/
noncomputable def realizedPaletteColoring (ψ : TopEdgeLabeling (Fin m) C) :
    TopEdgeLabeling (Fin m) (Fin (usedColors ψ).card) :=
  fun e => (usedColors ψ).equivFin
    ⟨ψ e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

theorem realizedPaletteColoring_surjective (ψ : TopEdgeLabeling (Fin m) C) :
    Function.Surjective (realizedPaletteColoring ψ) := by
  intro i
  let c : usedColors ψ := (usedColors ψ).equivFin.symm i
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp c.property
  refine ⟨e, ?_⟩
  change (usedColors ψ).equivFin ⟨ψ e, _⟩ = i
  rw [← (usedColors ψ).equivFin.apply_symm_apply i]
  apply congrArg (usedColors ψ).equivFin
  apply Subtype.ext
  exact he

/-- Relabeling a restricted coloring by its realized palette preserves
absence of rainbow copies of any graph. -/
theorem noRainbowCopy_realizedPaletteColoring {α : Type*} (H : SimpleGraph α)
    (ψ : TopEdgeLabeling (Fin m) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom ψ) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬IsRainbow f.toHom (realizedPaletteColoring ψ) := by
  intro f hr
  apply hno f
  intro e₁ e₂ heq
  apply hr
  change realizedPaletteColoring ψ (f.toHom.mapEdgeSet e₁) =
    realizedPaletteColoring ψ (f.toHom.mapEdgeSet e₂)
  unfold realizedPaletteColoring
  apply congrArg (usedColors ψ).equivFin
  apply Subtype.ext
  exact heq

omit [DecidableEq C] in
/-- A no-rainbow copy on the deletion would compose with the skipped-vertex
embedding to give one in the original complete graph. -/
theorem noRainbowCopy_deletedColoring {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬IsRainbow f.toHom (deletedColoring χ v) := by
  intro f hr
  let g : H.Copy (⊤ : SimpleGraph (Fin (m + 1))) :=
    ((SimpleGraph.Embedding.completeGraph v.succAboveEmb).toCopy).comp f
  apply hno g
  intro e₁ e₂ heq
  apply hr
  have hcolor (e : H.edgeSet) :
      (EdgeLabeling.pullback χ g.toHom) e =
        (EdgeLabeling.pullback (deletedColoring χ v) f.toHom) e := by
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (g : α → Fin (m + 1)) e.val =
      Sym2.map v.succAbove (Sym2.map (f : α → Fin m) e.val)
    rw [Sym2.map_map]
    congr 1
  rw [hcolor e₁, hcolor e₂] at heq
  exact heq

/-- The deletion is an explicit surjective `Fin p` witness with precisely the
number of colors occurring on edges avoiding the removed vertex. -/
theorem deletedPalette_witness {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    ∃ φ : TopEdgeLabeling (Fin m) (Fin (colorsAfterDeleting χ v).card),
      Function.Surjective φ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom φ := by
  rw [colorsAfterDeleting_eq_usedColors_deletedColoring]
  exact ⟨realizedPaletteColoring (deletedColoring χ v),
    realizedPaletteColoring_surjective (deletedColoring χ v),
    noRainbowCopy_realizedPaletteColoring H (deletedColoring χ v)
      (noRainbowCopy_deletedColoring H χ hno v)⟩

/-- Any no-rainbow complete-graph coloring has at most the Formal Conjectures
anti-Ramsey number many realized colors, without a surjectivity assumption on
its original color type. -/
theorem usedColors_card_le_antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (ψ : TopEdgeLabeling (Fin m) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom ψ) :
    (usedColors ψ).card ≤ antiRamseyNum H m := by
  classical
  let A : Set ℕ :=
    {p | ∃ φ : TopEdgeLabeling (Fin m) (Fin p), Function.Surjective φ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom φ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin m)).edgeSet), ?_⟩
    intro p hp
    obtain ⟨φ, hφ, _⟩ := hp
    simpa using Fintype.card_le_of_surjective φ hφ
  have hmem : (usedColors ψ).card ∈ A :=
    ⟨realizedPaletteColoring ψ, realizedPaletteColoring_surjective ψ,
      noRainbowCopy_realizedPaletteColoring H ψ hno⟩
  change (usedColors ψ).card ≤ sSup A
  exact le_csSup hbounded hmem

/-- Exact deletion colors are bounded by the anti-Ramsey number on one fewer
vertex. This is the low-new-color induction interface for any finite graph. -/
theorem colorsAfterDeleting_card_le_antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    (colorsAfterDeleting χ v).card ≤ antiRamseyNum H m := by
  rw [colorsAfterDeleting_eq_usedColors_deletedColoring]
  exact usedColors_card_le_antiRamseyNum H (deletedColoring χ v)
    (noRainbowCopy_deletedColoring H χ hno v)

/-- The exact new-color recurrence and deletion witness give the numerical
induction inequality. A bound on the new-color term is a separate input. -/
theorem surjective_color_count_le_antiRamseyNum_add_newColors
    {α : Type*} [Fintype α] {q : ℕ}
    (H : SimpleGraph α) (χ : TopEdgeLabeling (Fin (m + 1)) (Fin q))
    (hχ : Function.Surjective χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    q ≤ antiRamseyNum H m + (newColors χ v).card := by
  calc
    q = (colorsAfterDeleting χ v).card + (newColors χ v).card :=
      surjective_color_count_delete_add_new χ hχ v
    _ ≤ antiRamseyNum H m + (newColors χ v).card :=
      Nat.add_le_add_right
        (colorsAfterDeleting_card_le_antiRamseyNum H χ hno v)
        (newColors χ v).card

end ErdosProblems.AntiRamseyCycleNewColors
