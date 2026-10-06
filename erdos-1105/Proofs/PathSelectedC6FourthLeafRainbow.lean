module

public import PathUpperRainbowBridge
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
A selected alternating six-cycle, a seventh vertex
with all three hub spokes selected, and a distinct eighth host vertex force
an original rainbow P8. No inducedness, S3 containment, extremality, or
no-rainbow premise is supplied. The actual same-color owner is avoided. The finite row construction adapts the checked K23 replacement template;
its nine-edge/six-opening instance is different from that six-spoke lemma.
-/

namespace ErdosProblems.PathSelectedC6FourthLeaf

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Cycle hubs are positions0,2,4; its leaves1,3,5. Vertex6 is fully
spoked to the hubs, and vertex7 is unrestricted. Additional edges are allowed. -/
structure RepresentativeC6FourthLeafOn {V : Type*}
    (G : SimpleGraph V) (u : Fin 8 → V) : Prop where
  c01 : G.Adj (u 0) (u 1)
  c12 : G.Adj (u 1) (u 2)
  c23 : G.Adj (u 2) (u 3)
  c34 : G.Adj (u 3) (u 4)
  c45 : G.Adj (u 4) (u 5)
  c50 : G.Adj (u 5) (u 0)
  y0 : G.Adj (u 6) (u 0)
  y2 : G.Adj (u 6) (u 2)
  y4 : G.Adj (u 6) (u 4)

def motifEdgeIndex (i : Fin 9) : Sym2 (Fin 8) :=
  if i = 0 then s(0, 1)
  else if i = 1 then s(1, 2)
  else if i = 2 then s(2, 3)
  else if i = 3 then s(3, 4)
  else if i = 4 then s(4, 5)
  else if i = 5 then s(5, 0)
  else if i = 6 then s(6, 0)
  else if i = 7 then s(6, 2)
  else s(6, 4)

theorem motifEdgeIndex_injective : Function.Injective motifEdgeIndex := by
  decide

theorem motifEdge_mem {V : Type*}
    (G : SimpleGraph V) (u : Fin 8 → V)
    (h : RepresentativeC6FourthLeafOn G u) (i : Fin 9) :
    Sym2.map u (motifEdgeIndex i) ∈ G.edgeSet := by
  fin_cases i
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c01
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c12
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c23
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c34
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c45
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c50
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.y0
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.y2
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.y4

/-- The six selected-edge rows are
[6,5,4,3,2,1], [7,2,3,4,5,0], [7,1,0,5,4,3],
[8,4,5,0,1,2], [8,3,2,1,0,5], [6,0,1,2,3,4]. -/
def chosenEdgeIndex (r : Fin 6) (i : Fin 6) : Fin 9 :=
  if r = 0 then
    if i = 0 then 6 else if i = 1 then 5 else if i = 2 then 4
    else if i = 3 then 3 else if i = 4 then 2 else 1
  else if r = 1 then
    if i = 0 then 7 else if i = 1 then 2 else if i = 2 then 3
    else if i = 3 then 4 else if i = 4 then 5 else 0
  else if r = 2 then
    if i = 0 then 7 else if i = 1 then 1 else if i = 2 then 0
    else if i = 3 then 5 else if i = 4 then 4 else 3
  else if r = 3 then
    if i = 0 then 8 else if i = 1 then 4 else if i = 2 then 5
    else if i = 3 then 0 else if i = 4 then 1 else 2
  else if r = 4 then
    if i = 0 then 8 else if i = 1 then 3 else if i = 2 then 2
    else if i = 3 then 1 else if i = 4 then 0 else 5
  else
    if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 1
    else if i = 3 then 2 else if i = 4 then 3 else 4

theorem choose_avoids {E : Type*}
    (d : Fin 9 → E) (hd : Function.Injective d) (old : E)
    (j : Fin 9) (hj : old = d j) (r : Fin 6)
    (hr : ∀ i, j ≠ chosenEdgeIndex r i) :
    ∀ i, old ≠ d (chosenEdgeIndex r i) := by
  intro i
  rw [hj]
  exact hd.ne (hr i)

/-- All six cycle-owner cases and all three y-spoke cases, plus every owner
outside those nine actual selected edges. No owner premise is supplied. -/
theorem avoid_one {E : Type*}
    (d : Fin 9 → E) (hd : Function.Injective d) (old : E) :
    ∃ row : Fin 6, ∀ i : Fin 6, old ≠ d (chosenEdgeIndex row i) := by
  classical
  by_cases h0 : old = d 0
  · exact ⟨0, choose_avoids d hd old 0 h0 0 (by decide)⟩
  by_cases h1 : old = d 1
  · exact ⟨1, choose_avoids d hd old 1 h1 1 (by decide)⟩
  by_cases h2 : old = d 2
  · exact ⟨2, choose_avoids d hd old 2 h2 2 (by decide)⟩
  by_cases h3 : old = d 3
  · exact ⟨3, choose_avoids d hd old 3 h3 3 (by decide)⟩
  by_cases h4 : old = d 4
  · exact ⟨4, choose_avoids d hd old 4 h4 4 (by decide)⟩
  by_cases h5 : old = d 5
  · exact ⟨5, choose_avoids d hd old 5 h5 5 (by decide)⟩
  by_cases h6 : old = d 6
  · exact ⟨1, choose_avoids d hd old 6 h6 1 (by decide)⟩
  by_cases h7 : old = d 7
  · exact ⟨0, choose_avoids d hd old 7 h7 0 (by decide)⟩
  by_cases h8 : old = d 8
  · exact ⟨0, choose_avoids d hd old 8 h8 0 (by decide)⟩
  refine ⟨0, ?_⟩
  intro i
  fin_cases i <;> simp_all [chosenEdgeIndex]

/-- Every order starts at w7,y6 and opens the same selected C6 at the
cycle edge whose index is row. Its first cycle vertex is a hub. -/
def openOrderIndex (r : Fin 6) (i : Fin 8) : Fin 8 :=
  if i = 0 then 7
  else if i = 1 then 6
  else if r = 0 then
    if i = 2 then 0 else if i = 3 then 5 else if i = 4 then 4
    else if i = 5 then 3 else if i = 6 then 2 else 1
  else if r = 1 then
    if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4
    else if i = 5 then 5 else if i = 6 then 0 else 1
  else if r = 2 then
    if i = 2 then 2 else if i = 3 then 1 else if i = 4 then 0
    else if i = 5 then 5 else if i = 6 then 4 else 3
  else if r = 3 then
    if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 0
    else if i = 5 then 1 else if i = 6 then 2 else 3
  else if r = 4 then
    if i = 2 then 4 else if i = 3 then 3 else if i = 4 then 2
    else if i = 5 then 1 else if i = 6 then 0 else 5
  else
    if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2
    else if i = 5 then 3 else if i = 6 then 4 else 5

theorem openOrderIndex_injective (r : Fin 6) :
    Function.Injective (openOrderIndex r) := by
  fin_cases r <;> decide

/-- One exact owner-avoiding Copy bridge for the original coloring.
The motif has nine selected edges; no favorable representative is required. -/
theorem rainbow_path_eight_of_representative_c6_and_fourth_leaf {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (u : Fin 8 → Fin n) (hu : Function.Injective u)
    (h : RepresentativeC6FourthLeafOn (selectedGraph χ r) u) :
    ∃ f : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : HostEdge n :=
    ⟨s(u 7, u 6),
      (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
        ((top_adj _ _).mpr (hu.ne (by decide)))⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let r' : RepresentativeChoice χ := r.replace e
  let L : SimpleGraph (Fin n) := selectedGraph χ r
  let L' : SimpleGraph (Fin n) := selectedGraph χ r'
  let d : Fin 9 → Sym2 (Fin n) := fun i => Sym2.map u (motifEdgeIndex i)
  have hd : Function.Injective d := by
    intro i j hij
    apply motifEdgeIndex_injective
    apply Sym2.map.injective hu
    simpa [d] using hij
  obtain ⟨row, hrow⟩ := avoid_one d hd old
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hretained (i : Fin 9) (hne : old ≠ d i) : d i ∈ L'.edgeSet := by
    have he : d i ∈ L.edgeSet := by
      simpa [d, L] using motifEdge_mem L u h i
    have hed : d i ∈ (L.deleteEdges {old}).edgeSet := by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he, by simpa using hne.symm⟩
    exact SimpleGraph.edgeSet_mono hle hed
  have hchord : L'.Adj (u 7) (u 6) := by
    have he := replacedEdge_mem χ r e
    simpa [L', r', e] using he
  let w : Fin 8 → Fin n := u ∘ openOrderIndex row
  have hw : Function.Injective w := hu.comp (openOrderIndex_injective row)
  have hmotifStep (i : Fin 6) :
      L'.Adj (w (Fin.succ (Fin.castSucc i))) (w (Fin.succ (Fin.succ i))) := by
    have hval :
        s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) =
          d (chosenEdgeIndex row i) := by
      fin_cases row <;> fin_cases i <;>
        simp [w, d, openOrderIndex, chosenEdgeIndex, motifEdgeIndex,
          Sym2.map_mk, Sym2.eq_swap]
    change s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) ∈ L'.edgeSet
    rw [hval]
    exact hretained (chosenEdgeIndex row i) (hrow i)
  have hstep (i : Fin 7) : L'.Adj (w i.castSucc) (w i.succ) := by
    fin_cases i
    · simpa [w, openOrderIndex] using hchord
    · simpa using hmotifStep 0
    · simpa using hmotifStep 1
    · simpa using hmotifStep 2
    · simpa using hmotifStep 3
    · simpa using hmotifStep 4
    · simpa using hmotifStep 5
  let φ : (pathGraph 8) →g L' :=
    ⟨w, by
      intro i j hij
      rcases pathGraph_adj.mp hij with hij | hji
      · have hi7 : i.val < 7 := by have hj8 := j.isLt; omega
        let t : Fin 7 := ⟨i.val, hi7⟩
        have hi : i = t.castSucc := Fin.ext rfl
        have hj : j = t.succ := Fin.ext hij.symm
        rw [hi, hj]
        exact hstep t
      · have hj7 : j.val < 7 := by have hi8 := i.isLt; omega
        let t : Fin 7 := ⟨j.val, hj7⟩
        have hj : j = t.castSucc := Fin.ext rfl
        have hi : i = t.succ := Fin.ext hji.symm
        rw [hi, hj]
        exact (hstep t).symm⟩
  let f : (pathGraph 8).Copy L' := ⟨φ, hw⟩
  refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
  simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

end ErdosProblems.PathSelectedC6FourthLeaf
