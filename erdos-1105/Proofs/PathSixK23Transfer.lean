module

public import PathUpperRainbowBridge
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
Six selected spokes of a K₂,₃ on five named vertices, and a distinct sixth
host vertex, force a rainbow six-vertex path in the original complete host.
Four path orders avoid any one selected edge lost when the outside chord is
inserted into a representative choice. This is a restricted auxiliary result.
-/

namespace ErdosProblems.AntiRamseyPathSixK23Transfer

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- The hubs are `u 0,u 1`, the leaves are `u 2,u 3,u 4`, and `u 5`
is the outside vertex. Additional selected edges are allowed. -/
structure RepresentativeK23On {V : Type*}
    (G : SimpleGraph V) (u : Fin 6 → V) : Prop where
  hub0_b1 : G.Adj (u 0) (u 2)
  hub0_b2 : G.Adj (u 0) (u 3)
  hub0_b3 : G.Adj (u 0) (u 4)
  hub1_b1 : G.Adj (u 1) (u 2)
  hub1_b2 : G.Adj (u 1) (u 3)
  hub1_b3 : G.Adj (u 1) (u 4)

def k23SpokeIndex (i : Fin 6) : Sym2 (Fin 6) :=
  if i = 0 then s(0, 2)
  else if i = 1 then s(0, 3)
  else if i = 2 then s(0, 4)
  else if i = 3 then s(1, 2)
  else if i = 4 then s(1, 3)
  else s(1, 4)

theorem k23SpokeIndex_injective : Function.Injective k23SpokeIndex := by
  decide

theorem k23Spoke_mem {V : Type*}
    (G : SimpleGraph V) (u : Fin 6 → V)
    (h : RepresentativeK23On G u) (i : Fin 6) :
    Sym2.map u (k23SpokeIndex i) ∈ G.edgeSet := by
  fin_cases i
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub0_b1
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub0_b2
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub0_b3
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub1_b1
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub1_b2
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub1_b3

/-- The four rows use spokes `[0,1,4,5]`, `[0,2,5,4]`,
`[3,4,1,2]`, and `[3,5,2,1]` after their common outside chord. -/
def k23ChosenSpokeIndex (r : Fin 4) (i : Fin 4) : Fin 6 :=
  if r = 0 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else 5
  else if r = 1 then
    if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 5 else 4
  else if r = 2 then
    if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 1 else 2
  else
    if i = 0 then 3 else if i = 1 then 5 else if i = 2 then 2 else 1

theorem k23_choose_avoids {E : Type*}
    (d : Fin 6 → E) (hd : Function.Injective d) (old : E)
    (j : Fin 6) (h : old = d j) (r : Fin 4)
    (hr : ∀ i, j ≠ k23ChosenSpokeIndex r i) :
    ∀ i, old ≠ d (k23ChosenSpokeIndex r i) := by
  intro i
  rw [h]
  exact hd.ne (hr i)

/-- One of four spoke rows avoids an arbitrary edge among six distinct
spokes. The assertion also covers an edge outside the six-spoke set. -/
theorem k23_avoid_one {E : Type*}
    (d : Fin 6 → E) (hd : Function.Injective d) (old : E) :
    ∃ r : Fin 4, ∀ i : Fin 4, old ≠ d (k23ChosenSpokeIndex r i) := by
  classical
  by_cases h0 : old = d 0
  · exact ⟨2, k23_choose_avoids d hd old 0 h0 2 (by decide)⟩
  by_cases h1 : old = d 1
  · exact ⟨1, k23_choose_avoids d hd old 1 h1 1 (by decide)⟩
  by_cases h2 : old = d 2
  · exact ⟨0, k23_choose_avoids d hd old 2 h2 0 (by decide)⟩
  by_cases h3 : old = d 3
  · exact ⟨0, k23_choose_avoids d hd old 3 h3 0 (by decide)⟩
  by_cases h4 : old = d 4
  · exact ⟨3, k23_choose_avoids d hd old 4 h4 3 (by decide)⟩
  by_cases h5 : old = d 5
  · exact ⟨2, k23_choose_avoids d hd old 5 h5 2 (by decide)⟩
  refine ⟨0, ?_⟩
  intro i
  fin_cases i <;> simp_all [k23ChosenSpokeIndex]

/-- Four orders are `w,x,a,y,b,z`, `w,x,a,z,b,y`,
`w,x,b,y,a,z`, and `w,x,b,z,a,y`. -/
def k23OrderIndex (r : Fin 4) (i : Fin 6) : Fin 6 :=
  if i = 0 then 5
  else if i = 1 then 2
  else if r = 0 then
    if i = 2 then 0 else if i = 3 then 3 else if i = 4 then 1 else 4
  else if r = 1 then
    if i = 2 then 0 else if i = 3 then 4 else if i = 4 then 1 else 3
  else if r = 2 then
    if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 0 else 4
  else
    if i = 2 then 1 else if i = 3 then 4 else if i = 4 then 0 else 3

theorem k23OrderIndex_injective (r : Fin 4) :
    Function.Injective (k23OrderIndex r) := by
  fin_cases r <;> decide

theorem k23Path_adj_cases {i j : Fin 6}
    (h : (pathGraph 6).Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
    (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  fin_cases i <;> fin_cases j <;> simp_all [pathGraph_adj]

/-- A selected K₂,₃ on five vertices and a distinct sixth host vertex
force a literal rainbow six-vertex path for every representative choice. -/
theorem rainbow_path_six_of_representative_k23 {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeK23On (selectedGraph χ r) u) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : HostEdge n :=
    ⟨s(u 5, u 2), (top_adj _ _).mpr (hu.ne (by decide))⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let r' : RepresentativeChoice χ := r.replace e
  let L : SimpleGraph (Fin n) := selectedGraph χ r
  let L' : SimpleGraph (Fin n) := selectedGraph χ r'
  let d : Fin 6 → Sym2 (Fin n) := fun i => Sym2.map u (k23SpokeIndex i)
  have hd : Function.Injective d := by
    intro i j hij
    apply k23SpokeIndex_injective
    apply Sym2.map.injective hu
    simpa [d] using hij
  obtain ⟨row, hrow⟩ := k23_avoid_one d hd old
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hnewSpoke (i : Fin 6) (hne : old ≠ d i) : d i ∈ L'.edgeSet := by
    have he : d i ∈ L.edgeSet := by
      simpa [d, L] using k23Spoke_mem L u h i
    have hed : d i ∈ (L.deleteEdges {old}).edgeSet := by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he, by simpa using hne.symm⟩
    exact (SimpleGraph.edgeSet_mono hle) hed
  have hchord : L'.Adj (u 5) (u 2) := by
    have he := replacedEdge_mem χ r e
    simpa [L', r', e] using he
  let w : Fin 6 → Fin n := u ∘ k23OrderIndex row
  have hw : Function.Injective w := hu.comp (k23OrderIndex_injective row)
  have hspokeStep (i : Fin 4) :
      L'.Adj (w (Fin.succ (Fin.castSucc i))) (w (Fin.succ (Fin.succ i))) := by
    have hval :
        s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) =
          d (k23ChosenSpokeIndex row i) := by
      fin_cases row <;> fin_cases i <;>
        simp [w, d, k23OrderIndex, k23ChosenSpokeIndex,
          k23SpokeIndex, Sym2.map_mk, Sym2.eq_swap]
    change s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) ∈ L'.edgeSet
    rw [hval]
    exact hnewSpoke (k23ChosenSpokeIndex row i) (hrow i)
  have hstep (i : Fin 5) :
      L'.Adj (w (Fin.castSucc i)) (w (Fin.succ i)) := by
    fin_cases i
    · simpa [w, k23OrderIndex] using hchord
    · simpa using hspokeStep 0
    · simpa using hspokeStep 1
    · simpa using hspokeStep 2
    · simpa using hspokeStep 3
  let φ : (pathGraph 6) →g L' :=
    ⟨w, by
      intro i j hij
      rcases k23Path_adj_cases hij with h01 | h10 | h12 | h21 | h23 |
        h32 | h34 | h43 | h45 | h54
      · rcases h01 with ⟨rfl, rfl⟩
        simpa using hstep 0
      · rcases h10 with ⟨rfl, rfl⟩
        simpa using (hstep 0).symm
      · rcases h12 with ⟨rfl, rfl⟩
        simpa using hstep 1
      · rcases h21 with ⟨rfl, rfl⟩
        simpa using (hstep 1).symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using hstep 2
      · rcases h32 with ⟨rfl, rfl⟩
        simpa using (hstep 2).symm
      · rcases h34 with ⟨rfl, rfl⟩
        simpa using hstep 3
      · rcases h43 with ⟨rfl, rfl⟩
        simpa using (hstep 3).symm
      · rcases h45 with ⟨rfl, rfl⟩
        simpa using hstep 4
      · rcases h54 with ⟨rfl, rfl⟩
        simpa using (hstep 4).symm⟩
  let f : (pathGraph 6).Copy L' := ⟨φ, hw⟩
  refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
  simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

/-- The literal no-rainbow host premise excludes this six-spoke selected
shape for every representative choice. -/
theorem no_representative_k23_of_no_rainbow_path_six {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (u : Fin 6 → Fin n) (hu : Function.Injective u) :
    ¬ RepresentativeK23On (selectedGraph χ r) u := by
  intro h
  obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_k23 χ r u hu h
  exact hno f hf

end ErdosProblems.AntiRamseyPathSixK23Transfer
