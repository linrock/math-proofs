module

public import CycleFourNewWedge
public import CycleNewOutsideWitness
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Tactic

@[expose] public section

/-!
The literal no-rainbow C4 premise and two NEW colors at each vertex force
every selected NEW-representative edge color to be NEW at both endpoints.
The selected graph is locally a triangle at every vertex. No pair-sum,
surjectivity, n ≥ 4, or quotient-block hypothesis is needed.
-/

namespace ErdosProblems.AntiRamseyCycleFourNewTriangle

open SimpleGraph Finset
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow
open ErdosProblems.AntiRamseyCycleNewOutsideWitness
open ErdosProblems.AntiRamseyCycleFourNewWedge

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem newColorNeighbor_selectedColor
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin n)
    (c : newColors χ u) :
    selectedEdgeColor χ (newColorNeighbor_adj χ u c) = c.val := by
  have hedge :
      (⟨(selectedPair χ (newColorNeighbor_adj χ u c)).val,
        SimpleGraph.edgeSet_mono le_top
          (selectedPair χ (newColorNeighbor_adj χ u c)).property⟩ :
          (⊤ : SimpleGraph (Fin n)).edgeSet) =
      (⟨(newColorIncidenceEdge χ u c).val,
        SimpleGraph.edgeSet_mono le_top
          (newColorIncidenceEdge χ u c).property.1⟩ :
          (⊤ : SimpleGraph (Fin n)).edgeSet) := by
    apply Subtype.ext
    change s(u, newColorNeighbor χ u c) =
      (newColorIncidenceEdge χ u c).val
    exact (newColorIncidenceEdge_eq_pair χ u c).symm
  exact (congrArg χ hedge).trans (newColorIncidenceEdge_color χ u c)

theorem newColorNeighbor_selectedNEW
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin n)
    (c : newColors χ u) :
    selectedEdgeColor χ (newColorNeighbor_adj χ u c) ∈ newColors χ u := by
  rw [newColorNeighbor_selectedColor χ u c]
  exact c.property

/-- Choose one NEW-color-indexed selected neighbor other than a named
vertex. The chosen edge is oriented NEW at the current endpoint. -/
theorem exists_newColorNeighbor_ne
    (χ : TopEdgeLabeling (Fin n) C) (u v : Fin n)
    (hu : 2 ≤ (newColors χ u).card) :
    ∃ c : newColors χ u, newColorNeighbor χ u c ≠ v := by
  classical
  have hcap :
      ((newColorRepresentative χ).neighborFinset u ∩ ({v} : Finset (Fin n))).card ≤ 1 := by
    calc
      ((newColorRepresentative χ).neighborFinset u ∩ ({v} : Finset (Fin n))).card ≤
          ({v} : Finset (Fin n)).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 1 := by simp
  have hsmall :
      ((newColorRepresentative χ).neighborFinset u ∩ ({v} : Finset (Fin n))).card <
        (newColors χ u).card := by omega
  obtain ⟨c, hc⟩ := exists_newColorNeighbor_outside χ u {v} hsmall
  exact ⟨c, by simpa only [Finset.mem_singleton] using hc⟩

theorem selectedColor_eq_of_newColorNeighbor_eq
    (χ : TopEdgeLabeling (Fin n) C)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v)
    (c : newColors χ u) (hc : newColorNeighbor χ u c = v) :
    selectedEdgeColor χ huv = c.val := by
  have hedge : selectedPair χ huv =
      selectedPair χ (newColorNeighbor_adj χ u c) := by
    apply Subtype.ext
    change s(u, v) = s(u, newColorNeighbor χ u c)
    rw [hc]
  exact (congrArg (restrictedNewColor χ) hedge).trans
    (newColorNeighbor_selectedColor χ u c)

/-- Every selected color is NEW at its first endpoint. The high-NEW
cardinality rules out an edge selected only from the other endpoint. -/
theorem selectedColor_new_first
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) :
    selectedEdgeColor χ huv ∈ newColors χ u := by
  classical
  obtain ⟨d, hyu⟩ := exists_newColorNeighbor_ne χ v u (hnew v)
  let y : Fin n := newColorNeighbor χ v d
  have hvy : (newColorRepresentative χ).Adj v y :=
    newColorNeighbor_adj χ v d
  have hnewVY : selectedEdgeColor χ hvy ∈ newColors χ v :=
    newColorNeighbor_selectedNEW χ v d
  have hrange (c : newColors χ u) :
      newColorNeighbor χ u c = v ∨ newColorNeighbor χ u c = y := by
    by_cases hxv : newColorNeighbor χ u c = v
    · exact Or.inl hxv
    · have hux : (newColorRepresentative χ).Adj u (newColorNeighbor χ u c) :=
        newColorNeighbor_adj χ u c
      have hnewUX : selectedEdgeColor χ hux ∈ newColors χ u :=
        newColorNeighbor_selectedNEW χ u c
      exact Or.inr
        (selected_new_wedge_eq χ hno huv hux hvy hxv hyu hnewUX hnewVY)
  by_contra hnot
  have hconstant (c : newColors χ u) : newColorNeighbor χ u c = y := by
    rcases hrange c with hc | hc
    · have hcolor : selectedEdgeColor χ huv = c.val :=
        selectedColor_eq_of_newColorNeighbor_eq χ huv c hc
      have hnewUV : selectedEdgeColor χ huv ∈ newColors χ u := by
        rw [hcolor]
        exact c.property
      exact False.elim (hnot hnewUV)
    · exact hc
  have hinj : Function.Injective
      (fun _ : newColors χ u => (0 : Fin 1)) := by
    intro a b _
    exact newColorNeighbor_injective χ u
      ((hconstant a).trans (hconstant b).symm)
  have hcard : (newColors χ u).card ≤ 1 := by
    have h := Fintype.card_le_of_injective
      (fun _ : newColors χ u => (0 : Fin 1)) hinj
    simpa only [Fintype.card_coe, Fintype.card_fin] using h
  have hu2 := hnew u
  omega

/-- At k=4 with at least two NEW colors at each vertex, every edge
selected by the NEW representative has a host label NEW at *both*
endpoints. This strengthens the unconditional SOME-endpoint result. -/
theorem selected_edge_color_new_both
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) :
    selectedEdgeColor χ huv ∈ newColors χ u ∧
      selectedEdgeColor χ huv ∈ newColors χ v := by
  refine ⟨selectedColor_new_first χ hno hnew huv, ?_⟩
  have hswap : selectedEdgeColor χ huv.symm = selectedEdgeColor χ huv := by
    apply congrArg (restrictedNewColor χ)
    apply Subtype.ext
    change s(v, u) = s(u, v)
    exact Sym2.eq_swap
  have hsecond := selectedColor_new_first χ hno hnew huv.symm
  rw [hswap] at hsecond
  exact hsecond

/-- Every vertex of the selected NEW representative has exactly two
selected neighbors, which are themselves adjacent. This is the local
`K₃` structure before passing to connected-component supports. -/
theorem selected_vertex_triangle
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (u : Fin n) :
    ∃ v w : Fin n, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (newColorRepresentative χ).Adj u v ∧
      (newColorRepresentative χ).Adj u w ∧
      (newColorRepresentative χ).Adj v w ∧
      (∀ z : Fin n, (newColorRepresentative χ).Adj u z ↔ z = v ∨ z = w) := by
  classical
  have hpos : 0 < (newColors χ u).card := by
    have hu2 := hnew u
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  let c₀ : newColors χ u := ⟨c, hc⟩
  let v : Fin n := newColorNeighbor χ u c₀
  have huv : (newColorRepresentative χ).Adj u v :=
    newColorNeighbor_adj χ u c₀
  obtain ⟨d, hwu⟩ := exists_newColorNeighbor_ne χ v u (hnew v)
  let w : Fin n := newColorNeighbor χ v d
  have hvw : (newColorRepresentative χ).Adj v w :=
    newColorNeighbor_adj χ v d
  have hnewVW : selectedEdgeColor χ hvw ∈ newColors χ v :=
    newColorNeighbor_selectedNEW χ v d
  obtain ⟨a, hxv⟩ := exists_newColorNeighbor_ne χ u v (hnew u)
  let x : Fin n := newColorNeighbor χ u a
  have hux : (newColorRepresentative χ).Adj u x :=
    newColorNeighbor_adj χ u a
  have hnewUX : selectedEdgeColor χ hux ∈ newColors χ u :=
    newColorNeighbor_selectedNEW χ u a
  have hxw : x = w :=
    selected_new_wedge_eq χ hno huv hux hvw hxv hwu hnewUX hnewVW
  have huw : (newColorRepresentative χ).Adj u w := by
    simpa only [hxw] using hux
  have hvw' : v ≠ w := by
    intro heq
    exact hxv (hxw.trans heq.symm)
  have hall (z : Fin n) :
      (newColorRepresentative χ).Adj u z ↔ z = v ∨ z = w := by
    constructor
    · intro huz
      by_cases hzv : z = v
      · exact Or.inl hzv
      · have hnewUZ : selectedEdgeColor χ huz ∈ newColors χ u :=
          (selected_edge_color_new_both χ hno hnew huz).1
        exact Or.inr
          (selected_new_wedge_eq χ hno huv huz hvw hzv hwu hnewUZ hnewVW)
    · rintro (rfl | rfl)
      · exact huv
      · exact huw
  exact ⟨v, w, huv.ne, (huw.ne), hvw', huv, huw, hvw, hall⟩

/-- Under the same hypotheses, degree and NEW count are exactly two
at every selected vertex. -/
theorem selected_vertex_degree_new_card_two
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (u : Fin n) :
    (newColorRepresentative χ).degree u = 2 ∧
      (newColors χ u).card = 2 := by
  classical
  obtain ⟨v, w, huv, huw, hvw, _, _, _, hall⟩ :=
    selected_vertex_triangle χ hno hnew u
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  have hneighbor : G.neighborFinset u = {v, w} := by
    ext z
    simp only [G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    exact hall z
  have hdegree : G.degree u = 2 := by
    change (G.neighborFinset u).card = 2
    rw [hneighbor]
    simp [hvw]
  have hlow := hnew u
  have hhigh := newColorRepresentative_degree_ge_newColors χ u
  have hdegree' : (newColorRepresentative χ).degree u = 2 := hdegree
  refine ⟨hdegree, ?_⟩
  omega

/-- The three selected vertices of a triangle have no selected edge
to a fourth vertex. Every such edge would create a second NEW wedge. -/
theorem selected_triangle_no_outer_neighbors
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {u v w : Fin n}
    (huv : (newColorRepresentative χ).Adj u v)
    (huw : (newColorRepresentative χ).Adj u w)
    (hvw : (newColorRepresentative χ).Adj v w)
    (huw' : u ≠ w) (hvw' : v ≠ w) :
    (∀ z : Fin n, (newColorRepresentative χ).Adj u z → z = v ∨ z = w) ∧
    (∀ z : Fin n, (newColorRepresentative χ).Adj v z → z = u ∨ z = w) ∧
    (∀ z : Fin n, (newColorRepresentative χ).Adj w z → z = u ∨ z = v) := by
  have hnewUV := (selected_edge_color_new_both χ hno hnew huv).1
  have hnewUW := (selected_edge_color_new_both χ hno hnew huw).1
  have hnewVW := (selected_edge_color_new_both χ hno hnew hvw).1
  refine ⟨?_, ?_, ?_⟩
  · intro z huz
    by_cases hzv : z = v
    · exact Or.inl hzv
    · have hnewUZ := (selected_edge_color_new_both χ hno hnew huz).1
      exact Or.inr
        (selected_new_wedge_eq χ hno huv huz hvw hzv huw'.symm
          hnewUZ hnewVW)
  · intro z hvz
    by_cases hzu : z = u
    · exact Or.inl hzu
    · have hnewVZ := (selected_edge_color_new_both χ hno hnew hvz).1
      exact Or.inr
        (selected_new_wedge_eq χ hno huv.symm hvz huw hzu hvw'.symm
          hnewVZ hnewUW)
  · intro z hwz
    by_cases hzu : z = u
    · exact Or.inl hzu
    · have hnewWZ := (selected_edge_color_new_both χ hno hnew hwz).1
      exact Or.inr
        (selected_new_wedge_eq χ hno huw.symm hwz huv hzu hvw'
          hnewWZ hnewUV)

/-- Every connected component of the selected NEW representative has
exactly the support of one selected triangle. This is a component-order
statement, not yet a quotient block-color theorem. -/
theorem selected_component_is_triangle
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (D : (newColorRepresentative χ).ConnectedComponent) :
    ∃ u v w : Fin n, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      D.supp = ({u, v, w} : Set (Fin n)) ∧
      (newColorRepresentative χ).Adj u v ∧
      (newColorRepresentative χ).Adj u w ∧
      (newColorRepresentative χ).Adj v w := by
  classical
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  obtain ⟨u, huD⟩ := D.nonempty_supp
  obtain ⟨v, w, huv', huw', hvw', huv, huw, hvw, _⟩ :=
    selected_vertex_triangle χ hno hnew u
  obtain ⟨honlyU, honlyV, honlyW⟩ :=
    selected_triangle_no_outer_neighbors χ hno hnew
      huv huw hvw huw' hvw'
  let S : Set (Fin n) := {u, v, w}
  have hclosed : ∀ a b : Fin n, a ∈ S → G.Adj a b → b ∈ S := by
    intro a b ha hab
    have ha' : a = u ∨ a = v ∨ a = w := by
      simpa [S] using ha
    rcases ha' with rfl | rfl | rfl
    · rcases honlyU b hab with rfl | rfl <;> simp [S]
    · rcases honlyV b hab with rfl | rfl <;> simp [S]
    · rcases honlyW b hab with rfl | rfl <;> simp [S]
  have hgenS : ∀ z : Fin n, Relation.ReflTransGen G.Adj u z → z ∈ S := by
    intro z hz
    induction hz with
    | refl => simp [S]
    | tail _ hab ih => exact hclosed _ _ ih hab
  have hreachS (z : Fin n) (hz : G.Reachable u z) : z ∈ S :=
    hgenS z ((G.reachable_iff_reflTransGen u z).mp hz)
  have hsubset : D.supp ⊆ S := by
    intro z hz
    have hu : G.connectedComponentMk u = D :=
      (D.mem_supp_iff u).mp huD
    have hz' : G.connectedComponentMk z = D :=
      (D.mem_supp_iff z).mp hz
    have hreach : G.Reachable u z :=
      ConnectedComponent.eq.mp (hu.trans hz'.symm)
    exact hreachS z hreach
  have hsupset : S ⊆ D.supp := by
    intro z hz
    have hz' : z = u ∨ z = v ∨ z = w := by
      simpa [S] using hz
    rcases hz' with rfl | rfl | rfl
    · exact huD
    · exact D.mem_supp_of_adj_mem_supp huD huv
    · exact D.mem_supp_of_adj_mem_supp huD huw
  have hsupport : D.supp = S := Set.Subset.antisymm hsubset hsupset
  exact ⟨u, v, w, huv', huw', hvw', hsupport, huv, huw, hvw⟩

/-- The exact selected-component order at k=4 is three. -/
theorem selected_component_card_three
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (D : (newColorRepresentative χ).ConnectedComponent) :
    D.supp.ncard = 3 := by
  classical
  obtain ⟨u, v, w, huv, huw, hvw, hsupport, _, _, _⟩ :=
    selected_component_is_triangle χ hno hnew D
  rw [hsupport, Set.ncard_eq_toFinset_card]
  simp [huv, huw, hvw]

end ErdosProblems.AntiRamseyCycleFourNewTriangle
