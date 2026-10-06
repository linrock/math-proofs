module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
Auxiliary finite graph SOURCE: deleting distinct actual original bridge edges
of a connected graph leaves exactly one more component than deleted edges. Every deletion is an actual edge deletion. No count is a premise.
-/

universe u

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

/-- The two endpoint reachability sets after one edge deletion cover its old
component. This coverage does not require the edge to be a bridge. -/
theorem reachable_delete_edge_either_endpoint
    {V : Type u} (H : SimpleGraph V) (a b : V) {z : V}
    (haz : H.Reachable a z) :
    (H.deleteEdges {s(a, b)}).Reachable a z ∨
      (H.deleteEdges {s(a, b)}).Reachable b z := by
  let D := H.deleteEdges {s(a, b)}
  have hstep : ∀ x y, H.Adj x y →
      (D.Reachable a x ∨ D.Reachable b x) →
      (D.Reachable a y ∨ D.Reachable b y) := by
    intro x y hxy hx
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (SimpleGraph.Reachable.refl _)
      · exact Or.inl (SimpleGraph.Reachable.refl _)
    · have hdxy : D.Adj x y := SimpleGraph.deleteEdges_adj.mpr
        ⟨hxy, by simpa only [Set.mem_singleton_iff] using he⟩
      rcases hx with ha | hb
      · exact Or.inl (ha.trans hdxy.reachable)
      · exact Or.inr (hb.trans hdxy.reachable)
  have hwalk : ∀ {x y} (p : H.Walk x y),
      (D.Reachable a x ∨ D.Reachable b x) →
      (D.Reachable a y ∨ D.Reachable b y) := by
    intro x y p
    induction p with
    | nil => exact fun hx => hx
    | cons hxy p ih =>
        intro hx
        exact ih (hstep _ _ hxy hx)
  obtain ⟨p⟩ := haz
  exact hwalk p (Or.inl (SimpleGraph.Reachable.refl a))

/-- A walk in an old component different from the edge endpoints' component
survives the deletion. Actual adjacency joins the two old endpoints. -/
theorem reachable_delete_edge_of_other_component
    {V : Type u} (H : SimpleGraph V) {a b x y : V}
    (hab : H.Adj a b) (hxa : ¬ H.Reachable x a)
    (hxy : H.Reachable x y) :
    (H.deleteEdges {s(a, b)}).Reachable x y := by
  let D := H.deleteEdges {s(a, b)}
  have hstep : ∀ u v, H.Reachable x u → H.Adj u v → D.Reachable u v := by
    intro u v hxu huv
    have he : s(u, v) ≠ s(a, b) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxa hxu
      · exact hxa (hxu.trans hab.symm.reachable)
    exact (SimpleGraph.deleteEdges_adj.mpr
      ⟨huv, by simpa only [Set.mem_singleton_iff] using he⟩).reachable
  have hwalk : ∀ {u v} (p : H.Walk u v),
      H.Reachable x u → D.Reachable u v := by
    intro u v p
    induction p with
    | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
    | cons huv p ih =>
        intro hxu
        exact (hstep _ _ hxu huv).trans (ih (hxu.trans huv.reachable))
  obtain ⟨p⟩ := hxy
  exact hwalk p (SimpleGraph.Reachable.refl x)

theorem component_count_delete_bridge_pair
    {V : Type u} [Finite V] (H : SimpleGraph V) {a b : V}
    (hab : H.Adj a b) (hbridge : H.IsBridge s(a, b)) :
    Nat.card (H.deleteEdges {s(a, b)}).ConnectedComponent =
      Nat.card H.ConnectedComponent + 1 := by
  classical
  let D := H.deleteEdges {s(a, b)}
  let φ : D.ConnectedComponent → H.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map
      (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le (G := H) {s(a, b)}))
  let C₀ := H.connectedComponentMk a
  have hnot : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  have hcover : ∀ c : D.ConnectedComponent,
      φ c = C₀ → c = D.connectedComponentMk a ∨ c = D.connectedComponentMk b := by
    intro c
    refine c.ind ?_
    intro z hz
    change H.connectedComponentMk z = H.connectedComponentMk a at hz
    have haz : H.Reachable a z := (SimpleGraph.ConnectedComponent.exact hz).symm
    rcases reachable_delete_edge_either_endpoint H a b haz with ha | hb
    · exact Or.inl (SimpleGraph.ConnectedComponent.sound ha.symm)
    · exact Or.inr (SimpleGraph.ConnectedComponent.sound hb.symm)
  let ca : {c : D.ConnectedComponent // φ c = C₀} :=
    ⟨D.connectedComponentMk a, rfl⟩
  let cb : {c : D.ConnectedComponent // φ c = C₀} :=
    ⟨D.connectedComponentMk b, SimpleGraph.ConnectedComponent.sound hab.symm.reachable⟩
  have hcab : ca ≠ cb := by
    intro heq
    apply hnot
    apply SimpleGraph.ConnectedComponent.exact
    exact congrArg (fun q : {c : D.ConnectedComponent // φ c = C₀} => q.val) heq
  have hcard₀ : Nat.card {c : D.ConnectedComponent // φ c = C₀} = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨ca, cb, hcab, ?_⟩
    apply Set.ext
    intro q
    constructor
    · intro _
      trivial
    · intro _
      change q = ca ∨ q = cb
      rcases hcover q.val q.property with ha | hb
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr (Subtype.ext hb)
  have hsurj : Function.Surjective φ :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE
      (SimpleGraph.deleteEdges_le (G := H) {s(a, b)})
  have hcard_other : ∀ C : H.ConnectedComponent, C ≠ C₀ →
      Nat.card {c : D.ConnectedComponent // φ c = C} = 1 := by
    intro C hC
    have hsame : ∀ c d : D.ConnectedComponent, φ c = C → φ d = C → c = d := by
      intro c d
      refine c.ind ?_
      intro x
      refine d.ind ?_
      intro y hx hy
      change H.connectedComponentMk x = C at hx
      change H.connectedComponentMk y = C at hy
      have hxy : H.Reachable x y :=
        SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
      have hxa : ¬ H.Reachable x a := by
        intro hxa
        exact hC (hx.symm.trans (SimpleGraph.ConnectedComponent.sound hxa))
      exact SimpleGraph.ConnectedComponent.sound
        (reachable_delete_edge_of_other_component H hab hxa hxy)
    obtain ⟨c, hc⟩ := hsurj C
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨c, hc⟩, ?_⟩
    intro d
    exact Subtype.ext (hsame d.val c d.property hc)
  have hcards : ∀ C : H.ConnectedComponent,
      Nat.card {c : D.ConnectedComponent // φ c = C} = if C = C₀ then 2 else 1 := by
    intro C
    by_cases hC : C = C₀
    · subst C
      rw [ite_eq_left rfl]
      exact hcard₀
    · rw [ite_eq_right hC]
      exact hcard_other C hC
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  calc
    Nat.card D.ConnectedComponent =
        Nat.card (Σ C : H.ConnectedComponent, {c : D.ConnectedComponent // φ c = C}) :=
      Nat.card_congr ((Equiv.sigmaFiberEquiv φ).symm)
    _ = ∑ C : H.ConnectedComponent,
        Nat.card {c : D.ConnectedComponent // φ c = C} := Nat.card_sigma
    _ = ∑ C : H.ConnectedComponent, ((if C = C₀ then 1 else 0) + 1) := by
      apply Finset.sum_congr rfl
      intro C _
      rw [hcards C]
      by_cases hC : C = C₀
      · simp only [ite_eq_left hC]
      · simp only [ite_eq_right hC]
    _ = (∑ C : H.ConnectedComponent, if C = C₀ then 1 else 0) +
        (∑ _C : H.ConnectedComponent, 1) := Finset.sum_add_distrib
    _ = Nat.card H.ConnectedComponent + 1 := by
      simp [Nat.card_eq_fintype_card, Nat.add_comm]

/-- One actual bridge deletion increases the number of components by one.
The old graph is allowed to be disconnected. -/
theorem connected_component_count_delete_bridge
    {V : Type u} [Finite V] (H : SimpleGraph V) (e : Sym2 V)
    (he : e ∈ H.edgeSet) (hbridge : H.IsBridge e) :
    Nat.card (H.deleteEdges {e}).ConnectedComponent =
      Nat.card H.ConnectedComponent + 1 := by
  obtain ⟨a, b⟩ := e
  exact component_count_delete_bridge_pair H ((H.mem_edgeSet).mp he) hbridge

/-- Delete a finite set of distinct actual ORIGINAL bridges of one connected
graph. No connectedness is asserted for its intermediate deleted graphs. -/
theorem connected_component_count_delete_original_bridges
    {V : Type u} [Finite V] (G : SimpleGraph V) (hG : G.Connected)
    (A : Finset (Sym2 V))
    (hAedge : (A : Set (Sym2 V)) ⊆ G.edgeSet)
    (hAbridge : ∀ e ∈ A, G.IsBridge e) :
    Nat.card (G.deleteEdges (A : Set (Sym2 V))).ConnectedComponent = A.card + 1 := by
  classical
  revert hAedge hAbridge
  induction A using Finset.induction_on with
  | empty =>
      intro _ _
      rw [Finset.coe_empty, SimpleGraph.deleteEdges_empty, Finset.card_empty, Nat.zero_add]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨hG.preconnected.subsingleton_connectedComponent,
          Nonempty.map G.connectedComponentMk hG.nonempty⟩
  | @insert e A he ih =>
      intro hAedge hAbridge
      have hAedge' : (A : Set (Sym2 V)) ⊆ G.edgeSet :=
        fun _ hx => hAedge (Finset.mem_insert_of_mem hx)
      have hAbridge' : ∀ f ∈ A, G.IsBridge f :=
        fun f hf => hAbridge f (Finset.mem_insert_of_mem hf)
      have heedge : e ∈ (G.deleteEdges (A : Set (Sym2 V))).edgeSet := by
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨hAedge (Finset.mem_insert_self e A), he⟩
      have hebridge : (G.deleteEdges (A : Set (Sym2 V))).IsBridge e :=
        SimpleGraph.IsBridge.anti
          (SimpleGraph.deleteEdges_le (G := G) (A : Set (Sym2 V)))
          (hAbridge e (Finset.mem_insert_self e A))
      have hcount := connected_component_count_delete_bridge
        (G.deleteEdges (A : Set (Sym2 V))) e heedge hebridge
      have hdelete :
          (G.deleteEdges (A : Set (Sym2 V))).deleteEdges {e} =
            G.deleteEdges ((insert e A : Finset (Sym2 V)) : Set (Sym2 V)) := by
        rw [SimpleGraph.deleteEdges_deleteEdges, Finset.coe_insert]
        congr 1
        ext f
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
        exact or_comm
      rw [← hdelete, hcount, ih hAedge' hAbridge', Finset.card_insert_of_notMem he]

end ErdosProblems.PathUpperReduction

