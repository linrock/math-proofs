module

public import Mathlib

@[expose] public section


/-!
# The finite three-partite greedy-matching argument

This proves the precise `|E| ≤ 3 Δ |M|` bound without assuming any analytic
edge-count or degree estimates.
-/

namespace Erdos689

/-- An edge records its three distinct vertex-part coordinates. -/
abbrev TripleEdge := ℕ × ℕ × ℕ

/-- Two three-partite edges collide when they share at least one vertex. -/
def sharesVertex (e f : TripleEdge) : Prop :=
  e.1 = f.1 ∨ e.2.1 = f.2.1 ∨ e.2.2 = f.2.2

/-- The finite edge neighborhood deleted by one greedy selection. -/
def edgeNeighborhood (E : Finset TripleEdge) (e : TripleEdge) : Finset TripleEdge :=
  E.filter fun f => f.1 = e.1 ∨ f.2.1 = e.2.1 ∨ f.2.2 = e.2.2

/-- A matching has no vertex collision between distinct selected edges. -/
def threePartiteMatching (M : Finset TripleEdge) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ sharesVertex e f

/-- A maximal matching lies in the edge set and blocks every remaining edge. -/
def maximalMatching (E M : Finset TripleEdge) : Prop :=
  M ⊆ E ∧ threePartiteMatching M ∧
    ∀ e ∈ E, ∃ f ∈ M, sharesVertex e f

/-- Every edge shares its three vertices with itself. -/
theorem sharesVertex_refl (e : TripleEdge) : sharesVertex e e := by
  exact Or.inl rfl

/-- Vertex collision is symmetric. -/
theorem sharesVertex_symm {e f : TripleEdge} (h : sharesVertex e f) :
    sharesVertex f e := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

/-- Every finite three-partite edge family has an inclusion-maximal matching. -/
theorem exists_maximalMatching (E : Finset TripleEdge) :
    ∃ M : Finset TripleEdge, maximalMatching E M := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      refine ⟨∅, ?_⟩
      simp [maximalMatching, threePartiteMatching]
  | @insert e E _he ih =>
      obtain ⟨M, hsub, hmatching, hcover⟩ := ih
      by_cases hconflict : ∃ f ∈ M, sharesVertex e f
      · refine ⟨M, ?_, hmatching, ?_⟩
        · intro f hf
          exact Finset.mem_insert_of_mem (hsub hf)
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact hconflict
          · exact hcover f hf
      · refine ⟨insert e M, ?_, ?_, ?_⟩
        · intro f hf
          rcases Finset.mem_insert.mp hf with hfe | hf
          · subst f
            exact Finset.mem_insert_self e E
          · exact Finset.mem_insert_of_mem (hsub hf)
        · intro f hf g hg hfg hshare
          rcases Finset.mem_insert.mp hf with hfe | hf
          · subst f
            rcases Finset.mem_insert.mp hg with hge | hg
            · subst g
              exact hfg rfl
            · exact hconflict ⟨g, hg, hshare⟩
          · rcases Finset.mem_insert.mp hg with hge | hg
            · subst g
              exact hconflict ⟨f, hf, sharesVertex_symm hshare⟩
            · exact hmatching f hf g hg hfg hshare
        · intro f hf
          rcases Finset.mem_insert.mp hf with hfe | hf
          · subst f
            exact ⟨e, Finset.mem_insert_self e M, sharesVertex_refl e⟩
          · obtain ⟨g, hg, hshare⟩ := hcover f hf
            exact ⟨g, Finset.mem_insert_of_mem hg, hshare⟩

/-- A deleted edge neighborhood is the union of its three vertex fibers. -/
theorem edgeNeighborhood_eq_vertex_fibers (E : Finset TripleEdge) (e : TripleEdge) :
    edgeNeighborhood E e =
      ((E.filter fun f => f.1 = e.1) ∪
       (E.filter fun f => f.2.1 = e.2.1)) ∪
       (E.filter fun f => f.2.2 = e.2.2) := by
  classical
  ext f
  simp [edgeNeighborhood]
  tauto

/-- A maximum vertex degree `D` bounds every deleted neighborhood by `3D`. -/
theorem edgeNeighborhood_card_le_three_mul (E : Finset TripleEdge) (D : ℕ)
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D)
    (e : TripleEdge) :
    (edgeNeighborhood E e).card ≤ 3 * D := by
  rw [edgeNeighborhood_eq_vertex_fibers]
  have hxy := Finset.card_union_le
    (E.filter fun f => f.1 = e.1)
    (E.filter fun f => f.2.1 = e.2.1)
  have hxyz := Finset.card_union_le
    ((E.filter fun f => f.1 = e.1) ∪
     (E.filter fun f => f.2.1 = e.2.1))
    (E.filter fun f => f.2.2 = e.2.2)
  have hfirst := hx e.1
  have hsecond := hy e.2.1
  have hthird := hz e.2.2
  omega

/-- Every edge is deleted by the neighborhood of a maximal selected edge. -/
theorem edges_subset_selected_neighborhoods {E M : Finset TripleEdge}
    (hmax : maximalMatching E M) :
    E ⊆ M.biUnion (edgeNeighborhood E) := by
  classical
  intro e he
  obtain ⟨f, hf, hshare⟩ := hmax.2.2 e he
  apply Finset.mem_biUnion.mpr
  refine ⟨f, hf, ?_⟩
  exact Finset.mem_filter.mpr ⟨he, hshare⟩

/-- The manuscript's exact greedy bound holds for every maximal matching. -/
theorem maximalMatching_card_bound {E M : Finset TripleEdge} {D : ℕ}
    (hmax : maximalMatching E M)
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D) :
    E.card ≤ 3 * D * M.card := by
  classical
  calc
    E.card ≤ (M.biUnion (edgeNeighborhood E)).card :=
      Finset.card_le_card (edges_subset_selected_neighborhoods hmax)
    _ ≤ M.card * (3 * D) :=
      Finset.card_biUnion_le_card_mul M (edgeNeighborhood E) (3 * D)
        (fun e _ => edgeNeighborhood_card_le_three_mul E D hx hy hz e)
    _ = 3 * D * M.card := by ring

/-- There always exists a genuine three-partite matching of the required size. -/
theorem exists_greedy_matching {E : Finset TripleEdge} {D : ℕ}
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D) :
    ∃ M : Finset TripleEdge,
      M ⊆ E ∧ threePartiteMatching M ∧ E.card ≤ 3 * D * M.card := by
  obtain ⟨M, hmax⟩ := exists_maximalMatching E
  exact ⟨M, hmax.1, hmax.2.1, maximalMatching_card_bound hmax hx hy hz⟩

end Erdos689

#print axioms Erdos689.sharesVertex_refl
#print axioms Erdos689.sharesVertex_symm
#print axioms Erdos689.exists_maximalMatching
#print axioms Erdos689.edgeNeighborhood_eq_vertex_fibers
#print axioms Erdos689.edgeNeighborhood_card_le_three_mul
#print axioms Erdos689.edges_subset_selected_neighborhoods
#print axioms Erdos689.maximalMatching_card_bound
#print axioms Erdos689.exists_greedy_matching
