module

public import EvenActualContactClosure1105
public import EvenOutsiderEdgeCover1105

@[expose] public section

/-!
All graphs and degrees retain the SAME original
Fin (2*d+3) carrier. The original contact-cardinality and outsider-degree
premises remain explicit. The filled graph is constructed internally solely
to derive ORIGINAL outsider independence; no augmented edge is counted or
treated as an original colored edge.
-/

namespace ErdosProblems.PathUpperReduction.EvenOriginalContactRigidity1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.EvenActualContactClosure1105
open ErdosProblems.PathUpperReduction.EvenOutsiderEdgeCover1105

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Actual contact filling and its exact reversal rule out an ORIGINAL
outsider edge, without an outsider-independence or filling oracle. -/
theorem original_outsiders_independent {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (hCcard : (originalContacts G S).card = d)
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    ∀ x, x ∉ S → ∀ y, y ∉ S → ¬ G.Adj x y := by
  classical
  intro x hxS y hyS hxy
  let C := originalContacts G S
  let F := fillOriginalContacts G S
  have hCS : C ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hGF : G ≤ F := le_sup_left
  have hfilled : ∀ z, z ∉ S → ∀ a, a ∈ C → F.Adj z a := by
    intro z hzS a haC
    have haS := hCS haC
    have hza : z ≠ a := by
      intro hza
      exact hzS (hza.symm ▸ haS)
    change G.Adj z a ∨
      (fromEdgeSet (originalContactEdges G S : Set (Sym2 (Fin (2 * d + 3))))).Adj z a
    apply Or.inr
    apply (fromEdgeSet_adj _).mpr
    refine ⟨?_, hza⟩
    change s(z, a) ∈
      ((Finset.univ \ S).product (originalContacts G S)).image
        (fun p => s(p.1, p.2))
    exact Finset.mem_image.mpr ⟨(z, a), Finset.mem_product.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩, haC⟩, rfl⟩
  have hnew : cycleGraph (2 * d + 3) ⊑ F :=
    cycle_of_actual_outsider_edge hd G F hGF S C hScard hclique hCS
      hCcard hfilled ⟨x, y, hxS, hyS, hxy⟩
  have hclosure := cycle_contained_fill_original_contacts_iff
    hd G S hScard hclique houtsider
  exact hfree (hclosure.mp hnew)

/-- Every ORIGINAL outsider has exactly the actual original contact set as
its neighborhood, and its original whole-carrier degree is exactly d. -/
theorem outsider_neighbors_and_degree {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (hCcard : (originalContacts G S).card = d)
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (x : Fin (2 * d + 3)) (hxS : x ∉ S) :
    G.neighborFinset x = originalContacts G S ∧ G.degree x = d := by
  classical
  have hind := original_outsiders_independent hd G S hScard hclique
    hCcard houtsider hfree
  have hsub : G.neighborFinset x ⊆ originalContacts G S := by
    intro a ha
    have hxa := (mem_neighborFinset (G := G) (v := x) a).mp ha
    have haS : a ∈ S := by
      by_contra haS
      exact hind x hxS a haS hxa
    change a ∈ S.filter (fun a => ∃ z, z ∉ S ∧ G.Adj z a)
    exact Finset.mem_filter.mpr ⟨haS, x, hxS, hxa⟩
  have hcard : (originalContacts G S).card ≤ (G.neighborFinset x).card := by
    rw [hCcard, card_neighborFinset_eq_degree]
    exact houtsider x hxS
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨heq, ?_⟩
  rw [← card_neighborFinset_eq_degree, heq, hCcard]

/-- The actual ORIGINAL partition has d anchors, three other clique vertices,
and d outsiders. Its displayed exact adjacency is K_d join (K_3 disjoint I_d)
on those actual supports, without a supplied partition/order equivalence. -/
theorem original_contact_partition_and_adjacency {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (hCcard : (originalContacts G S).card = d)
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    originalContacts G S ⊆ S ∧
      (S \ originalContacts G S).card = 3 ∧
      (Finset.univ \ S).card = d ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ originalContacts G S) ∨
          (v ∉ S ∧ u ∈ originalContacts G S)) := by
  classical
  have hCS : originalContacts G S ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hthree : (S \ originalContacts G S).card = 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hCS
    rw [hCcard, hScard] at hcard
    omega
  have hOcard : (Finset.univ \ S).card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hcard
    omega
  refine ⟨hCS, hthree, hOcard, ?_⟩
  intro u v
  constructor
  · intro huv
    refine ⟨huv.ne, ?_⟩
    by_cases huS : u ∈ S
    · by_cases hvS : v ∈ S
      · exact Or.inl ⟨huS, hvS⟩
      · apply Or.inr
        apply Or.inr
        refine ⟨hvS, ?_⟩
        have heq := (outsider_neighbors_and_degree hd G S hScard hclique
          hCcard houtsider hfree v hvS).1
        rw [← heq]
        exact (mem_neighborFinset (G := G) (v := v) u).mpr huv.symm
    · apply Or.inr
      apply Or.inl
      refine ⟨huS, ?_⟩
      have heq := (outsider_neighbors_and_degree hd G S hScard hclique
        hCcard houtsider hfree u huS).1
      rw [← heq]
      exact (mem_neighborFinset (G := G) (v := u) v).mpr huv
  · rintro ⟨huv, hSS | hOC | hCO⟩
    · exact hclique hSS.1 hSS.2 huv
    · apply (mem_neighborFinset (G := G) (v := u) v).mp
      rw [(outsider_neighbors_and_degree hd G S hScard hclique
        hCcard houtsider hfree u hOC.1).1]
      exact hOC.2
    · apply Adj.symm
      apply (mem_neighborFinset (G := G) (v := v) u).mp
      rw [(outsider_neighbors_and_degree hd G S hScard hclique
        hCcard houtsider hfree v hCO.1).1]
      exact hCO.2

end ErdosProblems.PathUpperReduction.EvenOriginalContactRigidity1105
