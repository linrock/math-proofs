module

public import EvenOriginalContactCount1105
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

/-!
Faithful actual finite-carrier application of the Fin-only
contact classifier. The finite equivalence and every transported edge-filter,
contact, degree and cycle-copy fact are derived internally. This can be used
with an actual induced replacement graph; its original-ambient insertion
ledger and within-degree calculations remain separate caller obligations.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenFiniteCarrierAdapter1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenActualContactClosure1105

variable {V W : Type*} [Fintype V] [Fintype W]

-- Statement-side equality choices match the literal canonical filter definitions.
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W

noncomputable instance graph_neighborSet_fintype {A : Type*} [Finite A]
    (G : SimpleGraph A) (x : A) : Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- The identical actual-contact filter on an arbitrary finite carrier.
The imported `originalContacts` definition is specialized to `Fin n`. -/
noncomputable def actualContacts (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact S.filter (fun a => ∃ x, x ∉ S ∧ G.Adj x a)

omit [Fintype V] [Fintype W] in
theorem mapped_edge_subset_iff (f : V ↪ W) (e : Sym2 V) (A : Finset V) :
    (f.sym2Map e).toFinset ⊆ A.map f ↔ e.toFinset ⊆ A := by
  classical
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [Finset.subset_iff, Sym2.mem_toFinset, Function.Embedding.sym2Map_apply,
    Sym2.map_mk, Sym2.mem_iff]
  constructor
  · intro h z hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact (Finset.mem_map' f).mp (h (Or.inl rfl))
    · rw [hzy]; exact (Finset.mem_map' f).mp (h (Or.inr rfl))
  · intro h w hw
    rcases hw with hwx | hwy
    · rw [hwx]; exact (Finset.mem_map' f).mpr (h (Or.inl rfl))
    · rw [hwy]; exact (Finset.mem_map' f).mpr (h (Or.inr rfl))

/-- Exact transport of the ORIGINAL unordered within-support edge population.
No equality of filtered counts is supplied to the caller. -/
theorem withinEdges_map_embedding (G : SimpleGraph V) (f : V ↪ W)
    (A : Finset V) :
    withinEdges (G.map f) (A.map f) = (withinEdges G A).map f.sym2Map := by
  classical
  unfold withinEdges
  ext e
  simp only [Finset.mem_filter, Finset.mem_map, mem_edgeFinset]
  constructor
  · revert e
    intro e
    refine Sym2.inductionOn e ?_
    intro x y
    rintro ⟨hxy, heA⟩
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f G x y).mp hxy
    refine ⟨s(u, v), ⟨huv, ?_⟩, rfl⟩
    exact (mapped_edge_subset_iff f s(u, v) A).mp heA
  · rintro ⟨t, ⟨htG, htA⟩, rfl⟩
    refine ⟨?_, (mapped_edge_subset_iff f t A).mpr htA⟩
    revert htG
    refine Sym2.inductionOn t ?_
    intro u v huv
    change (G.map f).Adj (f u) (f v)
    exact (SimpleGraph.map_adj f G (f u) (f v)).mpr ⟨u, v, huv, rfl, rfl⟩

/-- Exact transport of the canonical ORIGINAL unordered cross population;
both exclusion filters refer to the actual transported supports. -/
theorem coreCrossEdges_map_embedding (G : SimpleGraph V) (f : V ↪ W)
    (S U : Finset V) :
    coreCrossEdges (G.map f) (S.map f) (U.map f) =
      (coreCrossEdges G S U).map f.sym2Map := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heNonCore, heNotOutside⟩ := Finset.mem_filter.mp he
    obtain ⟨heWithin, heNotCore⟩ := Finset.mem_filter.mp heNonCore
    rw [withinEdges_map_embedding] at heWithin
    obtain ⟨t, htWithin, rfl⟩ := Finset.mem_map.mp heWithin
    have htNotCore : ¬ t.toFinset ⊆ S := by
      intro htS
      exact heNotCore ((mapped_edge_subset_iff f t S).mpr htS)
    have htNotOutside : ¬ t.toFinset ⊆ U \ S := by
      intro htO
      have hmapped := (mapped_edge_subset_iff f t (U \ S)).mpr htO
      rw [Finset.map_sdiff] at hmapped
      exact heNotOutside hmapped
    exact Finset.mem_map.mpr ⟨t,
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨htWithin, htNotCore⟩, htNotOutside⟩, rfl⟩
  · intro he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨htNonCore, htNotOutside⟩ := Finset.mem_filter.mp ht
    obtain ⟨htWithin, htNotCore⟩ := Finset.mem_filter.mp htNonCore
    have hmappedWithin : f.sym2Map t ∈ withinEdges (G.map f) (U.map f) := by
      rw [withinEdges_map_embedding]
      exact Finset.mem_map.mpr ⟨t, htWithin, rfl⟩
    have hmappedNotCore : ¬ (f.sym2Map t).toFinset ⊆ S.map f := by
      intro heS
      exact htNotCore ((mapped_edge_subset_iff f t S).mp heS)
    have hmappedNotOutside :
        ¬ (f.sym2Map t).toFinset ⊆ U.map f \ S.map f := by
      intro heO
      rw [← Finset.map_sdiff] at heO
      exact htNotOutside ((mapped_edge_subset_iff f t (U \ S)).mp heO)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hmappedWithin, hmappedNotCore⟩, hmappedNotOutside⟩

/-- Actual original contacts are transported by the derived carrier
equivalence; no contact set or correspondence is supplied as an oracle. -/
theorem actualContacts_map_equiv (G : SimpleGraph V) (e : V ≃ W)
    (S : Finset V) :
    actualContacts (G.map e.toEmbedding) (S.map e.toEmbedding) =
      (actualContacts G S).map e.toEmbedding := by
  classical
  have hmem (A : Finset V) (x : V) :
      e x ∈ A.map e.toEmbedding ↔ x ∈ A := Finset.mem_map' e.toEmbedding
  have hadj (x y : V) : (G.map e.toEmbedding).Adj (e x) (e y) ↔ G.Adj x y :=
    (SimpleGraph.Iso.map e G).map_rel_iff'
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  constructor
  · intro hy
    unfold actualContacts at hy ⊢
    simp only [Finset.mem_filter] at hy
    rcases hy with ⟨hxS, z, hzS, hzx⟩
    obtain ⟨w, rfl⟩ := e.surjective z
    apply Finset.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨(hmem S x).mp hxS, w, fun hw => hzS ((hmem S w).mpr hw), (hadj w x).mp hzx⟩
  · intro hy
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hy
    have hzx' : z = x := e.injective hzx
    subst z
    unfold actualContacts at hz ⊢
    simp only [Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hxS, w, hwS, hwx⟩
    exact ⟨(hmem S x).mpr hxS, e w, fun hw => hwS ((hmem S w).mp hw), (hadj w x).mpr hwx⟩

/-- Generic actual finite-carrier contact rigidity. The only carrier-size
guard is its actual cardinality; the Fin equivalence, edge population,
degree/cycle transport and original contacts are all derived internally.
In particular V may be the actual subtype of a replacement support. -/
theorem actual_finite_contact_rigidity {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph V) (hN : Fintype.card V = 2 * d + 3) (S : Finset V)
    (hScard : S.card = d + 3) (hclique : G.IsClique (S : Set V))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hledger : d * d ≤ (coreCrossEdges G S Finset.univ).card +
      (withinEdges G (Finset.univ \ S)).card) :
    (actualContacts G S).card = d ∧
      actualContacts G S ⊆ S ∧
      (S \ actualContacts G S).card = 3 ∧
      (Finset.univ \ S).card = d ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ actualContacts G S) ∨
          (v ∉ S ∧ u ∈ actualContacts G S)) := by
  classical
  let e : V ≃ Fin (2 * d + 3) := Fintype.equivFinOfCardEq hN
  let J := G.map e.toEmbedding
  let S' := S.map e.toEmbedding
  let C := actualContacts G S
  let C' := originalContacts J S'
  have hmemS (x : V) : e x ∈ S' ↔ x ∈ S := Finset.mem_map' e.toEmbedding
  have hadj (x y : V) : J.Adj (e x) (e y) ↔ G.Adj x y :=
    (SimpleGraph.Iso.map e G).map_rel_iff'
  have hS'card : S'.card = d + 3 := by
    change (S.map e.toEmbedding).card = d + 3
    rw [Finset.card_map, hScard]
  have hclique' : J.IsClique (S' : Set (Fin (2 * d + 3))) := by
    intro u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
    exact (hadj a b).mpr (hclique ha hb (fun hab => huv (congrArg e hab)))
  have houtsider' : ∀ x, x ∉ S' → d ≤ J.degree x := by
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hxS : x ∉ S := fun hx => hy ((hmemS x).mpr hx)
    have hdegree := SimpleGraph.degree_map_apply G e.toEmbedding x
    exact hdegree.symm ▸ houtsider x hxS
  have hfree' : (cycleGraph (2 * d + 3)).Free J := by
    rintro ⟨f⟩
    exact hfree ⟨(SimpleGraph.Iso.map e G).symm.toCopy.comp f⟩
  have hcrossMap : coreCrossEdges J S' Finset.univ =
      (coreCrossEdges G S Finset.univ).map e.toEmbedding.sym2Map := by
    have h := coreCrossEdges_map_embedding G e.toEmbedding S Finset.univ
    rw [Finset.map_univ_equiv] at h
    exact h
  have hOutsideMap : (Finset.univ \ S).map e.toEmbedding =
      Finset.univ \ S' := by
    change (Finset.univ \ S).map e.toEmbedding = Finset.univ \ S.map e.toEmbedding
    rw [Finset.map_sdiff, Finset.map_univ_equiv]
  have houtMap : withinEdges J (Finset.univ \ S') =
      (withinEdges G (Finset.univ \ S)).map e.toEmbedding.sym2Map := by
    have h := withinEdges_map_embedding G e.toEmbedding (Finset.univ \ S)
    rw [hOutsideMap] at h
    exact h
  have hledger' : d * d ≤ (coreCrossEdges J S' Finset.univ).card +
      (withinEdges J (Finset.univ \ S')).card := by
    rw [hcrossMap, houtMap, Finset.card_map, Finset.card_map]
    exact hledger
  have hCmap : C' = C.map e.toEmbedding := by
    refine Eq.trans ?_ (actualContacts_map_equiv G e S)
    dsimp only [C']
    unfold originalContacts actualContacts
    congr 1
  have hCcard : C.card = d := by
    have h := EvenOriginalContactCount1105.original_contacts_card_eq
      hd J S' hS'card hclique' houtsider' hfree' hledger'
    change C'.card = d at h
    rw [hCmap, Finset.card_map] at h
    exact h
  have hCS : C ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hthree : (S \ C).card = 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hCS
    rw [hCcard, hScard] at hcard
    omega
  have hOcard : (Finset.univ \ S).card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, hN, hScard] at hcard
    omega
  obtain ⟨_hCS', _hthree', _hOcard', hAdj'⟩ :=
    EvenOriginalContactCount1105.original_contact_rigidity_of_suffix_ledger
      hd J S' hS'card hclique' houtsider' hfree' hledger'
  have hmemC (x : V) : e x ∈ C' ↔ x ∈ C := by
    rw [hCmap]
    exact Finset.mem_map' e.toEmbedding
  refine ⟨hCcard, hCS, hthree, hOcard, ?_⟩
  intro u v
  have h := hAdj' (e u) (e v)
  change J.Adj (e u) (e v) ↔ e u ≠ e v ∧
    ((e u ∈ S' ∧ e v ∈ S') ∨
      (e u ∉ S' ∧ e v ∈ C') ∨
      (e v ∉ S' ∧ e u ∈ C')) at h
  simpa only [hadj, hmemS, hmemC, ne_eq, e.injective.eq_iff] using h

end ErdosProblems.PathUpperReduction.EvenFiniteCarrierAdapter1105
