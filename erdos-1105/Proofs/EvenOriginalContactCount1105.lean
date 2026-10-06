module

public import EvenOriginalContactRigidity1105
public import TightCoreBlockEdgeLedger1105
public import PathErdosGallai
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
The exact original unordered suffix ledger supplies the
contact count; neither independence nor an actual path/cover/count oracle is
supplied.
-/

namespace ErdosProblems.PathUpperReduction.EvenOriginalContactCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenActualContactClosure1105
open ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105
open ErdosProblems.PathUpperReduction.EvenOriginalContactRigidity1105

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Each canonical unordered crossing edge has one outsider/contact
orientation. A subset of the product's image suffices for its capacity bound;
no injectivity or oriented-cross-count premise is needed. -/
theorem cross_edges_le_contact_capacity {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (coreCrossEdges G S Finset.univ).card ≤
      (Finset.univ \ S).card * (originalContacts G S).card := by
  classical
  let O : Finset (Fin n) := Finset.univ \ S
  let C := originalContacts G S
  let P := O.product C
  have hsub : coreCrossEdges G S Finset.univ ⊆
      P.image (fun p => s(p.1, p.2)) := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    unfold coreCrossEdges nonCoreEdges withinEdges at he
    simp only [Finset.mem_filter, Finset.subset_iff, Sym2.mem_toFinset,
      Sym2.mem_iff, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_edgeFinset] at he
    rcases he with ⟨⟨⟨hxy, _heUniv⟩, heNotS⟩, heNotO⟩
    have hnotS : ¬ (x ∈ S ∧ y ∈ S) := by
      rintro ⟨hxS, hyS⟩
      apply heNotS
      intro z hz
      rcases hz with rfl | rfl
      · exact hxS
      · exact hyS
    have hnotO : ¬ (x ∉ S ∧ y ∉ S) := by
      rintro ⟨hxS, hyS⟩
      apply heNotO
      intro z hz
      rcases hz with rfl | rfl
      · exact hxS
      · exact hyS
    by_cases hxS : x ∈ S
    · have hyS : y ∉ S := fun hyS => hnotS ⟨hxS, hyS⟩
      have hxC : x ∈ C := by
        change x ∈ S.filter (fun a => ∃ z, z ∉ S ∧ G.Adj z a)
        exact Finset.mem_filter.mpr ⟨hxS, y, hyS, hxy.symm⟩
      have hyO : y ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩
      exact Finset.mem_image.mpr ⟨(y, x),
        Finset.mem_product.mpr ⟨hyO, hxC⟩, Sym2.eq_swap⟩
    · have hyS : y ∈ S := by
        by_contra hyS
        exact hnotO ⟨hxS, hyS⟩
      have hyC : y ∈ C := by
        change y ∈ S.filter (fun a => ∃ z, z ∉ S ∧ G.Adj z a)
        exact Finset.mem_filter.mpr ⟨hyS, x, hxS, hxy⟩
      have hxO : x ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
      exact Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_product.mpr ⟨hxO, hyC⟩, rfl⟩
  calc
    (coreCrossEdges G S Finset.univ).card ≤
        (P.image (fun p => s(p.1, p.2))).card := Finset.card_le_card hsub
    _ ≤ P.card := Finset.card_image_le
    _ = (Finset.univ \ S).card * (originalContacts G S).card :=
      Finset.card_product _ _

/-- Construct an actual path plus all remaining singleton outsiders.
The cardinal identity is additive, avoiding truncated subtraction guards. -/
theorem exists_path_singleton_cover {V : Type*}
    (G : SimpleGraph V) (O : Finset V) (p : List V)
    (hp : p ≠ []) (hchain : p.IsChain G.Adj) (hnodup : p.Nodup)
    (hinside : ∀ z, z ∈ p → z ∈ O) :
    ∃ cover : List (List V),
      (∀ q, q ∈ cover → q ≠ []) ∧
      (∀ q, q ∈ cover → q.IsChain G.Adj) ∧
      cover.flatten.Nodup ∧
      (∀ z, z ∈ cover.flatten ↔ z ∈ O) ∧
      cover.length + p.length = O.card + 1 := by
  classical
  let R := O \ p.toFinset
  let cover := p :: R.toList.map (fun z => [z])
  have hflatten : cover.flatten = p ++ R.toList := by
    change p ++ (R.toList.map (fun z => [z])).flatten = p ++ R.toList
    rw [← List.flatMap_def, List.flatMap_singleton']
  have hnonempty : ∀ q, q ∈ cover → q ≠ [] := by
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hqR
    · subst q
      exact hp
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hqR
      simp
  have hpaths : ∀ q, q ∈ cover → q.IsChain G.Adj := by
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hqR
    · subst q
      exact hchain
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hqR
      exact List.IsChain.singleton (R := G.Adj) z
  have hsep : p.Disjoint R.toList := by
    rw [List.disjoint_left]
    intro z hzp hzR
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hzR)).2
      (List.mem_toFinset.mpr hzp)
  have hcoverNodup : cover.flatten.Nodup := by
    rw [hflatten]
    exact hnodup.append R.nodup_toList hsep
  have hcovers : ∀ z, z ∈ cover.flatten ↔ z ∈ O := by
    intro z
    rw [hflatten, List.mem_append]
    constructor
    · rintro (hzp | hzR)
      · exact hinside z hzp
      · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hzR)).1
    · intro hzO
      by_cases hzp : z ∈ p
      · exact Or.inl hzp
      · apply Or.inr
        apply Finset.mem_toList.mpr
        exact Finset.mem_sdiff.mpr ⟨hzO, fun hz => hzp (List.mem_toFinset.mp hz)⟩
  have hpSub : p.toFinset ⊆ O := by
    intro z hz
    exact hinside z (List.mem_toFinset.mp hz)
  have hcard := Finset.card_sdiff_add_card_eq_card hpSub
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  have hlength : cover.length + p.length = O.card + 1 := by
    simp only [cover, List.length_cons, List.length_map, Finset.length_toList]
    change R.card + p.length = O.card at hcard
    omega
  exact ⟨cover, hnonempty, hpaths, hcoverNodup, hcovers, hlength⟩

/-- A derived ORIGINAL outsider cover with enough actual contacts contradicts
original cycle-freedom, by filling and reversing only actual contact pairs. -/
theorem no_contact_cover {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (cover : List (List (Fin (2 * d + 3))))
    (hnonempty : ∀ p, p ∈ cover → p ≠ [])
    (hpaths : ∀ p, p ∈ cover → p.IsChain G.Adj)
    (hnodup : cover.flatten.Nodup)
    (hcovers : ∀ z, z ∈ cover.flatten ↔ z ∉ S)
    (hcapacity : cover.length + 1 ≤ (originalContacts G S).card) : False := by
  classical
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
    cycle_of_actual_outsider_path_cover hd G F hGF S C hScard hclique
      hCS cover hnonempty hpaths hnodup hcovers hcapacity hfilled
  exact hfree ((cycle_contained_fill_original_contacts_iff
    hd G S hScard hclique houtsider).mp hnew)

/-- The actual ORIGINAL suffix population, counting every crossing edge and
every internal-outsider edge once, determines the actual contact cardinality.
There is no independence, contact-count, path, cover or classification oracle. -/
theorem original_contacts_card_eq {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hledger : d * d ≤ (coreCrossEdges G S Finset.univ).card +
      (withinEdges G (Finset.univ \ S)).card) :
    (originalContacts G S).card = d := by
  classical
  let O : Finset (Fin (2 * d + 3)) := Finset.univ \ S
  let C := originalContacts G S
  have hOcard : O.card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    change O.card + S.card = (Finset.univ : Finset (Fin (2 * d + 3))).card at hcard
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hcard
    omega
  have hcle : C.card ≤ d := by
    by_contra hcle
    obtain ⟨x, hxO⟩ := Finset.card_pos.mp (by omega : 0 < O.card)
    obtain ⟨cover, hnonempty, hpaths, hnodup, hcovers, hlength⟩ :=
      exists_path_singleton_cover G O [x] (by simp)
        (List.IsChain.singleton (R := G.Adj) x) (by simp)
        (by
          intro z hz
          have hzx : z = x := List.mem_singleton.mp hz
          exact hzx.symm ▸ hxO)
    have hcapacity : cover.length + 1 ≤ C.card := by
      simp only [List.length_singleton] at hlength
      omega
    have hcoverOutside : ∀ z, z ∈ cover.flatten ↔ z ∉ S := by
      intro z
      simpa only [O, Finset.mem_sdiff, Finset.mem_univ, true_and] using hcovers z
    exact no_contact_cover hd G S hScard hclique houtsider hfree
      cover hnonempty hpaths hnodup hcoverOutside hcapacity
  have hcge : d ≤ C.card := by
    by_contra hcge
    let t := d - C.card
    have ht : 1 ≤ t := by omega
    have hct : C.card + t = d := by omega
    have hcross := cross_edges_le_contact_capacity G S
    change (coreCrossEdges G S Finset.univ).card ≤ O.card * C.card at hcross
    rw [hOcard] at hcross
    have hEQ : d * t ≤ (withinEdges G O).card := by
      change d * d ≤ (coreCrossEdges G S Finset.univ).card +
        (withinEdges G O).card at hledger
      nlinarith
    let Q := G.induce (O : Set (Fin (2 * d + 3)))
    have hQcard : Nat.card (O : Set (Fin (2 * d + 3))) = d :=
      (Nat.card_eq_finsetCard O).trans hOcard
    have hedgeQ : Nat.card Q.edgeSet = (withinEdges G O).card := by
      have hfilter := G.card_filter_edgeFinset_toFinset_subset O
      have hedge : Nat.card Q.edgeSet = Q.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card]
        exact Q.edgeFinset_card.symm
      refine hedge.trans (hfilter.symm.trans ?_)
      unfold withinEdges
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.subset_iff, Sym2.mem_toFinset]
    have hpath : pathGraph (t + 2) ⊑ Q := by
      by_contra hpath
      have hEG := ErdosProblems.PathErdosGallai.erdos_gallai_edge_bound
        Q (t + 1) (by omega) (by simpa only [Nat.add_assoc] using hpath)
      rw [hedgeQ, hQcard] at hEG
      have hpred : t + 1 - 1 = t := by omega
      rw [hpred] at hEG
      have hpositive : 0 < d * t := Nat.mul_pos (by omega) (by omega)
      nlinarith
    obtain ⟨f⟩ := hpath
    let order : Fin (t + 2) → Fin (2 * d + 3) := fun i => (f i : Fin (2 * d + 3))
    have horder : Function.Injective order := by
      intro i j hij
      apply f.injective
      exact Subtype.ext hij
    let p := List.ofFn order
    have hplen : p.length = t + 2 := List.length_ofFn
    have hp : p ≠ [] := by
      intro hnil
      rw [hnil, List.length_nil] at hplen
      omega
    have hchain : p.IsChain G.Adj := by
      apply List.isChain_ofFn.mpr
      intro i hi
      exact f.toHom.map_adj (pathGraph_adj.mpr (Or.inl rfl))
    have hpnodup : p.Nodup := List.nodup_ofFn_ofInjective horder
    have hpinside : ∀ z, z ∈ p → z ∈ O := by
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact (f i).property
    obtain ⟨cover, hnonempty, hpaths, hnodup, hcovers, hlength⟩ :=
      exists_path_singleton_cover G O p hp hchain hpnodup hpinside
    have hcapacity : cover.length + 1 ≤ C.card := by
      rw [hplen, hOcard] at hlength
      omega
    have hcoverOutside : ∀ z, z ∈ cover.flatten ↔ z ∉ S := by
      intro z
      simpa only [O, Finset.mem_sdiff, Finset.mem_univ, true_and] using hcovers z
    exact no_contact_cover hd G S hScard hclique houtsider hfree
      cover hnonempty hpaths hnodup hcoverOutside hcapacity
  exact Nat.le_antisymm hcle hcge

/-- Exact original support/cardinality/adjacency classification from the
original suffix ledger; the previously supplied contact-cardinality premise
is now derived internally on the SAME G, d and S. -/
theorem original_contact_rigidity_of_suffix_ledger {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hledger : d * d ≤ (coreCrossEdges G S Finset.univ).card +
      (withinEdges G (Finset.univ \ S)).card) :
    originalContacts G S ⊆ S ∧
      (S \ originalContacts G S).card = 3 ∧
      (Finset.univ \ S).card = d ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ originalContacts G S) ∨
          (v ∉ S ∧ u ∈ originalContacts G S)) := by
  exact original_contact_partition_and_adjacency hd G S hScard hclique
    (original_contacts_card_eq hd G S hScard hclique houtsider hfree hledger)
    houtsider hfree

end ErdosProblems.PathUpperReduction.EvenOriginalContactCount1105
