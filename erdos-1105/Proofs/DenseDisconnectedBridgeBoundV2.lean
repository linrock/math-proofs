module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
The bound uses three nonempty vertex parts obtained by deleting an actual bridge
from a disconnected graph. It does not assert a colored path theorem.
-/

namespace ErdosProblems.PathUpperDenseDisconnectedBridgeBound

open SimpleGraph

theorem choose_three_positive
    (s t u : ℕ) (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) :
    s.choose 2 + t.choose 2 + u.choose 2 ≤ (s + t + u - 2).choose 2 := by
  let x := s - 1
  let y := t - 1
  let z := u - 1
  have hsx : s = x + 1 := by dsimp [x]; omega
  have hty : t = y + 1 := by dsimp [y]; omega
  have huz : u = z + 1 := by dsimp [z]; omega
  have hshift : s + t + u - 2 = x + y + z + 1 := by omega
  have hx : (x + 1) * x = (x + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq x 1
  have hy : (y + 1) * y = (y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq y 1
  have hz : (z + 1) * z = (z + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq z 1
  have hxyz : (x + y + z + 1) * (x + y + z) =
      (x + y + z + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq (x + y + z) 1
  rw [hshift, hsx, hty, huz]
  nlinarith [Nat.zero_le (x * y), Nat.zero_le (x * z), Nat.zero_le (y * z)]

/-- A disconnected graph on `k` vertices with an actual bridge has at most
`choose (k - 2) 2 + 1` edges. Membership in the original edge set is essential:
Mathlib's `IsBridge` also holds for some absent pairs. -/
theorem edge_card_le_of_disconnected_actual_bridge
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hdis : ¬ G.Connected) (f : Sym2 (Fin k))
    (hf : f ∈ G.edgeSet) (hbridge : G.IsBridge f) :
    G.edgeFinset.card ≤ (k - 2).choose 2 + 1 := by
  classical
  revert hf hbridge
  refine Sym2.inductionOn f ?_
  intro a b hf hbridge
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin k)))
  have hle : D ≤ G := G.deleteEdges_le _
  have hab : G.Adj a b := G.mem_edgeSet.mp hf
  have hsep : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  let S : Finset (Fin k) := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset (Fin k) := Finset.univ.filter (fun x => D.Reachable b x)
  let U : Finset (Fin k) := Finset.univ \ (S ∪ T)
  have hS (x : Fin k) : x ∈ S ↔ D.Reachable a x := by simp [S]
  have hT (x : Fin k) : x ∈ T ↔ D.Reachable b x := by simp [T]
  have hU (x : Fin k) : x ∈ U ↔ x ∉ S ∧ x ∉ T := by simp [U]
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact hsep (((hS x).mp hxS).trans ((hT x).mp hxT).symm)
  have hSTU : Disjoint (S ∪ T) U := Finset.disjoint_sdiff
  have hparts : (S ∪ T) ∪ U = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsum : S.card + T.card + U.card = k := by
    calc
      S.card + T.card + U.card = (S ∪ T).card + U.card := by
        rw [Finset.card_union_of_disjoint hST]
      _ = ((S ∪ T) ∪ U).card := (Finset.card_union_of_disjoint hSTU).symm
      _ = k := by simp only [hparts, Finset.card_univ, Fintype.card_fin]
  have hSpos : 0 < S.card :=
    Finset.card_pos.mpr ⟨a, (hS a).mpr (SimpleGraph.Reachable.refl _)⟩
  have hTpos : 0 < T.card :=
    Finset.card_pos.mpr ⟨b, (hT b).mpr (SimpleGraph.Reachable.refl _)⟩
  have hzexists : ∃ z : Fin k, ¬ G.Reachable a z := by
    by_contra hz
    apply hdis
    apply (G.connected_iff_exists_forall_reachable).mpr
    refine ⟨a, ?_⟩
    intro z
    by_contra haz
    exact hz ⟨z, haz⟩
  obtain ⟨z, haz⟩ := hzexists
  have hzS : z ∉ S := by
    intro hzS
    exact haz (SimpleGraph.Reachable.mono hle ((hS z).mp hzS))
  have hzT : z ∉ T := by
    intro hzT
    exact haz (hab.reachable.trans (SimpleGraph.Reachable.mono hle ((hT z).mp hzT)))
  have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨z, (hU z).mpr ⟨hzS, hzT⟩⟩
  have hSclosed : ∀ {x y : Fin k}, D.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    exact (hS y).mpr (((hS x).mp hx).trans hxy.reachable)
  have hTclosed : ∀ {x y : Fin k}, D.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    exact (hT y).mpr (((hT x).mp hx).trans hxy.reachable)
  have hUclosed : ∀ {x y : Fin k}, D.Adj x y → x ∈ U → y ∈ U := by
    intro x y hxy hx
    obtain ⟨hxS, hxT⟩ := (hU x).mp hx
    apply (hU y).mpr
    constructor
    · intro hyS
      exact hxS (hSclosed hxy.symm hyS)
    · intro hyT
      exact hxT (hTclosed hxy.symm hyT)
  let ES := D.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := D.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  let EU := D.edgeFinset.filter (fun e => e.toFinset ⊆ U)
  have hcover : D.edgeFinset ⊆ (ES ∪ ET) ∪ EU := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : D.Adj x y := D.mem_edgeSet.mp (D.mem_edgeFinset.mp he)
    by_cases hxS : x ∈ S
    · have hsub : s(x, y).toFinset ⊆ S := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxS (hSclosed hxy hxS)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨he, hsub⟩))))
    · by_cases hxT : x ∈ T
      · have hsub : s(x, y).toFinset ⊆ T := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxT (hTclosed hxy hxT)
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))))
      · have hxU : x ∈ U := (hU x).mpr ⟨hxS, hxT⟩
        have hsub : s(x, y).toFinset ⊆ U := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxU (hUclosed hxy hxU)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))
  have hES : ES.card ≤ S.card.choose 2 := by
    calc
      ES.card = (D.induce (↑S : Set (Fin k))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) S
      _ ≤ (Fintype.card S).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑S : Set (Fin k)))
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hET : ET.card ≤ T.card.choose 2 := by
    calc
      ET.card = (D.induce (↑T : Set (Fin k))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) T
      _ ≤ (Fintype.card T).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑T : Set (Fin k)))
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hEU : EU.card ≤ U.card.choose 2 := by
    calc
      EU.card = (D.induce (↑U : Set (Fin k))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) U
      _ ≤ (Fintype.card U).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑U : Set (Fin k)))
      _ = U.card.choose 2 := by rw [Fintype.card_coe]
  have hDcap : D.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 := by
    calc
      D.edgeFinset.card ≤ ((ES ∪ ET) ∪ EU).card := Finset.card_le_card hcover
      _ ≤ (ES ∪ ET).card + EU.card := Finset.card_union_le (ES ∪ ET) EU
      _ ≤ ES.card + ET.card + EU.card :=
        Nat.add_le_add_right (Finset.card_union_le ES ET) EU.card
      _ ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 := by omega
  have hchoose : S.card.choose 2 + T.card.choose 2 + U.card.choose 2 ≤ (k - 2).choose 2 := by
    simpa only [hsum] using choose_three_positive S.card T.card U.card hSpos hTpos hUpos
  have hdelete : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, Finset.coe_erase, D, SimpleGraph.edgeSet_deleteEdges]
  have hedge : D.edgeFinset.card + 1 = G.edgeFinset.card := by
    rw [hdelete]
    exact Finset.card_erase_add_one (G.mem_edgeFinset.mpr hf)
  omega

/-- In a disconnected graph above the bridge bound, every actual edge is a nonbridge. -/
theorem actual_edge_not_bridge_of_dense_disconnected
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hdis : ¬ G.Connected) (hdense : (k - 2).choose 2 + 2 ≤ G.edgeFinset.card) :
    ∀ f ∈ G.edgeSet, ¬ G.IsBridge f := by
  intro f hf hbridge
  have hcap := edge_card_le_of_disconnected_actual_bridge G hdis f hf hbridge
  omega

end ErdosProblems.PathUpperDenseDisconnectedBridgeBound

