module

public import CorePreliminaries1105
public import CoreCliqueCheckpoint1105
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
Actual greatest-core size bound. All cycles of order at least K are excluded;
the final wrapper derives saturation on the same finite carrier.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.CoreSizeUpper1105

variable {V : Type*}

theorem clique_cycle_copy (G : SimpleGraph V) (S : Finset V) (K : ℕ)
    (hcl : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) (hcard : K ≤ S.card) :
    Nonempty ((cycleGraph K).Copy G) := by
  classical
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin K) (s := S) (by simpa using hcard)
  refine ⟨{ toHom := { toFun := f, map_rel' := ?_ }, injective' := f.injective }⟩
  intro i j hij
  exact hcl (f i) (hf ⟨i, rfl⟩) (f j) (hf ⟨j, rfl⟩)
    (fun h => hij.ne (f.injective h))

theorem clique_card_lt_cycle_order (G : SimpleGraph V) (S : Finset V) (K : ℕ)
    (hcl : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)
    (hfree : (cycleGraph K).Free G) : S.card < K := by
  apply Nat.lt_of_not_ge
  intro hcard
  exact hfree (clique_cycle_copy G S K hcl hcard)

theorem insert_good_of_all_neighbors (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hS : GoodCore G d S) (hd : d < S.card) (x : V)
    (hall : ∀ y ∈ S, G.Adj x y) :
    letI := Classical.decEq V
    GoodCore G d (insert x S) := by
  classical
  intro z hz
  have hmono : S.filter (fun w => G.Adj z w) ⊆
      (insert x S).filter (fun w => G.Adj z w) := by
    intro w hw
    obtain ⟨hwS, hzw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwS, hzw⟩
  rcases Finset.mem_insert.mp hz with hzx | hzS
  · subst z
    have heq : S.filter (fun w => G.Adj x w) = S := Finset.filter_eq_self.mpr hall
    have hle := Finset.card_le_card hmono
    rw [heq] at hle
    exact hd.trans_le hle
  · exact (hS z hzS).trans_le (Finset.card_le_card hmono)

theorem captured_neighbor_count_le (G : SimpleGraph V) (S : Finset V)
    {a b : V} (P : G.Walk a b) (x : V)
    (hcap : ∀ z ∈ S, G.Adj x z → z ∈ P.support) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    (S.filter (fun z => G.Adj x z)).card ≤
      (P.support.toFinset.filter (fun z => G.Adj x z)).card := by
  classical
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzS, hxz⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcap z hzS hxz), hxz⟩

variable [Fintype V]

theorem saturated_core_card_le (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ G.Adj u v →
      ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (G ⊔ fromEdgeSet {s(u, v)}))) :
    (degreeCore G ((K - 1) / 2)).card ≤ K - 2 := by
  classical
  let C := degreeCore G ((K - 1) / 2)
  have hcl : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → G.Adj x y :=
    CoreCliqueCheckpoint1105.saturated_core_clique G hK hfree hdel hsat
  have hlt : C.card < K := clique_card_lt_cycle_order G C K hcl (hfree K le_rfl)
  by_contra hbound
  change ¬ C.card ≤ K - 2 at hbound
  have hcard : C.card = K - 1 := by omega
  have hout : ∃ x : V, x ∉ C := by
    by_contra hnone
    have hall : ∀ x : V, x ∈ C := by
      intro x
      by_contra hx
      exact hnone ⟨x, hx⟩
    have heq : C = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have hcardN : C.card = Fintype.card V := by rw [heq]; exact Finset.card_univ
    omega
  obtain ⟨x, hx⟩ := hout
  have hmissing : ∃ y ∈ C, ¬ G.Adj x y := by
    by_contra hnone
    have hall : ∀ y ∈ C, G.Adj x y := by
      intro y hy
      by_contra hxy
      exact hnone ⟨y, hy, hxy⟩
    have hd : (K - 1) / 2 < C.card := by omega
    have hgood := insert_good_of_all_neighbors G ((K - 1) / 2) C
      (degree_core_good G ((K - 1) / 2)) hd x hall
    have hxcore := good_subset_core G ((K - 1) / 2) (insert x C) hgood
      (Finset.mem_insert_self x C)
    exact hx hxcore
  obtain ⟨y, hy, hxy⟩ := hmissing
  have hne : x ≠ y := by
    intro heq
    subst y
    exact hx hy
  obtain ⟨m, hKm, ⟨f⟩⟩ := hsat x y hne hxy
  obtain ⟨P, hp, hlen⟩ := AllLongSaturation.added_pair_path
    (G := G) (u := x) (v := y) (m := m)
    (CoreCliqueCheckpoint1105.cycle_order_gt_two K m hK hKm)
    (hfree m hKm) hne hxy f
  have hKP : K ≤ P.length + 1 :=
    CoreCliqueCheckpoint1105.extracted_path_long K m P.length hK hKm hlen
  have noLong := AllLongSaturation.no_long_cycle G hK hfree
  obtain ⟨a, _ha, b, hb, Q, hQ, _hab, hPQ, _hmax, hleft, hright⟩ :=
    EndpointCapture.exists_captured_family_maximum
      (G := G) (x := x) (y := y) (K := K)
      Finset.univ C P hp (Finset.mem_univ x) hy hxy hK hKP noLong
  have hKQ : K ≤ Q.length + 1 := by omega
  have hN : 3 ≤ Fintype.card V := by omega
  have hL : 2 ≤ (Q.support.toFinset.filter (fun z => G.Adj a z)).card :=
    (CorePreliminaries1105.ambient_neighbor_filter_card_ge_two G hN hdel a).trans
      (captured_neighbor_count_le G Finset.univ Q a hleft)
  have hrsub : C.erase b ⊆ Q.support.toFinset.filter (fun z => G.Adj b z) := by
    intro z hz
    obtain ⟨hzb, hzC⟩ := Finset.mem_erase.mp hz
    have hbz : G.Adj b z := hcl b hb z hzC (Ne.symm hzb)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hright z hzC hbz), hbz⟩
  have hR : K - 2 ≤ (Q.support.toFinset.filter (fun z => G.Adj b z)).card := by
    have hle := Finset.card_le_card hrsub
    rw [Finset.card_erase_of_mem hb, hcard] at hle
    omega
  have hsum : K ≤
      (Q.support.toFinset.filter (fun z => G.Adj (Q.getVert 0) z)).card +
      (Q.support.toFinset.filter (fun z => G.Adj (Q.getVert Q.length) z)).card := by
    simp only [Walk.getVert_zero, Walk.getVert_length]
    omega
  have hdelQ : ∀ i : Fin (Q.length + 1), 0 < i → i < Fin.last Q.length →
      (G.induce {w | w ≠ Q.getVert i.val}).Connected := by
    intro i _hi _hilast
    exact hdel (Q.getVert i.val)
  obtain ⟨D, hD, hKD⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold
    Q hQ hdelQ K hK hKQ hsum
  exact (Nat.not_le_of_gt (noLong (Q.getVert 0) D hD)) hKD

theorem nonempty_core_size_interval (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ G.Adj u v →
      ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (G ⊔ fromEdgeSet {s(u, v)})))
    (hC : (degreeCore G ((K - 1) / 2)).Nonempty) :
    (K - 1) / 2 + 2 ≤ (degreeCore G ((K - 1) / 2)).card ∧
      (degreeCore G ((K - 1) / 2)).card ≤ K - 2 := by
  exact ⟨CorePreliminaries1105.nonempty_degree_core_card_ge_add_two
    G ((K - 1) / 2) hC, saturated_core_card_le G hK hKN hfree hdel hsat⟩

theorem exists_saturated_small_core (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      (∀ x ∈ degreeCore H ((K - 1) / 2), ∀ y ∈ degreeCore H ((K - 1) / 2),
        x ≠ y → H.Adj x y) ∧
      (degreeCore H ((K - 1) / 2)).card ≤ K - 2 := by
  obtain ⟨H, hGH, hHfree, hHdel, hHsat, hHcl⟩ :=
    CoreCliqueCheckpoint1105.exists_saturated_clique_core G hK hfree hdel
  exact ⟨H, hGH, hHfree, hHdel, hHsat, hHcl,
    saturated_core_card_le H hK hKN hHfree hHdel hHsat⟩

end ErdosProblems.PathUpperReduction.CoreSizeUpper1105
