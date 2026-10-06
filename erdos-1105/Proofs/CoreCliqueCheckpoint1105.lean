module

public import AllLongSaturation
public import EndpointCapture
public import CountCoreBasis
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Every
missing-pair path and every endpoint capture is derived on the same graph.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.CoreCliqueCheckpoint1105

theorem cycle_order_gt_two (K m : ℕ) (hK : 5 ≤ K) (hKm : K ≤ m) :
    2 < m := by omega

theorem extracted_path_long (K m p : ℕ) (hK : 5 ≤ K) (hKm : K ≤ m)
    (hp : p = m - 1) : K ≤ p + 1 := by omega

theorem longer_path_long (K p q : ℕ) (hKp : K ≤ p + 1) (hpq : p ≤ q) :
    K ≤ q + 1 := by omega

theorem core_endpoint_sum (K L R : ℕ) (hK : 5 ≤ K)
    (hL : (K - 1) / 2 < L) (hR : (K - 1) / 2 < R) :
    K ≤ L + R := by omega

variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem captured_good_degree (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hS : GoodCore G d S) {a b : V} (P : G.Walk a b) (x : V) (hx : x ∈ S)
    (hcap : ∀ z ∈ S, G.Adj x z → z ∈ P.support) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    d < (P.support.toFinset.filter (fun z => G.Adj x z)).card := by
  classical
  apply (hS x hx).trans_le
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzS, haz⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcap z hzS haz), haz⟩

/-- Intermediate paths are supplied by the subsequent original saturation wrapper. -/
theorem good_set_clique (G : SimpleGraph V) (K : ℕ) (S : Finset V)
    (hK : 5 ≤ K) (hS : GoodCore G ((K - 1) / 2) S)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hpaths : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.Adj x y →
      ∃ P : G.Walk x y, P.IsPath ∧ K ≤ P.length + 1) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y := by
  classical
  intro x hx y hy hxy
  by_contra hmissing
  obtain ⟨P, hp, hKP⟩ := hpaths x hx y hy hxy hmissing
  obtain ⟨a, ha, b, hb, Q, hQ, _hab, hPQ, _hmax, hleft, hright⟩ :=
    EndpointCapture.exists_captured_family_maximum
      (G := G) (x := x) (y := y) (K := K)
      S S P hp hx hy hmissing hK hKP noLong
  have hKQ : K ≤ Q.length + 1 := longer_path_long K P.length Q.length hKP hPQ
  have hL := captured_good_degree G ((K - 1) / 2) S hS Q a ha hleft
  have hR := captured_good_degree G ((K - 1) / 2) S hS Q b hb hright
  have hsum : K ≤
      (Q.support.toFinset.filter (fun z => G.Adj (Q.getVert 0) z)).card +
      (Q.support.toFinset.filter (fun z => G.Adj (Q.getVert Q.length) z)).card := by
    simpa only [Walk.getVert_zero, Walk.getVert_length] using
      core_endpoint_sum K _ _ hK hL hR
  have hdelQ : ∀ i : Fin (Q.length + 1), 0 < i → i < Fin.last Q.length →
      (G.induce {w | w ≠ Q.getVert i.val}).Connected := by
    intro i _hi _hilast
    exact hdel (Q.getVert i.val)
  obtain ⟨C, hC, hKC⟩ :=
    BoundaryEndpoint.uniform_endpoint_vertex_threshold Q hQ hdelQ K hK hKQ hsum
  exact (Nat.not_le_of_gt (noLong (Q.getVert 0) C hC)) hKC

theorem saturated_core_clique (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ G.Adj u v →
      ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (G ⊔ fromEdgeSet {s(u, v)}))) :
    ∀ x ∈ degreeCore G ((K - 1) / 2), ∀ y ∈ degreeCore G ((K - 1) / 2),
      x ≠ y → G.Adj x y := by
  apply good_set_clique G K (degreeCore G ((K - 1) / 2)) hK
    (degree_core_good G ((K - 1) / 2))
    (AllLongSaturation.no_long_cycle G hK hfree) hdel
  intro x _hx y _hy hxy hmissing
  obtain ⟨m, hKm, ⟨f⟩⟩ := hsat x y hxy hmissing
  obtain ⟨P, hp, hlen⟩ :=
    AllLongSaturation.added_pair_path (G := G) (u := x) (v := y) (m := m)
      (cycle_order_gt_two K m hK hKm) (hfree m hKm) hxy hmissing f
  exact ⟨P, hp, extracted_path_long K m P.length hK hKm hlen⟩

theorem exists_saturated_clique_core
    (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      (∀ x ∈ degreeCore H ((K - 1) / 2), ∀ y ∈ degreeCore H ((K - 1) / 2),
        x ≠ y → H.Adj x y) := by
  obtain ⟨H, hGH, hHfree, hHdel, hHsat⟩ :=
    AllLongSaturation.exists_connected_all_long_saturated_supergraph G K hfree hdel
  exact ⟨H, hGH, hHfree, hHdel, hHsat,
    saturated_core_clique H hK hHfree hHdel hHsat⟩

end ErdosProblems.PathUpperReduction.CoreCliqueCheckpoint1105
