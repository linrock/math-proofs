module

public import CoreSizeUpper1105
public import CoreElimination

@[expose] public section

/-!
Same-graph second-core identity and actual edge count. candidate;
all original freedom, deletion-connectivity and saturation hypotheses remain. The empty-core branch uses its own exact generic count, without nonemptiness.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.SecondCoreCount1105

variable {V : Type*}

theorem good_core_degree_mono (G : SimpleGraph V) (d e : ℕ) (S : Finset V)
    (hde : d ≤ e) (hS : GoodCore G e S) : GoodCore G d S := by
  intro x hx
  exact lt_of_le_of_lt hde (hS x hx)

variable [Fintype V]

theorem degree_core_antitone (G : SimpleGraph V) (d e : ℕ) (hde : d ≤ e) :
    degreeCore G e ⊆ degreeCore G d := by
  exact good_subset_core G d (degreeCore G e)
    (good_core_degree_mono G d e (degreeCore G e) hde (degree_core_good G e))

theorem saturated_second_core_eq (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ G.Adj u v →
      ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (G ⊔ fromEdgeSet {s(u, v)})))
    (hC : (degreeCore G ((K - 1) / 2)).Nonempty) :
    degreeCore G (K - (degreeCore G ((K - 1) / 2)).card) =
      degreeCore G ((K - 1) / 2) := by
  classical
  let t := (K - 1) / 2
  let C := degreeCore G t
  let r := C.card
  let d := K - r
  let D := degreeCore G d
  have hlow : t + 2 ≤ r :=
    (CoreSizeUpper1105.nonempty_core_size_interval G hK hKN hfree hdel hsat hC).1
  have hupp : r ≤ K - 2 :=
    (CoreSizeUpper1105.nonempty_core_size_interval G hK hKN hfree hdel hsat hC).2
  have hrK : r ≤ K := by omega
  have htr : t < r := by omega
  have hdt : d ≤ t := by
    dsimp [d, t]
    dsimp [t] at hlow
    omega
  have hcl : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → G.Adj x y :=
    CoreCliqueCheckpoint1105.saturated_core_clique G hK hfree hdel hsat
  have hCD : C ⊆ D := degree_core_antitone G d t hdt
  have hDC : D ⊆ C := by
    intro x hxD
    by_contra hxC
    have hmissing : ∃ y ∈ C, ¬ G.Adj x y := by
      by_contra hnone
      have hall : ∀ y ∈ C, G.Adj x y := by
        intro y hy
        by_contra hxy
        exact hnone ⟨y, hy, hxy⟩
      have hgood := CoreSizeUpper1105.insert_good_of_all_neighbors G t C
        (degree_core_good G t) htr x hall
      have hxcore := good_subset_core G t (insert x C) hgood
        (Finset.mem_insert_self x C)
      exact hxC hxcore
    obtain ⟨y, hy, hxy⟩ := hmissing
    have hne : x ≠ y := by
      intro heq
      subst y
      exact hxC hy
    obtain ⟨m, hKm, ⟨f⟩⟩ := hsat x y hne hxy
    obtain ⟨P, hp, hlen⟩ := AllLongSaturation.added_pair_path
      (G := G) (u := x) (v := y) (m := m)
      (CoreCliqueCheckpoint1105.cycle_order_gt_two K m hK hKm)
      (hfree m hKm) hne hxy f
    have hKP : K ≤ P.length + 1 :=
      CoreCliqueCheckpoint1105.extracted_path_long K m P.length hK hKm hlen
    have noLong := AllLongSaturation.no_long_cycle G hK hfree
    obtain ⟨a, ha, b, hb, Q, hQ, _hab, hPQ, _hmax, hleft, hright⟩ :=
      EndpointCapture.exists_captured_family_maximum
        (G := G) (x := x) (y := y) (K := K)
        D C P hp hxD hy hxy hK hKP noLong
    have hKQ : K ≤ Q.length + 1 := by omega
    have hL : d < (Q.support.toFinset.filter (fun z => G.Adj a z)).card :=
      CoreCliqueCheckpoint1105.captured_good_degree G d D
        (degree_core_good G d) Q a ha hleft
    have hrsub : C.erase b ⊆ Q.support.toFinset.filter (fun z => G.Adj b z) := by
      intro z hz
      obtain ⟨hzb, hzC⟩ := Finset.mem_erase.mp hz
      have hbz : G.Adj b z := hcl b hb z hzC (Ne.symm hzb)
      exact Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr (hright z hzC hbz), hbz⟩
    have hR : r - 1 ≤ (Q.support.toFinset.filter (fun z => G.Adj b z)).card := by
      have hle := Finset.card_le_card hrsub
      rw [Finset.card_erase_of_mem hb] at hle
      exact hle
    have hsum : K ≤
        (Q.support.toFinset.filter (fun z => G.Adj (Q.getVert 0) z)).card +
        (Q.support.toFinset.filter (fun z => G.Adj (Q.getVert Q.length) z)).card := by
      simp only [Walk.getVert_zero, Walk.getVert_length]
      dsimp [d] at hL
      omega
    have hdelQ : ∀ i : Fin (Q.length + 1), 0 < i → i < Fin.last Q.length →
        (G.induce {w | w ≠ Q.getVert i.val}).Connected := by
      intro i _hi _hilast
      exact hdel (Q.getVert i.val)
    obtain ⟨Z, hZ, hKZ⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold
      Q hQ hdelQ K hK hKQ hsum
    exact (Nat.not_le_of_gt (noLong (Q.getVert 0) Z hZ)) hKZ
  exact Finset.Subset.antisymm hDC hCD

theorem nonempty_core_edge_bound (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ G.Adj u v →
      ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (G ⊔ fromEdgeSet {s(u, v)})))
    (hC : (degreeCore G ((K - 1) / 2)).Nonempty) :
    Nat.card G.edgeSet ≤ (degreeCore G ((K - 1) / 2)).card.choose 2 +
      (K - (degreeCore G ((K - 1) / 2)).card) *
        (Fintype.card V - (degreeCore G ((K - 1) / 2)).card) := by
  classical
  let t := (K - 1) / 2
  let C := degreeCore G t
  let r := C.card
  let d := K - r
  have hlow : t + 2 ≤ r :=
    (CoreSizeUpper1105.nonempty_core_size_interval G hK hKN hfree hdel hsat hC).1
  have hdr : d ≤ r := by
    dsimp [d]
    dsimp [t] at hlow
    omega
  have hNcard : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hdN : d ≤ Nat.card V := by
    rw [hNcard]
    dsimp [d]
    omega
  have heq : degreeCore G d = C :=
    saturated_second_core_eq G hK hKN hfree hdel hsat hC
  have hmax : max d (degreeCore G d).card = r := by
    rw [heq]
    exact max_eq_right hdr
  have hbound := CoreElimination.degree_core_edge_bound G d hdN
  rw [hmax, hNcard] at hbound
  exact hbound

theorem empty_core_edge_bound (G : SimpleGraph V) (d : ℕ)
    (hdN : d ≤ Fintype.card V) (hC : degreeCore G d = ∅) :
    Nat.card G.edgeSet ≤ d.choose 2 + d * (Fintype.card V - d) := by
  have hNcard : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hd : d ≤ Nat.card V := by rw [hNcard]; exact hdN
  have hbound := CoreElimination.degree_core_edge_bound G d hd
  rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d), hNcard] at hbound
  exact hbound

theorem exists_saturated_core_count (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      ((degreeCore H ((K - 1) / 2)).Nonempty →
        degreeCore H (K - (degreeCore H ((K - 1) / 2)).card) =
          degreeCore H ((K - 1) / 2) ∧
        Nat.card H.edgeSet ≤ (degreeCore H ((K - 1) / 2)).card.choose 2 +
          (K - (degreeCore H ((K - 1) / 2)).card) *
            (Fintype.card V - (degreeCore H ((K - 1) / 2)).card)) ∧
      (degreeCore H ((K - 1) / 2) = ∅ →
        Nat.card H.edgeSet ≤ ((K - 1) / 2).choose 2 +
          ((K - 1) / 2) * (Fintype.card V - (K - 1) / 2)) := by
  obtain ⟨H, hGH, hHfree, hHdel, hHsat, _hHcl, _hHsize⟩ :=
    CoreSizeUpper1105.exists_saturated_small_core G hK hKN hfree hdel
  refine ⟨H, hGH, hHfree, hHdel, hHsat, ?_, ?_⟩
  · intro hC
    exact ⟨saturated_second_core_eq H hK hKN hHfree hHdel hHsat hC,
      nonempty_core_edge_bound H hK hKN hHfree hHdel hHsat hC⟩
  · intro hC
    have htN : (K - 1) / 2 ≤ Fintype.card V := by omega
    exact empty_core_edge_bound H ((K - 1) / 2) htN hC

end ErdosProblems.PathUpperReduction.SecondCoreCount1105
