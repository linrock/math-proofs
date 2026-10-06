module

public import CoreEndpointBound1105
public import SecondCoreCount1105

@[expose] public section

/-!
The nonempty core interval is derived for the actual saturated H; the final
statement supplies no core, saturation or maximum-path premise. All cycle
orders at least K and every actual vertex deletion remain in its hypotheses. K <= the actual host order guards both truncated-subtraction rewrites. The
empty core retains its separate count. This is an ordinary graph bound, not
the full original-color path theorem, stability theorem or induction.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.GraphCoreBound1105

theorem long_cycle_free_edge_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hKN : K ≤ Fintype.card V)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    Nat.card G.edgeSet ≤
      max (CoreEndpointBound1105.extremalCount (Fintype.card V) K 2)
        (CoreEndpointBound1105.extremalCount (Fintype.card V) K ((K - 1) / 2)) := by
  classical
  obtain ⟨H, hGH, hHfree, hHdel, hHsat, hHnonempty, hHempty⟩ :=
    SecondCoreCount1105.exists_saturated_core_count G hK hKN hfree hdel
  have hEdges : Nat.card G.edgeSet ≤ Nat.card H.edgeSet :=
    Nat.card_mono (Set.toFinite H.edgeSet) (SimpleGraph.edgeSet_mono hGH)
  let C := degreeCore H ((K - 1) / 2)
  by_cases hC : C.Nonempty
  · have hinterval := CoreSizeUpper1105.nonempty_core_size_interval
      H hK hKN hHfree hHdel hHsat hC
    change (K - 1) / 2 + 2 ≤ C.card ∧ C.card ≤ K - 2 at hinterval
    let a := K - C.card
    have ha2 : 2 ≤ a := by
      dsimp [a]
      omega
    have hat : a ≤ (K - 1) / 2 := by
      dsimp [a]
      omega
    have hKa : K - a = C.card := by
      dsimp [a]
      omega
    have hNa : Fintype.card V - K + a = Fintype.card V - C.card := by
      dsimp [a]
      omega
    have hHcount := (hHnonempty hC).2
    change Nat.card H.edgeSet ≤ C.card.choose 2 +
      (K - C.card) * (Fintype.card V - C.card) at hHcount
    have hHscalar : Nat.card H.edgeSet ≤
        CoreEndpointBound1105.extremalCount (Fintype.card V) K a := by
      unfold CoreEndpointBound1105.extremalCount
      rw [hKa, hNa]
      exact hHcount
    exact hEdges.trans (hHscalar.trans
      (CoreEndpointBound1105.extremalCount_endpoints
        (Fintype.card V) K a hK hKN ha2 hat))
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    have hHcount := hHempty hCempty
    have hHscalar : Nat.card H.edgeSet ≤
        CoreEndpointBound1105.extremalCount (Fintype.card V) K ((K - 1) / 2) :=
      hHcount.trans (CoreEndpointBound1105.emptyCoreCount_le_endpoint
        (Fintype.card V) K hK hKN)
    exact hEdges.trans (hHscalar.trans (le_max_right _ _))

end ErdosProblems.PathUpperReduction.GraphCoreBound1105
