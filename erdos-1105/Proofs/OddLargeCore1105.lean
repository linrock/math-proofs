module

public import SecondCoreCount1105
public import UniformWindowScalar

@[expose] public section

/-!
Actual SAME-H odd-core application, with no supplied core,
nonemptiness, clique, deletion order, count oracle or container conclusion. The graph-density premise is explicit; an original-color cone caller must
derive it from its actual full selected representative and graph inclusion.

The
new specialized odd-cone scalar reuses the accepted base interval endpoint
theorem after the accepted cone shift; no new convexity helper is needed.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.OddLargeCore1105

/-- The actual greatest ell-core of the SAME saturated graph has K-2 vertices
under the literal original odd high-palette density. Empty cores are excluded
by their own non-strict count; the surviving d=2 slot is not discarded. -/
theorem saturated_odd_core_card_eq {V : Type*} [Fintype V]
    (H : SimpleGraph V) (ell n q : ℕ)
    (hell : 4 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (hN : Fintype.card V = n + 1)
    (hfree : ∀ m, 2 * ell + 2 ≤ m → (cycleGraph m).Free H)
    (hdel : ∀ z, (H.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ H.Adj u v →
      ∃ m, 2 * ell + 2 ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (H ⊔ fromEdgeSet {s(u, v)})))
    (hlower : n + q ≤ Nat.card H.edgeSet)
    (hq : max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) < q) :
    (degreeCore H ell).card = 2 * ell := by
  classical
  have hK : 5 ≤ 2 * ell + 2 := by omega
  have hKN : 2 * ell + 2 ≤ Fintype.card V := by rw [hN]; omega
  have hhalf : (2 * ell + 2 - 1) / 2 = ell := by omega
  have hstrict := UniformWindowScalar1105.odd_palette_strict_cone_threshold
    ell n q hell hn hq
  let C := degreeCore H ell
  have hC : C.Nonempty := by
    by_contra hC
    have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    have hdN : ell ≤ Fintype.card V := by omega
    have hcount := SecondCoreCount1105.empty_core_edge_bound H ell hdN hCempty
    rw [hN] at hcount
    have hendpoint := CoreEndpointBound1105.emptyCoreCount_le_endpoint
      (n + 1) (2 * ell + 2) hK (by omega)
    rw [hhalf] at hendpoint
    have hle := hlower.trans (hcount.trans hendpoint)
    have hmax : n + q ≤
        max (CoreEndpointBound1105.extremalCount (n + 1) (2 * ell + 2) 3)
          (CoreEndpointBound1105.extremalCount (n + 1) (2 * ell + 2) ell) :=
      hle.trans (le_max_right _ _)
    exact (not_lt_of_ge hmax) hstrict
  have hC' : (degreeCore H ((2 * ell + 2 - 1) / 2)).Nonempty := by
    rw [hhalf]
    exact hC
  have hinterval := CoreSizeUpper1105.nonempty_core_size_interval
    H hK hKN hfree hdel hsat hC'
  rw [hhalf] at hinterval
  change ell + 2 ≤ C.card ∧ C.card ≤ 2 * ell + 2 - 2 at hinterval
  change C.card = 2 * ell
  by_contra hneq
  let d := 2 * ell + 2 - C.card
  have hd3 : 3 ≤ d := by dsimp [d]; omega
  have hdell : d ≤ ell := by dsimp [d]; omega
  have hKd : 2 * ell + 2 - d = C.card := by dsimp [d]; omega
  have hNd : Fintype.card V - (2 * ell + 2) + d =
      Fintype.card V - C.card := by dsimp [d]; omega
  have hcount := SecondCoreCount1105.nonempty_core_edge_bound
    H hK hKN hfree hdel hsat hC'
  rw [hhalf] at hcount
  change Nat.card H.edgeSet ≤ C.card.choose 2 +
    (2 * ell + 2 - C.card) * (Fintype.card V - C.card) at hcount
  have hscalar : Nat.card H.edgeSet ≤
      CoreEndpointBound1105.extremalCount (Fintype.card V) (2 * ell + 2) d := by
    unfold CoreEndpointBound1105.extremalCount
    rw [hKd, hNd]
    exact hcount
  rw [hN] at hscalar
  have hend := UniformWindowScalar1105.odd_cone_intermediate_count_le_endpoints
    ell n d hell hn hd3 hdell
  exact (not_lt_of_ge (hlower.trans (hscalar.trans hend))) hstrict

end ErdosProblems.PathUpperReduction.OddLargeCore1105
