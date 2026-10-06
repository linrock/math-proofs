module

public import OddLargeCore1105
public import UniformConeStructure1105
public import PathUpperRainbowBridge

@[expose] public section

/-!
The exact original coloring and
its full RepresentativeChoice remain fixed. The connected-step interface
already supplies selectedGraph connectivity; no new existence or FULL IH is
assumed. Every saturated-graph premise and density is derived on ONE SAME
Option carrier, using the checked cone/count/selected-graph/saturation APIs.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)

namespace ErdosProblems.PathUpperReduction.ConnectedOddCore1105

/-- The SAME original full connected representative supplies the actual cone,
saturation and density. Preserve the actual core clique and apex/pullback
coupling for a subsequent original-color container exit. -/
theorem exists_connected_odd_saturated_large_core {ell n q : ℕ}
    (hell : 4 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) < q) :
    ∃ H : SimpleGraph (Option (Fin n)),
      cone (selectedGraph χ R) ≤ H ∧
      (∀ m, 2 * ell + 2 ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, 2 * ell + 2 ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      n + q ≤ Nat.card H.edgeSet ∧
      (∀ x ∈ degreeCore H ell, ∀ y ∈ degreeCore H ell,
        x ≠ y → H.Adj x y) ∧
      (degreeCore H ell).card = 2 * ell ∧
      H.IsUniversal none ∧
      none ∈ degreeCore H ell ∧
      H = cone (H.comap (some : Fin n → Option (Fin n))) ∧
      selectedGraph χ R ≤ H.comap (some : Fin n → Option (Fin n)) := by
  classical
  let M := selectedGraph χ R
  have hk : 5 ≤ 2 * ell + 1 := by omega
  have hMfree : (pathGraph (2 * ell + 1)).Free M :=
    selectedGraph_free (pathGraph (2 * ell + 1)) χ R hno
  have hc := UniformConeStructure1105.finite_connected_path_free_cone
    M hk hn hconn hMfree
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hK : 5 ≤ 2 * ell + 2 := by omega
  have hKN : 2 * ell + 2 ≤ Fintype.card (Option (Fin n)) := by rw [hN]; omega
  have hCfree : ∀ m, 2 * ell + 2 ≤ m → (cycleGraph m).Free (cone M) := by
    intro m hm
    exact hc.2.2.1 m (by omega)
  have hCdel : ∀ z, ((cone M).induce {w | w ≠ z}).Connected := by
    intro z
    exact hc.2.1 z
  obtain ⟨H, hCH, hHfree, hHdel, hHsat, hHclique, _hHupper⟩ :=
    CoreSizeUpper1105.exists_saturated_small_core
      (cone M) hK hKN hCfree hCdel
  have hMcount : Nat.card M.edgeSet = q := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      selectedGraph_card_edgeFinset χ R
  have hConeCount : Nat.card (cone M).edgeSet = Nat.card M.edgeSet + n := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc.2.2.2
  have hEdges : Nat.card (cone M).edgeSet ≤ Nat.card H.edgeSet := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      (Finset.card_le_card (SimpleGraph.edgeFinset_mono hCH))
  have hLower : n + q ≤ Nat.card H.edgeSet := by
    calc
      n + q = Nat.card M.edgeSet + n := by rw [hMcount]; omega
      _ = Nat.card (cone M).edgeSet := hConeCount.symm
      _ ≤ Nat.card H.edgeSet := hEdges
  have hCoreCard := OddLargeCore1105.saturated_odd_core_card_eq
    H ell n q hell hn hN hHfree hHdel hHsat hLower hq
  have hhalf : (2 * ell + 2 - 1) / 2 = ell := by omega
  rw [hhalf] at hHclique
  have hApex : H.IsUniversal none := by
    intro v hne
    exact hCH (UniformConeStructure1105.cone_apex_isUniversal M hne)
  have hApexCore : none ∈ degreeCore H ell := by
    by_contra hnot
    have hall : ∀ v ∈ degreeCore H ell, H.Adj none v := by
      intro v hv
      exact hApex (by intro heq; subst v; exact hnot hv)
    have hgood := CoreSizeUpper1105.insert_good_of_all_neighbors
      H ell (degreeCore H ell) (degree_core_good H ell)
      (by rw [hCoreCard]; omega) none hall
    exact hnot ((good_subset_core H ell _ hgood) (by simp))
  have hPullback : M ≤ H.comap (some : Fin n → Option (Fin n)) := by
    intro u v huv
    exact hCH huv
  have hConeEq : H = cone (H.comap (some : Fin n → Option (Fin n))) := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    cases u with
    | none =>
        cases v with
        | none =>
            change H.Adj none none ↔ False
            exact ⟨H.loopless.irrefl _, False.elim⟩
        | some v =>
            change H.Adj none (some v) ↔ True
            exact ⟨fun _ => True.intro, fun _ => hApex (by simp)⟩
    | some u =>
        cases v with
        | none =>
            change H.Adj (some u) none ↔ True
            exact ⟨fun _ => True.intro, fun _ => (hApex (by simp)).symm⟩
        | some v => rfl
  exact ⟨H, hCH, hHfree, hHdel, hHsat, hLower, hHclique, hCoreCard,
    hApex, hApexCore, hConeEq, hPullback⟩

end ErdosProblems.PathUpperReduction.ConnectedOddCore1105
