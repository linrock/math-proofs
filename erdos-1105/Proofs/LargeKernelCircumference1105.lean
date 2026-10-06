module

public import LongCycleFromMinimumDegree1105
public import EvenConnectedLargeKernel1105
public import PathOriginalConnectedStep1105
public import Erdos1105UniversalPathReduction
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
2-connectedness and `2 * d`-cycle existence for large kernels `|K| ≥ 2 * d + 2`
whenever `Drem < d.choose 2` (which holds across the entire finite base window
`2 * d + 2 ≤ n ≤ 2 * d + 2 + (d - 1) / 2` and up to `n ≤ d + 2 + d.choose 2`),
closing the connected representative step for all `d ≥ 4` (`k = 2 * d + 2 ≥ 10`).
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.LargeKernelCircumference1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.LongCycleFromMinimumDegree1105
open ErdosProblems.PathUpperReduction.EvenConnectedLargeKernel1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-- When `degreeCore G d = ∅`, `∀ x ∈ K, d ≤ withinDegree G K x`, and
`Drem < d.choose 2`, any subset `W ⊆ K` obtained by deleting at most one vertex
(`(K \ W).card ≤ 1`) induces a connected subgraph `G.induce W`. -/
theorem connected_induce_of_sdiff_le_one
    (G : SimpleGraph V) (d : ℕ) (K W : Finset V) (Drem : ℕ)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hKlarge : 2 * d + 2 ≤ K.card) (hWK : W ⊆ K) (hsdiff : (K \ W).card ≤ 1)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hDrem : Drem < d.choose 2)
    (hKcount : (withinEdges G K).card + Drem = d.choose 2 + d * (K.card - d)) :
    (G.induce (W : Set V)).Connected := by
  classical
  let H := G.induce (W : Set V)
  have hWcardEq : W.card + (K \ W).card = K.card := by
    rw [Finset.card_sdiff_of_subset hWK]
    have hle := Finset.card_le_card hWK
    omega
  have hWpos : 0 < W.card := by omega
  obtain ⟨z0, hz0⟩ := Finset.card_pos.mp hWpos
  have hne : Nonempty (W : Set V) := ⟨⟨z0, hz0⟩⟩
  by_contra hnotConn
  have hnotPre : ¬ H.Preconnected := fun hpre => hnotConn ⟨hpre⟩
  unfold SimpleGraph.Preconnected at hnotPre
  push Not at hnotPre
  obtain ⟨u, v, hnotReach⟩ := hnotPre
  let A : Finset V := W.filter (fun x => ∃ hx : x ∈ W, H.Reachable u ⟨x, hx⟩)
  let B : Finset V := W \ A
  have hAW : A ⊆ W := Finset.filter_subset _ _
  have hBW : B ⊆ W := Finset.sdiff_subset
  have huA : u.val ∈ A :=
    Finset.mem_filter.mpr ⟨u.property, ⟨u.property, SimpleGraph.Reachable.rfl⟩⟩
  have hvB : v.val ∈ B := by
    refine Finset.mem_sdiff.mpr ⟨v.property, ?_⟩
    intro hvA
    obtain ⟨_, hvW, hr⟩ := Finset.mem_filter.mp hvA
    exact hnotReach hr
  have hnoAB : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
    intro x hxA y hyB hxy
    obtain ⟨hxW, _, hux⟩ := Finset.mem_filter.mp hxA
    obtain ⟨hyW, hyNotA⟩ := Finset.mem_sdiff.mp hyB
    have hadjH : H.Adj ⟨x, hxW⟩ ⟨y, hyW⟩ := hxy
    exact hyNotA (Finset.mem_filter.mpr ⟨hyW, ⟨hyW, hux.trans hadjH.reachable⟩⟩)
  let A1 : Finset V := K \ B
  let B1 : Finset V := K \ A
  have hA1sub : K.filter (fun z => G.Adj u.val z) ⊆ A1 := by
    intro z hz
    obtain ⟨hzK, huz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_sdiff.mpr ⟨hzK, fun hzB => hnoAB u.val huA z hzB huz⟩
  have hB1sub : K.filter (fun z => G.Adj v.val z) ⊆ B1 := by
    intro z hz
    obtain ⟨hzK, hvz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_sdiff.mpr ⟨hzK, fun hzA => hnoAB z hzA v.val hvB hvz.symm⟩
  have hdA1 : d ≤ A1.card :=
    (hmin u.val (hWK u.property)).trans (Finset.card_le_card hA1sub)
  have hdB1 : d ≤ B1.card :=
    (hmin v.val (hWK v.property)).trans (Finset.card_le_card hB1sub)
  have hABcard : A.card + B.card = W.card := by
    dsimp [B]
    rw [Finset.card_sdiff_of_subset hAW]
    have hle := Finset.card_le_card hAW
    omega
  have hA1card : A1.card = K.card - B.card :=
    Finset.card_sdiff_of_subset (hBW.trans hWK)
  have hB1card : B1.card = K.card - A.card :=
    Finset.card_sdiff_of_subset (hAW.trans hWK)
  have hBcardLe : B.card ≤ K.card := Finset.card_le_card (hBW.trans hWK)
  have hAcardLe : A.card ≤ K.card := Finset.card_le_card (hAW.trans hWK)
  have hsumCards : A1.card + B1.card ≤ K.card + 1 := by omega
  have hCA1 : degreeCore G d ⊆ A1 := by rw [hC]; exact Finset.empty_subset _
  have hCB1 : degreeCore G d ⊆ B1 := by rw [hC]; exact Finset.empty_subset _
  have hMA1 : max d (degreeCore G d).card ≤ A1.card := by
    rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)]
    exact hdA1
  have hMB1 : max d (degreeCore G d).card ≤ B1.card := by
    rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)]
    exact hdB1
  have hEdgesA1 : (withinEdges G A1).card ≤ d.choose 2 + d * (A1.card - d) := by
    simpa only [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      core_induced_edge_bound G d A1 hCA1 hMA1
  have hEdgesB1 : (withinEdges G B1).card ≤ d.choose 2 + d * (B1.card - d) := by
    simpa only [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      core_induced_edge_bound G d B1 hCB1 hMB1
  have hEdgesSub : withinEdges G K ⊆ withinEdges G A1 ∪ withinEdges G B1 := by
    intro e he
    obtain ⟨heG, heK⟩ := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := by simpa only [mem_edgeFinset, mem_edgeSet] using heG
      have hxK : x ∈ K := heK (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y))
      have hyK : y ∈ K := heK (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y))
      by_cases hxB : x ∈ B
      · have hxNotA : x ∉ A := (Finset.mem_sdiff.mp hxB).2
        have hyNotA : y ∉ A := fun hyA => hnoAB y hyA x hxB hxy.symm
        apply Finset.mem_union_right
        refine Finset.mem_filter.mpr ⟨heG, ?_⟩
        intro z hz
        rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hz) with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨hxK, hxNotA⟩
        · exact Finset.mem_sdiff.mpr ⟨hyK, hyNotA⟩
      · by_cases hyB : y ∈ B
        · have hyNotA : y ∉ A := (Finset.mem_sdiff.mp hyB).2
          have hxNotA : x ∉ A := fun hxA => hnoAB x hxA y hyB hxy
          apply Finset.mem_union_right
          refine Finset.mem_filter.mpr ⟨heG, ?_⟩
          intro z hz
          rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hz) with rfl | rfl
          · exact Finset.mem_sdiff.mpr ⟨hxK, hxNotA⟩
          · exact Finset.mem_sdiff.mpr ⟨hyK, hyNotA⟩
        · apply Finset.mem_union_left
          refine Finset.mem_filter.mpr ⟨heG, ?_⟩
          intro z hz
          rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hz) with rfl | rfl
          · exact Finset.mem_sdiff.mpr ⟨hxK, hxB⟩
          · exact Finset.mem_sdiff.mpr ⟨hyK, hyB⟩
  have hEdgesUnion : (withinEdges G K).card ≤
      (withinEdges G A1).card + (withinEdges G B1).card :=
    (Finset.card_le_card hEdgesSub).trans (Finset.card_union_le _ _)
  have hpred : d - 1 + 1 = d := by omega
  have hdouble : 2 * d.choose 2 = d * (d - 1) := by
    have h := Nat.add_one_mul_choose_eq (d - 1) 1
    rw [hpred, Nat.choose_one_right] at h
    simpa only [Nat.reduceAdd, Nat.mul_comm] using h.symm
  have hmulLe : d * (A1.card - d) + d * (B1.card - d) ≤ d * (K.card + 1 - 2 * d) := by
    rw [← Nat.mul_add]
    apply Nat.mul_le_mul_left
    omega
  have hident : d * (d - 1) + d * (K.card + 1 - 2 * d) = d * (K.card - d) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

/-- When `Drem < d.choose 2` and `2 * d + 2 ≤ K.card`, `G.induce K` is 2-connected
and has minimum degree `≥ d`, so `LongCycleFromMinimumDegree1105` produces a cycle
walk of length `2 * d` in `G`. -/
theorem exists_exact_cycle_of_large_kernel_small_deficit
    (G : SimpleGraph V) (d : ℕ) (K : Finset V) (Drem : ℕ)
    (hd : 4 ≤ d) (hconn : G.Connected) (hVlarge : 2 * d + 2 ≤ Fintype.card V)
    (hC : degreeCore G d = ∅) (hKlarge : 2 * d + 2 ≤ K.card)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hDrem : Drem < d.choose 2)
    (hKcount : (withinEdges G K).card + Drem = d.choose 2 + d * (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ x : V, ∃ C : G.Walk x x, C.IsCycle ∧ C.length = 2 * d := by
  classical
  let H := G.induce (K : Set V)
  have hKtype : 2 * d + 2 ≤ Fintype.card (K : Set V) := by
    have hc : Fintype.card (K : Set V) = K.card :=
      Fintype.card_of_finset' (p := (K : Set V)) K (fun _ => Iff.rfl)
    omega
  have hHconn : H.Connected := by
    have hsdiff : (K \ K).card ≤ 1 := by simp
    exact connected_induce_of_sdiff_le_one G d K K Drem hd hC hKlarge
      (Finset.Subset.refl K) hsdiff hmin hDrem hKcount
  have hHdel : ∀ z : (K : Set V), (H.induce {w | w ≠ z}).Connected := by
    intro z
    let W : Finset V := K.erase z.val
    have hWK : W ⊆ K := Finset.erase_subset z.val K
    have hsdiff : (K \ W).card ≤ 1 := by
      have hsub : K \ W ⊆ {z.val} := by
        intro x hx
        obtain ⟨hxK, hxW⟩ := Finset.mem_sdiff.mp hx
        by_contra hxz
        exact hxW (Finset.mem_erase.mpr ⟨fun h => hxz (Finset.mem_singleton.mpr h), hxK⟩)
      exact (Finset.card_le_card hsub).trans (by simp)
    have hWconn : (G.induce (W : Set V)).Connected :=
      connected_induce_of_sdiff_le_one G d K W Drem hd hC hKlarge
        hWK hsdiff hmin hDrem hKcount
    let e : (W : Set V) ≃ {w : (K : Set V) | w ≠ z} :=
      { toFun := fun u =>
          ⟨⟨u.val, (Finset.mem_erase.mp u.property).2⟩,
            fun h => (Finset.mem_erase.mp u.property).1 (congrArg Subtype.val h)⟩
        invFun := fun u =>
          ⟨u.val.val, Finset.mem_erase.mpr
            ⟨fun h => u.property (Subtype.ext h), u.val.property⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
    let iso : G.induce (W : Set V) ≃g H.induce {w | w ≠ z} :=
      { toEquiv := e
        map_rel_iff' := by
          intro a b
          rfl }
    exact (SimpleGraph.Iso.connected_iff iso).mp hWconn
  have hHdeg : ∀ z : (K : Set V), d ≤ Nat.card (H.neighborSet z) := by
    intro z
    rw [Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree,
      ActualInducedDegree1105.degree_induce_eq_withinDegree G K z]
    exact hmin z.val z.property
  obtain ⟨x0, CK, hCK, hCKlen⟩ :=
    exists_long_cycle_of_minimum_degree H d hd hKtype hHconn hHdel hHdeg
  let emb : H ↪g G := SimpleGraph.Embedding.induce (K : Set V)
  let C : G.Walk x0.val x0.val := CK.map emb.toHom
  have hC : C.IsCycle := hCK.map emb.injective
  have hClen : 2 * d ≤ C.length := by
    change 2 * d ≤ (CK.map emb.toHom).length
    rw [SimpleGraph.Walk.length_map]
    exact hCKlen
  have hpathBound : ∀ a b : V, ∀ P : G.Walk a b, P.IsPath → P.length ≤ 2 * d := by
    intro a b P hp
    by_contra hlong
    have hlen : 2 * d + 2 ≤ P.length + 1 := by omega
    have hcopy : (pathGraph (P.length + 1)).Copy G := hp.pathGraphCopy
    let f : (pathGraph (2 * d + 2)) →g pathGraph (P.length + 1) :=
      { toFun := fun i => ⟨i.val, by omega⟩
        map_rel' := by
          intro i j hij
          simpa only [pathGraph_adj] using hij }
    have hfinj : Function.Injective f := by
      intro i j hij
      exact Fin.ext (congrArg (fun x : Fin (P.length + 1) => x.val) hij)
    exact hfree ⟨hcopy.comp ⟨f, hfinj⟩⟩
  have hCdrop : C.dropLast.length ≤ 2 * d :=
    hpathBound _ _ C.dropLast hC.isPath_dropLast
  have hCstep := SimpleGraph.Walk.length_dropLast_add_one hC.not_nil
  have hCneq : C.length ≠ 2 * d + 1 :=
    LongCycleOutside1105.no_cycle_of_order_one_below_forbidden_path
      G hconn d hVlarge hfree C hC
  exact ⟨x0.val, C, hC, by omega⟩

/-- For any `d ≥ 4` and any `n` with `2 * d + 2 ≤ n ≤ d + 2 + d.choose 2`
(which contains the entire base window `2 * d + 2 ≤ n ≤ 2 * d + 2 + (d - 1) / 2`),
every connected representative of a rainbow-`P_{2d+2}`-free coloring satisfies
`q ≤ max ((2 * d).choose 2 + 1) ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2)`. -/
theorem connected_even_path_upper_of_le_choose_window {d n q : ℕ}
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) (hwin : n ≤ d + 2 + d.choose 2)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (hconn : (selectedGraph χ r).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) :
    q ≤ max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  classical
  by_contra hqNotLe
  have hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q := Nat.lt_of_not_ge hqNotLe
  obtain ⟨hC, K, hKS, _hKlower, hK2d3, hKmin, Drem, _hDrem0, hDremBound,
      hKcount, _c, _w, _htrace, _hcharge, _hw, _hslack, _hsteps, _hoccurs,
      _W, _hWK, _hWcard, _hWdegree⟩ :=
    exists_connected_original_color_large_kernel hd hn χ r hconn hno hq
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  have hKle : K.card ≤ n := by
    have hc := Finset.card_le_card hKS
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have hDremLt : Drem < d.choose 2 := by omega
  have hVlarge : 2 * d + 2 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hn
  have hfreeG : (pathGraph (2 * d + 2)).Free G :=
    selectedGraph_free (pathGraph (2 * d + 2)) χ r hno
  obtain ⟨x, P, hP, hPlen⟩ :=
    exists_exact_cycle_of_large_kernel_small_deficit
      G d K Drem hd hconn hVlarge hC (by omega) hKmin hDremLt hKcount hfreeG
  obtain ⟨H, hHcard, hCoverUniv⟩ :=
    exists_cover_of_large_kernel_and_cycle G d K hconn hVlarge
      (by omega) hKmin hfreeG P hP hPlen
  obtain ⟨Q, hQ⟩ :=
    EvenCoverColorCaller1105.rainbow_path_of_actual_vertex_cover_above_even_max
      hd hn χ r H hHcard hCoverUniv hq
  exact hno Q hQ

/-- Strong induction across `2 * d + 2 ≤ n ≤ d + 2 + d.choose 2` discharges
disconnected representatives via `PathOriginalConnectedStep1105`, proving the
upper bound on the entire choose window (and hence on the finite base window
`2 * d + 2 ≤ n ≤ 2 * d + 2 + (d - 1) / 2`) for every `d ≥ 4`. -/
theorem antiRamseyNum_even_path_le_on_choose_window (d : ℕ) (hd : 4 ≤ d) :
    ∀ n : ℕ, 2 * d + 2 ≤ n → n ≤ d + 2 + d.choose 2 →
      antiRamseyNum (pathGraph (2 * d + 2)) n ≤
        max ((2 * d).choose 2 + 1)
          ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  have hformula (m : ℕ) :
      ErdosProblems.PathLemmaFourScalar.pathFormula m (2 * d + 2) =
        max ((2 * d).choose 2 + 1)
          ((d - 1).choose 2 + (d - 1) * (m - d + 1) + 2) := by
    unfold ErdosProblems.PathLemmaFourScalar.pathFormula
    have heven : ¬ Odd (2 * d + 2) := by rintro ⟨r, hr⟩; omega
    have hquot : (2 * d + 2 - 1) / 2 = d := by omega
    have hsub : 2 * d + 2 - 2 = 2 * d := by omega
    simp only [hquot, hsub, ite_eq_right heven]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hwin
    classical
    let k := 2 * d + 2
    have hk8 : 8 ≤ k := by dsimp [k]; omega
    let admissible : Set ℕ :=
      {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
        ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
          ¬ IsRainbow P.toHom χ}
    have hbounded : BddAbove admissible := by
      refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
      intro q hq
      obtain ⟨χ, hχ, _⟩ := hq
      simpa using Fintype.card_le_of_surjective χ hχ
    rw [← hformula n]
    change sSup admissible ≤ _
    apply (csSup_le_iff' hbounded).2
    intro q hq
    obtain ⟨χ, hχ, hno⟩ := hq
    have hIH : OriginalFullSmallerHostIH k n := by
      intro m hkm hmn
      rw [hformula m]
      exact ih m hmn hkm (by omega)
    have hstep : OriginalConnectedPathStep k n := by
      intro q' χ' R' _hkn hconn' hno' _hIH'
      rw [hformula n]
      exact connected_even_path_upper_of_le_choose_window
        hd hn hwin χ' R' hconn' hno'
    exact original_color_count_le_formula_of_connected_step_and_full_IH
      hk8 hn hstep χ hχ hno hIH

/-- For every `d ≥ 4`, the finite base window `2 * d + 2 ≤ n ≤ 2 * d + 2 + (d - 1) / 2`
is contained in `n ≤ d + 2 + d.choose 2`, so the upper bound holds on the finite
base window. -/
theorem antiRamseyNum_even_path_le_on_base_window (d : ℕ) (hd : 4 ≤ d)
    (n : ℕ) (hn : 2 * d + 2 ≤ n) (hwin : n ≤ 2 * d + 2 + (d - 1) / 2) :
    antiRamseyNum (pathGraph (2 * d + 2)) n ≤
      max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  have hpred : d - 1 + 1 = d := by omega
  have hdouble : 2 * d.choose 2 = d * (d - 1) := by
    have h := Nat.add_one_mul_choose_eq (d - 1) 1
    rw [hpred, Nat.choose_one_right] at h
    simpa only [Nat.reduceAdd, Nat.mul_comm] using h.symm
  have h4d : 4 * (d - 1) ≤ d * (d - 1) :=
    Nat.mul_le_mul_right (d - 1) (by omega)
  have hchoose : n ≤ d + 2 + d.choose 2 := by omega
  exact antiRamseyNum_even_path_le_on_choose_window d hd n hn hchoose

/-- Unconditional exact Formal Conjectures formula for all even paths `P_{2d+2}`
with `d ≥ 4` (`k ≥ 10` even) and ALL host orders `n ≥ 2 * d + 2`. -/
theorem erdos_1105_even_paths_ge_ten_exact (d n : ℕ) (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) :
    let k := 2 * d + 2
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) :=
  Erdos1105UniversalPathReduction.even_path_exact_of_finite_window d (by omega)
    (antiRamseyNum_even_path_le_on_base_window d hd) n hn

end ErdosProblems.PathUpperReduction.LargeKernelCircumference1105
