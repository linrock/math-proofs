module

public import LargeKernelCircumference1105
public import PathEightSpanningBase1105
public import PathEightWindmillCount1105
public import CycleGenericLongPathSeedV2
public import H3ResidualCount1105
public import H3ResidualStar1105
public import HighSeedLedgerBridge1105
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Unconditional proof of the `P_8` on `K_9` base (`antiRamseyNum (pathGraph 8) 9 = 17`),
all-host `P_8` formula, and the complete universal Formal Conjectures statement
`erdos_1105.parts.ii` for all `k ≥ 5` and all `n ≥ k`.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.PathEightNineBase1105

open SimpleGraph
open scoped BigOperators
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualTraceCarrierCut1105
open ErdosProblems.PathUpperReduction.ActualPrefixCarrierDegree1105
open ErdosProblems.PathUpperReduction.SmallKernelWholeSupport1105
open ErdosProblems.PathUpperReduction.EvenConnectedLargeKernel1105
open ErdosProblems.PathUpperReduction.LargeKernelCircumference1105
open ErdosProblems.PathUpperReduction.PathEightSpanningBase1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

section HighSeedPool

local instance (priority := 3000) subtypeNeighborSetFintypePool {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- `high_seed_degree_pool` holds for all `d ≥ 3` (`h ≥ 3`): the degree-sum gap is
identically `4 > 0`. -/
theorem high_seed_degree_pool_ge_three
    (G : SimpleGraph V) {d h : ℕ}
    (hd : 3 ≤ d) (hh : 3 ≤ h)
    (horder : Fintype.card V = d + h)
    (hedges : d * (d - 1) + 2 * d * h ≤
      2 * G.edgeFinset.card + 2 * (h - 3)) :
    d - 1 ≤ (Finset.univ.filter fun v : V => d + 1 ≤ G.degree v).card := by
  let S : Finset V := Finset.univ.filter fun v => d + 1 ≤ G.degree v
  by_contra hpool
  change ¬ d - 1 ≤ S.card at hpool
  have hsmall : S.card ≤ d - 2 := by omega
  have hdegree (v : V) :
      G.degree v ≤ d + (if v ∈ S then h - 1 else 0) := by
    split_ifs with hv
    · have hvmax := G.degree_lt_card_verts v
      rw [horder] at hvmax
      omega
    · have hvlow : ¬ d + 1 ≤ G.degree v := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hv
      omega
  have hpiece :
      (∑ v : V, if v ∈ S then h - 1 else 0) = S.card * (h - 1) := by
    calc
      _ = (∑ v : V, if v ∈ S then 1 else 0) * (h - 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp
      _ = S.card * (h - 1) := by
        rw [← Finset.card_eq_sum_ite (Finset.subset_univ S)]
  have hsum : (∑ v : V, G.degree v) ≤
      (d + h) * d + S.card * (h - 1) := by
    calc
      _ ≤ ∑ v : V, (d + (if v ∈ S then h - 1 else 0)) := by
        apply Finset.sum_le_sum
        intro v _
        exact hdegree v
      _ = (d + h) * d + S.card * (h - 1) := by
        rw [Finset.sum_add_distrib, hpiece, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, horder]
        simp only [Nat.cast_id]
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hupper : 2 * G.edgeFinset.card ≤
      (d + h) * d + (d - 2) * (h - 1) :=
    hsum.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (h - 1) hsmall) _)
  have hupperZ : (2 : ℤ) * (G.edgeFinset.card : ℤ) ≤
      ((d + h : ℕ) : ℤ) * (d : ℤ) +
        ((d - 2 : ℕ) : ℤ) * ((h - 1 : ℕ) : ℤ) := by
    exact_mod_cast hupper
  have hedgesZ : (d : ℤ) * ((d - 1 : ℕ) : ℤ) +
      2 * (d : ℤ) * (h : ℤ) ≤
        2 * (G.edgeFinset.card : ℤ) + 2 * ((h - 3 : ℕ) : ℤ) := by
    exact_mod_cast hedges
  simp only [Nat.cast_add,
    Nat.cast_sub (show 2 ≤ d by omega),
    Nat.cast_sub (show 1 ≤ d by omega),
    Nat.cast_sub (show 1 ≤ h by omega),
    Nat.cast_sub hh, Nat.cast_ofNat, Nat.cast_one] at hupperZ hedgesZ
  nlinarith

/-- `exists_actual_high_seed_subset` for `3 ≤ d`. -/
theorem exists_actual_high_seed_subset_ge_three
    (G : SimpleGraph V) (K : Finset V) {d h D : ℕ}
    (hd : 3 ≤ d) (hh : 3 ≤ h) (horder : K.card = d + h)
    (hD : D ≤ h - 3)
    (hbalance : (withinEdges G K).card + D = d.choose 2 + d * (K.card - d)) :
    ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  let JK := G.induce (K : Set V)
  have hkernelOrder : Fintype.card (K : Set V) = d + h :=
    (Fintype.card_of_finset' (p := (K : Set V)) K (fun _ => Iff.rfl)).trans horder
  have hsub : K.card - d = h := by omega
  have hkernelBalance : JK.edgeFinset.card + D = d.choose 2 + d * h := by
    rw [← HighSeedLedgerBridge1105.withinEdges_card_eq_induced G K, ← hsub]
    exact hbalance
  have hedges := HighSeedLedgerBridge1105.twice_edges_of_deficit_balance
    (by omega : 1 ≤ d) hD hkernelBalance
  have hpool := high_seed_degree_pool_ge_three JK hd hh hkernelOrder hedges
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hpool
  let f : (K : Set V) ↪ V := Function.Embedding.subtype (· ∈ (K : Set V))
  refine ⟨W.map f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hx
    exact u.property
  · simpa only [Finset.card_map] using hWcard
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    have hdeg : d + 1 ≤ JK.degree u := (Finset.mem_filter.mp (hWsub hu)).2
    have hdegEq : @SimpleGraph.degree (K : Set V) JK u (subtypeNeighborSetFintypePool JK u) =
        withinDegree G K u.val := by
      trans @SimpleGraph.degree (K : Set V) JK u (Fintype.ofFinite _)
      · congr 1; exact Subsingleton.elim _ _
      · exact ActualInducedDegree1105.degree_induce_eq_withinDegree G K u
    rwa [hdegEq] at hdeg

end HighSeedPool

/-- `exists_actual_kernel_with_trace_high_seed_slack_and_prefix_bounds` for `3 ≤ d`. -/
theorem exists_kernel_with_trace_high_seed_slack_ge_three
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 3 ≤ d) (hC : degreeCore G d = ∅)
    (hS : d + 3 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card) :
    let B : ℕ := (d - 1).choose 2 + (d - 1) * (S.card - d + 1) + 2
    let D : ℕ := (d.choose 2 + d * (S.card - d)) - (withinEdges G S).card
    let delta : ℕ := (withinEdges G S).card - (B + 1)
    ∃ K : Finset V, K ⊆ S ∧ S.card - D ≤ K.card ∧
      d + 3 ≤ K.card ∧ (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ Drem : ℕ, Drem ≤ D ∧ Drem ≤ K.card - d - 3 ∧
        (withinEdges G K).card + Drem =
          d.choose 2 + d * (K.card - d) ∧
        ∃ c w : ℕ, RestorationTrace G d K S c ∧ D = Drem + c ∧
          c = (S.card - K.card) + w ∧
          Drem + w + delta = (K.card - d) - 3 ∧
          (∀ U x, ActualRestorationStep G d K S c U x →
            d + 2 ≤ withinDegree G U x + (K.card - d)) ∧
          (∀ x ∈ S, x ∉ K → ∃ U, ActualRestorationStep G d K S c U x) ∧
          ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
            ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  let B : ℕ := (d - 1).choose 2 + (d - 1) * (S.card - d + 1) + 2
  let Q : ℕ := d.choose 2 + d * (S.card - d)
  let D : ℕ := Q - (withinEdges G S).card
  let delta : ℕ := (withinEdges G S).card - (B + 1)
  have hcoreSubset : degreeCore G d ⊆ S := by
    rw [hC]; exact Finset.empty_subset S
  have hcoreSize : max d (degreeCore G d).card ≤ S.card := by
    rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)]; omega
  have hcap : (withinEdges G S).card ≤ Q := by
    dsimp only [Q]
    simpa only [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      (core_induced_edge_bound G d S hcoreSubset hcoreSize)
  have hbalance : (withinEdges G S).card + D = Q := Nat.add_sub_of_le hcap
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using (Nat.choose_succ_succ' (d - 1) 1)
  have hmul : d * (S.card - d) = ((d - 1) + 1) * (S.card - d) := by rw [hpred]
  have hbase : Q =
      ((d - 1).choose 2 + (d - 1) * (S.card - d + 1)) + (S.card - d) := by
    dsimp only [Q]; rw [hchoose, hmul]; ring
  have hgap : Q = B + (S.card - d - 2) := by
    dsimp only [B]; rw [hbase]; omega
  have hstrict : B < (withinEdges G S).card := hthreshold
  have hdeficit : D ≤ S.card - d - 3 := by omega
  obtain ⟨K, hKS, hKlower, hKsize, hKmin, Drem, hDrem, hDremBound,
      hKcount, c, htrace, hcharge⟩ :=
    RestorationTrace1105.exists_actual_kernel_with_restoration_trace_of_empty_core_deficit
      G d S D hC hS hdeficit hbalance
  let h : ℕ := K.card - d
  have hh : 3 ≤ h := by dsimp only [h]; omega
  have horder : K.card = d + h := by dsimp only [h]; omega
  obtain ⟨W, hWK, hWcard, hWdegree⟩ :=
    exists_actual_high_seed_subset_ge_three G K hd hh horder hDremBound hKcount
  obtain ⟨_hKS', hcard, _hedges, w, hw⟩ :=
    restoration_trace_ledgers G d K S c htrace
  have hfinalSlack : Drem + w + delta = (K.card - d) - 3 := by omega
  have hsteps : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d) := by
    intro U x hstep
    have hdefect := actual_step_defect_le_excess G d K S U c w x hw hstep
    obtain ⟨_a, _b, _hp, _hf, hlow, _hs, _hc⟩ := hstep
    omega
  exact ⟨K, hKS, hKlower, hKsize, hKmin, Drem, hDrem, hDremBound,
    hKcount, c, w, htrace, hcharge, hw, hfinalSlack, hsteps,
    restoration_trace_step_exists G d K S c htrace,
    W, hWK, hWcard, hWdegree⟩

section StarSix

local instance (priority := 3000) subtypeNeighborSetFintypeSix {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- At `d = 3`, a kernel `K` of size `6 = d + 3 = 2 * d` with `Drem = 0` has a
residual star center `b ∈ K \ W` such that `H = insert b W` (of size `3`) covers
all edges of `G`. -/
theorem whole_graph_cover_of_kernel_six_at_d_three
    (G : SimpleGraph V) (K W : Finset V) (c : ℕ)
    (hconn : G.Connected) (hVlarge : 8 ≤ Fintype.card V)
    (hWK : W ⊆ K) (hKcard : K.card = 6) (hWcard : W.card = 2)
    (hmin : ∀ x ∈ K, 3 ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, 4 ≤ withinDegree G K x)
    (hQ : (withinEdges G K).card = 12)
    (htrace : RestorationTrace G 3 K Finset.univ c)
    (hfull : ∀ U x, ActualRestorationStep G 3 K Finset.univ c U x →
      5 ≤ withinDegree G U x + (K.card - 3))
    (hfree : (pathGraph 8).Free G) :
    ∃ H : Finset V, H.card = 3 ∧ ∀ x y : V, G.Adj x y → x ∈ H ∨ y ∈ H := by
  have hSlarge : 8 ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using hVlarge
  obtain ⟨D0, a, b_rem, hKD0, _hD0S, hD0card, hprefix, hsuffix, hcharge⟩ :=
    exists_actual_restoration_trace_cut G 3 K Finset.univ c htrace 8 (by omega) hSlarge
  have hrest0 : ∀ x ∈ D0, x ∉ K → 3 + 2 ≤ withinDegree G D0 x + 3 := by
    intro x hxD0 hxK
    obtain ⟨U, hstepD0⟩ := restoration_trace_step_exists G 3 K D0 a hprefix x hxD0 hxK
    have hstepS : ActualRestorationStep G 3 K Finset.univ c U x := by
      rw [hcharge]
      exact actual_step_extend_suffix G 3 K D0 Finset.univ U a b_rem x hstepD0 hsuffix
    have hbound := hfull U x hstepS
    obtain ⟨_p, q, _hp, _hfresh, _hlow, htail, _hc⟩ := hstepD0
    have hUD0 : U ⊆ D0 := (Finset.subset_insert x U).trans
      (restoration_trace_ledgers G 3 (insert x U) D0 q htail).1
    have hmono := withinDegree_le_of_subset G U D0 x hUD0
    omega
  obtain ⟨hP4, _hP3P2, _h3P2⟩ :=
    original_residual_forest_free_of_actual_carrier_additive
      (d := 3) (h := 3) (by decide) (by decide)
      G D0 K W hD0card hKD0 hWK (by omega) hWcard hmin hhigh hrest0 hfree
  have hKWcard : (K \ W).card = 4 := by
    rw [Finset.card_sdiff_of_subset hWK, hKcard, hWcard]
  have hpart := H3ResidualCount1105.original_seed_edge_partition_upper G K W hWK
  rw [hQ, hWcard, hKWcard] at hpart
  have hc22 : (2 : ℕ).choose 2 = 1 := by decide
  have hKWedges : 3 ≤ (G.induce (↑(K \ W) : Set V)).edgeFinset.card := by
    rw [← HighSeedLedgerBridge1105.withinEdges_card_eq_induced G (K \ W)]
    omega
  have hRmin := residual_min_degree_one G 3 K W (by decide) hWcard hmin
  obtain ⟨b, hb, _hleavesCard, hcenterErase, _hleaves⟩ :=
    H3ResidualStar1105.original_residual_star G K W hKWcard hRmin hKWedges hP4
  have hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x := by
    intro x hx hxb
    exact hcenterErase x (Finset.mem_erase.mpr ⟨hxb, hx⟩)
  let H : Finset V := insert b W
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  have hHK : H ⊆ K := Finset.insert_subset_iff.mpr ⟨hbK, hWK⟩
  have hHcard : H.card = 3 := by
    dsimp [H]
    rw [Finset.card_insert_of_notMem hbW, hWcard]
  have hcoverD0 := actual_carrier_cover_of_star_center_additive
    (d := 3) (h := 3) (by decide) (by decide)
    G D0 K W b hD0card hKD0 hWK (by omega) hWcard hb hcenter hmin hhigh hrest0 hfree
  have hKcover : ∀ x ∈ K, ∀ y ∈ K, G.Adj x y → x ∈ H ∨ y ∈ H :=
    fun x hxK y hyK hxy => hcoverD0 x (hKD0 hxK) y (hKD0 hyK) hxy
  obtain ⟨a0, P, hP, hPlen, hPK⟩ :=
    exists_cycle_in_kernel_of_kernel_cover G 3 K H (by decide) hHK hHcard
      (by omega) hmin hKcover
  have hOutInd := ActualCycleOutside1105.outside_independent_of_actual_cycle
    G hconn 3 hfree P hP hPlen
  have hOutNotK : ∀ x ∉ K, ∀ y ∉ K, ¬ G.Adj x y := by
    intro x hxK y hyK
    exact hOutInd x y (fun h => hxK (hPK x h)) (fun h => hyK (hPK y h))
  have hLateDeg : ∀ z ∉ K, 2 ≤ withinDegree G K z := by
    intro z hzK
    obtain ⟨U, hstep⟩ := restoration_trace_step_exists G 3 K Finset.univ c
      htrace z (Finset.mem_univ z) hzK
    have hbound := hfull U z hstep
    have hsub : U.filter (fun w => G.Adj z w) ⊆ K.filter (fun w => G.Adj z w) := by
      intro w hw
      obtain ⟨_hwU, hzw⟩ := Finset.mem_filter.mp hw
      have hwK : w ∈ K := by
        by_contra hwNotK
        exact hOutNotK z hzK w hwNotK hzw
      exact Finset.mem_filter.mpr ⟨hwK, hzw⟩
    have hc := Finset.card_le_card hsub
    change withinDegree G U z ≤ withinDegree G K z at hc
    omega
  refine ⟨H, hHcard, ?_⟩
  intro x y hxy
  let B : Finset V := insert x (insert y K)
  have hKB : K ⊆ B :=
    (Finset.subset_insert y K).trans (Finset.subset_insert x (insert y K))
  have hBcard : B.card ≤ 8 := by
    have h1 := Finset.card_insert_le x (insert y K)
    have h2 := Finset.card_insert_le y K
    dsimp [B]
    omega
  obtain ⟨D, hBD, _hDU, hDcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ B) hBcard hSlarge
  have hKD : K ⊆ D := hKB.trans hBD
  have hxD : x ∈ D := hBD (Finset.mem_insert_self x (insert y K))
  have hyD : y ∈ D := hBD (Finset.mem_insert_of_mem (Finset.mem_insert_self y K))
  have hrestD : ∀ z ∈ D, z ∉ K → 3 + 2 ≤ withinDegree G D z + 3 := by
    intro z _hzD hzK
    have hdeg := (hLateDeg z hzK).trans (withinDegree_le_of_subset G K D z hKD)
    omega
  exact actual_carrier_cover_of_star_center_additive
    (d := 3) (h := 3) (by decide) (by decide)
    G D K W b hDcard hKD hWK (by omega) hWcard hb hcenter hmin hhigh hrestD hfree
    x hxD y hyD hxy

end StarSix

section KernelNine

local instance (priority := 3000) subtypeNeighborSetFintypeNine {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- At `d = 3, n = 9, q ≥ 18`, if `K.card = 9`, then `K = Finset.univ`, so `G` has
minimum degree `≥ 3`, is 2-connected by `PathEightWindmillCount1105`, contains a
`6`-cycle, and has a size-`3` vertex cover. -/
theorem whole_graph_cover_of_kernel_nine_at_d_three
    (G : SimpleGraph (Fin 9)) (K : Finset (Fin 9))
    (hconn : G.Connected) (hKcard : K.card = 9)
    (hmin : ∀ x ∈ K, 3 ≤ withinDegree G K x)
    (hedges : 18 ≤ G.edgeFinset.card)
    (hfree : (pathGraph 8).Free G) :
    ∃ H : Finset (Fin 9), H.card = 3 ∧ ∀ x y : Fin 9, G.Adj x y → x ∈ H ∨ y ∈ H := by
  have hKuniv : K = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ K) (by simp [hKcard])
  have hdeg3 : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    have hv : 3 ≤ withinDegree G K v := hmin v (by rw [hKuniv]; exact Finset.mem_univ v)
    have hsub : K.filter (fun w => G.Adj v w) ⊆ G.neighborFinset v := by
      intro w hw
      exact (G.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2
    have hc := hv.trans (Finset.card_le_card hsub)
    rwa [G.card_neighborFinset_eq_degree v] at hc
  have hdelete : ∀ c : Fin 9, (G.induce {v : Fin 9 | v ≠ c}).Connected := by
    intro c
    let Hc := G.induce {v : Fin 9 | v ≠ c}
    by_contra hnotConn
    let z0 : Fin 9 := if c = 0 then 1 else 0
    have hz0 : z0 ≠ c := by dsimp [z0]; split_ifs with h <;> omega
    have hne : Nonempty {v : Fin 9 | v ≠ c} := ⟨⟨z0, hz0⟩⟩
    have hnotPre : ¬ Hc.Preconnected := fun hpre => hnotConn ⟨hpre⟩
    unfold SimpleGraph.Preconnected at hnotPre
    push Not at hnotPre
    obtain ⟨u, v, hnotReach⟩ := hnotPre
    let D := Hc.connectedComponentMk u
    let E := Hc.connectedComponentMk v
    have hDE : D ≠ E := fun heq => hnotReach (SimpleGraph.ConnectedComponent.exact heq)
    have hwind := PathEightWindmillCount1105.windmill_edge_count_of_distinct_deleted_components
      G hconn hdeg3 hfree c D E hDE
    rw [Fintype.card_fin] at hwind
    omega
  obtain ⟨order, hinj, horder⟩ :=
    ErdosProblems.AntiRamseyCycleGenericLongPathSeed.exists_ordered_path_of_degree_bounds
      (k := 7) (by decide) G hconn (by decide)
      (fun v => by have := hdeg3 v; omega)
      (fun x y _ => by have := hdeg3 x; have := hdeg3 y; omega)
  let seed : G.Walk (order 0) (order 6) :=
    Walk.cons (horder 0 1 (by decide))
      (Walk.cons (horder 1 2 (by decide))
        (Walk.cons (horder 2 3 (by decide))
          (Walk.cons (horder 3 4 (by decide))
            (Walk.cons (horder 4 5 (by decide))
              (Walk.cons (horder 5 6 (by decide)) Walk.nil)))))
  have hseed : seed.IsPath := by
    apply Walk.IsPath.mk'
    change [order 0, order 1, order 2, order 3, order 4, order 5, order 6].Nodup
    simp [hinj.eq_iff]
  obtain ⟨u, v, P, hP, hmax⟩ :=
    LongCycleFromMinimumDegree1105.exists_global_maximum_path G (0 : Fin 9)
  obtain ⟨hleft, hright⟩ :=
    LongCycleFromMinimumDegree1105.global_maximum_captures_endpoints P hP hmax
  have hPlower : 6 ≤ P.length := by
    have hb := hmax (order 0) (order 6) seed hseed
    simpa only [seed, Walk.length_cons, Walk.length_nil] using hb
  let _ : DecidableEq (Fin 9) := Classical.decEq (Fin 9)
  have hcounts (x : Fin 9) (hcapture : ∀ z, G.Adj x z → z ∈ P.support) :
      (P.support.toFinset.filter (fun z => G.Adj x z)).card = G.degree x := by
    rw [← G.card_neighborFinset_eq_degree x]
    congr 1
    ext z
    simp only [Finset.mem_filter, List.mem_toFinset, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.2, fun hz => ⟨hcapture z hz, hz⟩⟩
  have hLdeg : 3 ≤ (P.support.toFinset.filter (fun z => G.Adj u z)).card := by
    rw [hcounts u hleft]; exact hdeg3 u
  have hRdeg : 3 ≤ (P.support.toFinset.filter (fun z => G.Adj v z)).card := by
    rw [hcounts v hright]; exact hdeg3 v
  have hsum : 6 ≤
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
        (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card := by
    simp only [Walk.getVert_zero, Walk.getVert_length]; omega
  obtain ⟨C, hC, hCge⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold P hP
    (fun i _ _ => hdelete (P.getVert i.val)) 6 (by decide) (by omega) hsum
  have hpathBound : ∀ a b : Fin 9, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ 6 := by
    intro a b Q hQ
    by_contra hlong
    have hlen : 8 ≤ Q.length + 1 := by omega
    have hcopy : (pathGraph (Q.length + 1)).Copy G := hQ.pathGraphCopy
    let f : (pathGraph 8) →g pathGraph (Q.length + 1) :=
      { toFun := fun i => ⟨i.val, by omega⟩
        map_rel' := fun hij => by simpa only [pathGraph_adj] using hij }
    have hfinj : Function.Injective f := fun i j hij =>
      Fin.ext (congrArg (fun x : Fin (Q.length + 1) => x.val) hij)
    exact hfree ⟨hcopy.comp ⟨f, hfinj⟩⟩
  have hCdrop : C.dropLast.length ≤ 6 := hpathBound _ _ C.dropLast hC.isPath_dropLast
  have hCstep := SimpleGraph.Walk.length_dropLast_add_one hC.not_nil
  have hCneq : C.length ≠ 7 :=
    LongCycleOutside1105.no_cycle_of_order_one_below_forbidden_path
      G hconn 3 (by decide) hfree C hC
  have hClen : C.length = 6 := by omega
  exact exists_cover_of_large_kernel_and_cycle G 3 K hconn (by decide)
    (by omega) hmin hfree C hC hClen

end KernelNine

/-- Every connected representative `selectedGraph χ r` on `Fin 9` avoiding a
rainbow `P_8` satisfies `q ≤ 17`. -/
theorem connected_path_eight_nine_upper {q : ℕ}
    (χ : TopEdgeLabeling (Fin 9) (Fin q)) (r : RepresentativeChoice χ)
    (hconn : (selectedGraph χ r).Connected)
    (hno : ∀ P : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin 9)),
      ¬ IsRainbow P.toHom χ) : q ≤ 17 := by
  classical
  by_contra hqNotLe
  have hq18 : 18 ≤ q := by omega
  have hq : max ((2 * 3).choose 2 + 1)
      ((3 - 1).choose 2 + (3 - 1) * (9 - 3 + 1) + 2) < q := by
    have hmax : max ((2 * 3 : ℕ).choose 2 + 1)
        ((3 - 1 : ℕ).choose 2 + (3 - 1) * (9 - 3 + 1) + 2) = 17 := by decide
    omega
  let G : SimpleGraph (Fin 9) := selectedGraph χ r
  let S : Finset (Fin 9) := Finset.univ
  obtain ⟨J, hcone, _hfreeJ, _hdelete, _hsat, _hlower, hJ⟩ :=
    EvenOriginalNonemptyCore1105.original_even_saturated_first_core_empty
      (d := 3) (n := 9) (by decide) (by decide) χ r hconn hno hq
  have hC : degreeCore G 3 = ∅ :=
    StrictConeCore1105.degreeCore_eq_empty_of_cone_le G J 3 hcone hJ
  have hEdges : withinEdges G S = G.edgeFinset := by
    ext e; simp [withinEdges, S]
  have hCount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  have hScard : S.card = 9 := by simp [S]
  have hthreshold : (3 - 1).choose 2 + (3 - 1) * (S.card - 3 + 1) + 2 <
      (withinEdges G S).card := by
    rw [hScard, hEdges, hCount]
    have hb : (3 - 1 : ℕ).choose 2 + (3 - 1) * (9 - 3 + 1) + 2 = 17 := by decide
    omega
  have hfreeG : (pathGraph 8).Free G := selectedGraph_free (pathGraph 8) χ r hno
  obtain ⟨K, hKS, _hKlower, hKsize, hKmin, Drem, _hDrem, hDremBound,
      hKcount, c, w, htrace, _hcharge, _hw, _hslack, hfull, _hoccurs,
      W, hWK, hWcard, hWdegree⟩ :=
    exists_kernel_with_trace_high_seed_slack_ge_three G 3 S (by decide) hC
      (by rw [hScard]; decide) hthreshold
  have hKle9 : K.card ≤ 9 := by
    have hc := Finset.card_le_card hKS
    simpa only [hScard] using hc
  have hnocover : ∀ H : Finset (Fin 9), H.card = 3 →
      ¬ (∀ x y : Fin 9, G.Adj x y → x ∈ H ∨ y ∈ H) := by
    intro H hHcard hCoverUniv
    have hqB : (3 - 1).choose 2 + (3 - 1) * (9 - 3 + 1) + 2 < q := by
      have hb : (3 - 1 : ℕ).choose 2 + (3 - 1) * (9 - 3 + 1) + 2 = 17 := by decide
      omega
    obtain ⟨P, hP⟩ :=
      ActualVertexCoverSellExit1105.rainbow_path_of_actual_vertex_cover
        (d := 3) (n := 9) (by decide) (by decide) χ r H hHcard hCoverUniv hqB
    exact hno P hP
  have hcases : K.card = 6 ∨ K.card = 7 ∨ K.card = 8 ∨ K.card = 9 := by omega
  rcases hcases with hK6 | hK7 | hK8 | hK9
  · have hDrem0 : Drem = 0 := by omega
    have hQ12 : (withinEdges G K).card = 12 := by
      have hc32 : (3 : ℕ).choose 2 = 3 := by decide
      omega
    obtain ⟨H, hHcard, hCover⟩ :=
      whole_graph_cover_of_kernel_six_at_d_three G K W c hconn (by decide)
        hWK hK6 hWcard hKmin hWdegree hQ12 htrace hfull hfreeG
    exact hnocover H hHcard hCover
  · obtain ⟨H, _hHK, hHcard, hCover⟩ :=
      whole_graph_cover_of_kernel_two_d_plus_one G 3 K W c (by decide) hconn (by decide)
        hWK hK7 hWcard hKmin hWdegree htrace hfull hfreeG
    exact hnocover H hHcard hCover
  · obtain ⟨H, hHcard, hCover⟩ :=
      whole_graph_cover_of_kernel_two_d_plus_two G 3 K W c (by decide) hconn (by decide)
        hWK hK8 hWcard hKmin hWdegree htrace hfull hfreeG
    exact hnocover H hHcard hCover
  · have hG18 : 18 ≤ (@SimpleGraph.edgeFinset (Fin 9) G G.fintypeEdgeSet).card := by
      have heq : (@SimpleGraph.edgeFinset (Fin 9) G G.fintypeEdgeSet).card = G.edgeFinset.card := by
        congr 2; exact Subsingleton.elim _ _
      omega
    obtain ⟨H, hHcard, hCover⟩ :=
      whole_graph_cover_of_kernel_nine_at_d_three G K hconn hK9 hKmin hG18 hfreeG
    exact hnocover H hHcard hCover

/-- Upper bound `antiRamseyNum (pathGraph 8) 9 ≤ 17`, discharging disconnected
representatives via `PathOriginalConnectedStep1105` and the `n = 8` base
`antiRamseyNum_path_eight_eight_le_sixteen`. -/
theorem antiRamseyNum_path_eight_nine_le_seventeen :
    antiRamseyNum (pathGraph 8) 9 ≤ 17 := by
  classical
  have hformula8 : ErdosProblems.PathLemmaFourScalar.pathFormula 8 8 = 16 := by decide
  have hformula9 : ErdosProblems.PathLemmaFourScalar.pathFormula 9 8 = 17 := by decide
  let admissible : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin 9) (Fin q), Function.Surjective χ ∧
      ∀ P : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin 9)),
        ¬ IsRainbow P.toHom χ}
  have hbounded : BddAbove admissible := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin 9)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  rw [← hformula9]
  change sSup admissible ≤ _
  apply (csSup_le_iff' hbounded).2
  intro q hq
  obtain ⟨χ, hχ, hno⟩ := hq
  have hIH : OriginalFullSmallerHostIH 8 9 := by
    intro m hkm hmn
    have hm8 : m = 8 := by omega
    subst m
    rw [hformula8]
    exact antiRamseyNum_path_eight_eight_le_sixteen
  have hstep : OriginalConnectedPathStep 8 9 := by
    intro q' χ' R' _hkn hconn' hno' _hIH'
    rw [hformula9]
    exact connected_path_eight_nine_upper χ' R' hconn' hno'
  exact original_color_count_le_formula_of_connected_step_and_full_IH
    (by decide : 8 ≤ 8) (by decide : 8 ≤ 9) hstep χ hχ hno hIH

/-- Complete unconditional proof of `erdos_1105.parts.ii` for ALL path orders
`k ≥ 5` and ALL host orders `n ≥ k`. -/
theorem erdos_1105_parts_ii_exact :
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
      let ℓ := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  rw [Erdos1105UniversalPathReduction.erdos_1105_parts_ii_iff_even_windows_ge_three]
  intro ℓ hℓ n hn hwin
  have hcases : ℓ = 3 ∨ 4 ≤ ℓ := by omega
  rcases hcases with rfl | hℓ4
  · have hnCases : n = 8 ∨ n = 9 := by omega
    rcases hnCases with rfl | rfl
    · have hmax8 : max ((2 * 3 : ℕ).choose 2 + 1)
          ((3 - 1 : ℕ).choose 2 + (3 - 1) * (8 - 3 + 1) + 2) = 16 := by decide
      rw [hmax8]
      exact antiRamseyNum_path_eight_eight_le_sixteen
    · have hmax9 : max ((2 * 3 : ℕ).choose 2 + 1)
          ((3 - 1 : ℕ).choose 2 + (3 - 1) * (9 - 3 + 1) + 2) = 17 := by decide
      rw [hmax9]
      exact antiRamseyNum_path_eight_nine_le_seventeen
  · exact antiRamseyNum_even_path_le_on_base_window ℓ hℓ4 n hn hwin

end ErdosProblems.PathUpperReduction.PathEightNineBase1105
