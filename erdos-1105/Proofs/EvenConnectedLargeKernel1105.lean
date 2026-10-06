module

public import SmallKernelWholeSupport1105
public import ActualPrefixCycle1105
public import ActualSuffixIndependence1105
public import TwoHighDegreeCycleCover1105
public import H3CountStar1105
public import EvenOriginalNonemptyCore1105
public import StrictConeCore1105
public import EvenCoverColorCaller1105
public import PathUpperRainbowBridge
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Whole-support vertex cover for all small kernels `d + 4 ≤ |K| ≤ 2 * d`
(`4 ≤ h ≤ d`), and unconditional elimination of the entire small-kernel regime
`|K| ≤ 2 * d` for connected representatives of rainbow-`P_{2d+2}`-free colorings
above the even threshold.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenConnectedLargeKernel1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualTraceCarrierCut1105
open ErdosProblems.PathUpperReduction.ActualNestedPrefixGuards1105
open ErdosProblems.PathUpperReduction.ActualPrefixFilledCycle1105
open ErdosProblems.PathUpperReduction.ActualPrefixCycle1105
open ErdosProblems.PathUpperReduction.ActualSuffixIndependence1105
open ErdosProblems.PathUpperReduction.ActualPrefixCarrierDegree1105
open ErdosProblems.PathUpperReduction.SmallKernelWholeSupport1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Generalization of `H3SameTraceCarrier1105.exists_same_trace_prefix_with_all_carrier_degrees`
from `|K| = d + 3` to all small kernels `d + 3 ≤ |K| ≤ 2 * d`: the `2 * d`-prefix
cycle and suffix independence transfer the restored degree bound
`d - (K.card - d) + 2` to every carrier `D` with `A ⊆ D ⊆ S`. -/
theorem exists_same_trace_prefix_with_all_carrier_degrees_of_small_kernel
    (G : SimpleGraph V) (d : ℕ) (K S : Finset V) (c : ℕ)
    (hd : 4 ≤ d) (hKlarge : d + 3 ≤ K.card) (hKsmall : K.card ≤ 2 * d)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x)
    (htrace : RestorationTrace G d K S c)
    (hfull : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ A : Finset V, ∃ a b : ℕ,
      K ⊆ A ∧ A ⊆ S ∧ A.card = 2 * d ∧
      RestorationTrace G d K A a ∧ RestorationTrace G d A S b ∧ c = a + b ∧
      ∃ C : Copy (cycleGraph (2 * d)) G,
        Set.range C = (A : Set V) ∧
        (∀ x ∈ S, x ∉ A → ∀ y ∈ S, y ∉ A → ¬ G.Adj x y) ∧
        (∀ x ∈ S, x ∉ A → d - (K.card - d) + 2 ≤ withinDegree G A x) ∧
        (∀ D : Finset V, A ⊆ D → D ⊆ S →
          ∀ x ∈ D, x ∉ K → d - (K.card - d) + 2 ≤ withinDegree G D x) := by
  classical
  have hSfits : 2 * d ≤ S.card := by omega
  obtain ⟨A, a, b, hKA, hAS, hAcard, hprefix, hsuffix, hcharge⟩ :=
    exists_actual_restoration_trace_cut G d K S c htrace
      (2 * d) hKsmall hSfits
  have hstepsA := actual_prefix_steps_lower_bound G d K A S a b c
    hKsmall hsuffix hcharge hfull
  have hretained := retained_degree_of_actual_prefix_steps G d K A a
    (d - (K.card - d) + 2) hprefix hstepsA
  have hseedA : ∀ x ∈ K, d ≤ withinDegree G A x := by
    intro x hx
    exact (hseed x hx).trans (withinDegree_le_of_subset G K A x hKA)
  have hfilled := actual_trace_has_exact_filled_cycle_copy G d K A a
    hprefix hKlarge (by omega) hstepsA
  obtain ⟨C, hRange⟩ := original_cycle_copy_of_actual_seed_filling G d K A
    (by omega) hAcard hseedA hfilled
  have hfreeS : (pathGraph (2 * d + 2)).Free (G.induce (S : Set V)) := by
    rintro ⟨P⟩
    exact hfree ⟨(Copy.induce G (S : Set V)).comp P⟩
  obtain ⟨hIndependent, _hContacts⟩ :=
    suffix_independent_of_same_kernel_prefix_and_original_cycle_copy
      G d K A S a b c (by omega) hprefix hsuffix hcharge
      hKsmall hfull hfreeS C hRange
  have hLate : ∀ x ∈ S, x ∉ A → d - (K.card - d) + 2 ≤ withinDegree G A x := by
    intro x hxS hxA
    have hxK : x ∉ K := fun hx => hxA (hKA hx)
    obtain ⟨U, hstep⟩ := restoration_trace_step_exists
      G d K S c htrace x hxS hxK
    have hbound := hfull U x hstep
    obtain ⟨p, q, _hp, _hfresh, _hlow, htail, _hcharge⟩ := hstep
    have hUS : U ⊆ S := (Finset.subset_insert x U).trans
      (restoration_trace_ledgers G d (insert x U) S q htail).1
    have hmono := withinDegree_le_of_subset G U S x hUS
    have hFilter := neighbor_filter_eq_of_suffix_independent G A S S
      hAS (fun _ hx => hx) hIndependent x hxS hxA
    have hDegree : withinDegree G S x = withinDegree G A x := by
      simpa only [withinDegree] using
        congrArg (fun T : Finset V => T.card) hFilter
    omega
  have hAll : ∀ D : Finset V, A ⊆ D → D ⊆ S →
      ∀ x ∈ D, x ∉ K → d - (K.card - d) + 2 ≤ withinDegree G D x := by
    intro D hAD hDS x hxD hxK
    by_cases hxA : x ∈ A
    · exact (hretained x hxA hxK).trans
        (withinDegree_le_of_subset G A D x hAD)
    · exact (hLate x (hDS hxD) hxA).trans
        (withinDegree_le_of_subset G A D x hAD)
  exact ⟨A, a, b, hKA, hAS, hAcard, hprefix, hsuffix, hcharge,
    C, hRange, hIndependent, hLate, hAll⟩

/-- For any kernel `K` with `d + 4 ≤ K.card ≤ 2 * d`, its residual `K \ W` has a
star center `b ∈ K \ W` such that `H = insert b W` (of size `d`) covers all
edges of `G` on the entire support `S`. -/
theorem small_kernel_whole_support_cover
    (G : SimpleGraph V) (d : ℕ) (K W S : Finset V) (c : ℕ)
    (hd : 4 ≤ d) (hWK : W ⊆ K)
    (hKlow : d + 4 ≤ K.card) (hKhigh : K.card ≤ 2 * d)
    (hWcard : W.card = d - 1)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (htrace : RestorationTrace G d K S c)
    (hfull : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ H : Finset V, H ⊆ K ∧ H.card = d ∧
      ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x ∈ H ∨ y ∈ H := by
  classical
  let h : ℕ := K.card - d
  have hlow : 4 ≤ h := by dsimp [h]; omega
  have hKcard : K.card = d + h := by dsimp [h]; omega
  obtain ⟨A, _a, _b, hKA, hAS, hAcard, _hprefix, _hsuffix, _hcharge,
      _C, _hRange, _hIndependent, _hLate, hAll⟩ :=
    exists_same_trace_prefix_with_all_carrier_degrees_of_small_kernel
      G d K S c hd (by omega) hKhigh hSlarge hmin htrace hfull hfree
  -- Choose one reference carrier `D0` of size `2*d+2` with `A ⊆ D0 ⊆ S` to extract the star center `b ∈ K \ W`.
  have hAle : A.card ≤ 2 * d + 2 := by omega
  obtain ⟨D0, hAD0, hD0S, hD0card⟩ :=
    Finset.exists_subsuperset_card_eq hAS hAle hSlarge
  have hKD0 : K ⊆ D0 := hKA.trans hAD0
  have hrest0 : ∀ x ∈ D0, x ∉ K → d + 2 ≤ withinDegree G D0 x + h := by
    intro x hxD0 hxK
    have hdeg := hAll D0 hAD0 hD0S x hxD0 hxK
    dsimp [h] at *
    omega
  obtain ⟨b, hb, hcenter, _hleaves⟩ :=
    exists_residual_star_center_of_carrier_additive (by omega) hlow
      G D0 K W hD0card hKD0 hWK hKcard hWcard hmin hhigh hrest0 hfree
  let H : Finset V := insert b W
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  have hHK : H ⊆ K := Finset.insert_subset_iff.mpr ⟨hbK, hWK⟩
  have hHcard : H.card = d := by
    dsimp [H]
    rw [Finset.card_insert_of_notMem hbW, hWcard]
    omega
  refine ⟨H, hHK, hHcard, ?_⟩
  intro x hxS y hyS hxy
  let B : Finset V := insert x (insert y A)
  have hAB : A ⊆ B :=
    (Finset.subset_insert y A).trans (Finset.subset_insert x (insert y A))
  have hBS : B ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzx | hz
    · simpa only [hzx] using hxS
    rcases Finset.mem_insert.mp hz with hzy | hzA
    · simpa only [hzy] using hyS
    · exact hAS hzA
  have hBcard : B.card ≤ 2 * d + 2 := by
    have hfirst := Finset.card_insert_le x (insert y A)
    have hsecond := Finset.card_insert_le y A
    dsimp only [B]
    omega
  obtain ⟨D, hBD, hDS, hDcard⟩ :=
    Finset.exists_subsuperset_card_eq hBS hBcard hSlarge
  have hAD : A ⊆ D := hAB.trans hBD
  have hKD : K ⊆ D := hKA.trans hAD
  have hxD : x ∈ D := hBD (Finset.mem_insert_self x (insert y A))
  have hyD : y ∈ D := hBD (Finset.mem_insert_of_mem (Finset.mem_insert_self y A))
  have hrestD : ∀ z ∈ D, z ∉ K → d + 2 ≤ withinDegree G D z + h := by
    intro z hzD hzK
    have hdeg := hAll D hAD hDS z hzD hzK
    dsimp [h] at *
    omega
  exact actual_carrier_cover_of_star_center_additive (by omega) (by omega)
    G D K W b hDcard hKD hWK hKcard hWcard hb hcenter hmin hhigh hrestD hfree
    x hxD y hyD hxy

/-- For any kernel `K` with `d + 4 ≤ K.card ≤ 2 * d + 2`, cutting the restoration
trace at a prefix carrier `D0` of size `2 * d + 2` yields a star center `b ∈ K \ W`
such that `H = insert b W` (of size `d`) covers all edges of `G[K]`. -/
theorem exists_star_center_and_kernel_cover_of_le_two_d_plus_two
    (G : SimpleGraph V) (d : ℕ) (K W S : Finset V) (c : ℕ)
    (hd : 3 ≤ d) (hWK : W ⊆ K)
    (hKlow : d + 4 ≤ K.card) (hKhigh : K.card ≤ 2 * d + 2)
    (hWcard : W.card = d - 1)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (htrace : RestorationTrace G d K S c)
    (hfull : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ b ∈ K \ W,
      (∀ x ∈ K \ W, x ≠ b → G.Adj b x) ∧
      (insert b W).card = d ∧
      (∀ x ∈ K, ∀ y ∈ K, G.Adj x y → x ∈ insert b W ∨ y ∈ insert b W) := by
  classical
  let h : ℕ := K.card - d
  have hlow : 4 ≤ h := by dsimp [h]; omega
  have hKcard : K.card = d + h := by dsimp [h]; omega
  obtain ⟨D0, a, b_rem, hKD0, _hD0S, hD0card, hprefix, hsuffix, hcharge⟩ :=
    exists_actual_restoration_trace_cut G d K S c htrace (2 * d + 2) hKhigh hSlarge
  have hrest0 : ∀ x ∈ D0, x ∉ K → d + 2 ≤ withinDegree G D0 x + h := by
    intro x hxD0 hxK
    obtain ⟨U, hstepD0⟩ := restoration_trace_step_exists G d K D0 a hprefix x hxD0 hxK
    have hstepS : ActualRestorationStep G d K S c U x := by
      rw [hcharge]
      exact actual_step_extend_suffix G d K D0 S U a b_rem x hstepD0 hsuffix
    have hbound := hfull U x hstepS
    obtain ⟨_p, q, _hp, _hfresh, _hlow, htail, _hc⟩ := hstepD0
    have hUD0 : U ⊆ D0 := (Finset.subset_insert x U).trans
      (restoration_trace_ledgers G d (insert x U) D0 q htail).1
    have hmono := withinDegree_le_of_subset G U D0 x hUD0
    dsimp [h]
    omega
  obtain ⟨b, hb, hcenter, _hleaves⟩ :=
    exists_residual_star_center_of_carrier_additive hd hlow
      G D0 K W hD0card hKD0 hWK hKcard hWcard hmin hhigh hrest0 hfree
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  have hHcard : (insert b W).card = d := by
    rw [Finset.card_insert_of_notMem hbW, hWcard]
    omega
  have hcoverD0 := actual_carrier_cover_of_star_center_additive hd (by omega)
    G D0 K W b hD0card hKD0 hWK hKcard hWcard hb hcenter hmin hhigh hrest0 hfree
  refine ⟨b, hb, hcenter, hHcard, ?_⟩
  intro x hxK y hyK hxy
  exact hcoverD0 x (hKD0 hxK) y (hKD0 hyK) hxy

/-- When a subset `H ⊆ K` of size `d` covers all edges of `G[K]` and `2 * d ≤ K.card`,
every vertex of `K \ H` is adjacent to every vertex of `H`, yielding an original
`2 * d`-cycle walk `P` supported inside `K`. -/
theorem exists_cycle_in_kernel_of_kernel_cover
    (G : SimpleGraph V) (d : ℕ) (K H : Finset V)
    (hd : 2 ≤ d) (hHK : H ⊆ K) (hHcard : H.card = d) (hKlarge : 2 * d ≤ K.card)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hKcover : ∀ x ∈ K, ∀ y ∈ K, G.Adj x y → x ∈ H ∨ y ∈ H) :
    ∃ a : V, ∃ P : G.Walk a a, P.IsCycle ∧ P.length = 2 * d ∧
      ∀ v, v ∈ P.support → v ∈ K := by
  classical
  have hcross : ∀ u ∈ K \ H, ∀ w ∈ H, G.Adj u w := by
    intro u hu w hw
    obtain ⟨huK, huH⟩ := Finset.mem_sdiff.mp hu
    have hsub : K.filter (fun z => G.Adj u z) ⊆ H := by
      intro z hz
      obtain ⟨hzK, huz⟩ := Finset.mem_filter.mp hz
      rcases hKcover u huK z hzK huz with huH' | hzH
      · exact False.elim (huH huH')
      · exact hzH
    have hdeg : d ≤ (K.filter (fun z => G.Adj u z)).card := hmin u huK
    have heq : K.filter (fun z => G.Adj u z) = H :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hwMem : w ∈ K.filter (fun z => G.Adj u z) := by rw [heq]; exact hw
    exact (Finset.mem_filter.mp hwMem).2
  have hKHcard : d ≤ (K \ H).card := by
    rw [Finset.card_sdiff_of_subset hHK, hHcard]
    omega
  obtain ⟨I0, hI0sub, hI0card⟩ := Finset.exists_subset_card_eq hKHcard
  let A : Finset V := H ∪ I0
  have hdisj : Disjoint H I0 := by
    apply Finset.disjoint_left.mpr
    intro x hxH hxI0
    exact (Finset.mem_sdiff.mp (hI0sub hxI0)).2 hxH
  have hAcard : A.card = 2 * d := by
    dsimp [A]
    rw [Finset.card_union_of_disjoint hdisj, hHcard, hI0card]
    omega
  have hAK : A ⊆ K := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxH | hxI0
    · exact hHK hxH
    · exact (Finset.mem_sdiff.mp (hI0sub hxI0)).1
  have hseedA : ∀ x ∈ A, d ≤ withinDegree G A x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxH | hxI0
    · have hsub : I0 ⊆ A.filter (fun z => G.Adj x z) := by
        intro u huI0
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ huI0,
          (hcross u (hI0sub huI0) x hxH).symm⟩
      have hc := Finset.card_le_card hsub
      rw [hI0card] at hc
      exact hc
    · have hsub : H ⊆ A.filter (fun z => G.Adj x z) := by
        intro w hwH
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hwH,
          hcross x (hI0sub hxI0) w hwH⟩
      have hc := Finset.card_le_card hsub
      rw [hHcard] at hc
      exact hc
  have hfilled := filled_seed_has_exact_cycle_copy G A
  obtain ⟨C, hRange⟩ := original_cycle_copy_of_actual_seed_filling G d A A
    hd hAcard hseedA hfilled
  obtain ⟨a, P, hP, hPlen, hPsupport⟩ :=
    exists_original_cycle_walk_of_copy G (2 * d) (by omega) C
  refine ⟨a, P, hP, hPlen, ?_⟩
  intro v hv
  have hvRange : v ∈ Set.range C := (hPsupport v).mp hv
  rw [hRange] at hvRange
  exact hAK hvRange

section TwoOutsiders

local instance (priority := 3000) subtypeNeighborSetFintype {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- When `2 * d + 2 ≤ K.card` and `G` contains any `2 * d`-cycle `P`, at least two
vertices of `K` lie outside `P`, so `TwoHighDegreeCycleCover1105` yields a size-`d`
vertex cover of `G`. -/
theorem exists_cover_of_large_kernel_and_cycle
    (G : SimpleGraph V) (d : ℕ) (K : Finset V)
    (hconn : G.Connected) (hVlarge : 2 * d + 2 ≤ Fintype.card V)
    (hKlarge : 2 * d + 2 ≤ K.card)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (P : G.Walk a a) (hP : P.IsCycle) (hPlen : P.length = 2 * d) :
    ∃ H : Finset V, H.card = d ∧ ∀ x y : V, G.Adj x y → x ∈ H ∨ y ∈ H := by
  classical
  let Cset : Finset V := P.support.toFinset
  have hCcard : Cset.card = 2 * d := by
    dsimp [Cset]
    rw [LongCycleOutside1105.support_finset_card_of_cycle G P hP, hPlen]
  have hdiff : 1 < (K \ Cset).card := by
    have hle := Finset.card_sdiff_add_card_inter K Cset
    have hinter : (K ∩ Cset).card ≤ Cset.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hdiff
  obtain ⟨huK, huC⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hvK, hvC⟩ := Finset.mem_sdiff.mp hv
  have huNotP : u ∉ P.support := fun h => huC (List.mem_toFinset.mpr h)
  have hvNotP : v ∉ P.support := fun h => hvC (List.mem_toFinset.mpr h)
  have hdeg (z : V) (hzK : z ∈ K) : d ≤ G.degree z := by
    have hsub : K.filter (fun w => G.Adj z w) ⊆ G.neighborFinset z := by
      intro w hw
      exact (G.mem_neighborFinset z w).mpr (Finset.mem_filter.mp hw).2
    have hc := (hmin z hzK).trans (Finset.card_le_card hsub)
    rwa [G.card_neighborFinset_eq_degree z] at hc
  obtain ⟨A, hAcard, hAcover⟩ :=
    TwoHighDegreeCycleCover1105.exists_actual_cover_of_cycle_and_two_high_degree_outsiders
      G d hconn hVlarge hfree P hP hPlen u v huNotP hvNotP huv (hdeg u huK) (hdeg v hvK)
  refine ⟨A, hAcard, ?_⟩
  intro x y hxy
  exact hAcover hxy

end TwoOutsiders

/-- Whole-graph vertex cover when `K.card = 2 * d + 1` (`h = d + 1`). -/
theorem whole_graph_cover_of_kernel_two_d_plus_one
    (G : SimpleGraph V) (d : ℕ) (K W : Finset V) (c : ℕ)
    (hd : 3 ≤ d) (hconn : G.Connected) (hVlarge : 2 * d + 2 ≤ Fintype.card V)
    (hWK : W ⊆ K) (hKcard : K.card = 2 * d + 1) (hWcard : W.card = d - 1)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (htrace : RestorationTrace G d K Finset.univ c)
    (hfull : ∀ U x, ActualRestorationStep G d K Finset.univ c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ H : Finset V, H ⊆ K ∧ H.card = d ∧
      ∀ x y : V, G.Adj x y → x ∈ H ∨ y ∈ H := by
  classical
  have hSlarge : 2 * d + 2 ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using hVlarge
  obtain ⟨b, hb, hcenter, hHcard, hKcover⟩ :=
    exists_star_center_and_kernel_cover_of_le_two_d_plus_two
      G d K W Finset.univ c hd hWK (by omega) (by omega) hWcard
      hmin hhigh hSlarge htrace hfull hfree
  let H : Finset V := insert b W
  have hHK : H ⊆ K := Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp hb).1, hWK⟩
  obtain ⟨a, P, hP, hPlen, hPK⟩ :=
    exists_cycle_in_kernel_of_kernel_cover G d K H (by omega) hHK hHcard
      (by omega) hmin hKcover
  have hOutInd := ActualCycleOutside1105.outside_independent_of_actual_cycle
    G hconn d hfree P hP hPlen
  refine ⟨H, hHK, hHcard, ?_⟩
  intro x y hxy
  by_cases hxK : x ∈ K
  · by_cases hyK : y ∈ K
    · exact hKcover x hxK y hyK hxy
    · let D : Finset V := insert y K
      have hDcard : D.card = 2 * d + 2 := by
        dsimp [D]
        rw [Finset.card_insert_of_notMem hyK, hKcard]
      have hKD : K ⊆ D := Finset.subset_insert y K
      have hrestD : ∀ z ∈ D, z ∉ K → d + 2 ≤ withinDegree G D z + (d + 1) := by
        intro z hzD hzK
        rcases Finset.mem_insert.mp hzD with rfl | hzK'
        · have hxMem : x ∈ D.filter (fun w => G.Adj z w) :=
            Finset.mem_filter.mpr ⟨hKD hxK, hxy.symm⟩
          have hpos : 1 ≤ withinDegree G D z :=
            Finset.card_pos.mpr ⟨x, hxMem⟩
          omega
        · exact False.elim (hzK hzK')
      exact actual_carrier_cover_of_star_center_additive hd (by omega)
        G D K W b hDcard hKD hWK (by omega) hWcard hb hcenter hmin hhigh hrestD hfree
        x (hKD hxK) y (Finset.mem_insert_self y K) hxy
  · by_cases hyK : y ∈ K
    · let D : Finset V := insert x K
      have hDcard : D.card = 2 * d + 2 := by
        dsimp [D]
        rw [Finset.card_insert_of_notMem hxK, hKcard]
      have hKD : K ⊆ D := Finset.subset_insert x K
      have hrestD : ∀ z ∈ D, z ∉ K → d + 2 ≤ withinDegree G D z + (d + 1) := by
        intro z hzD hzK
        rcases Finset.mem_insert.mp hzD with rfl | hzK'
        · have hyMem : y ∈ D.filter (fun w => G.Adj z w) :=
            Finset.mem_filter.mpr ⟨hKD hyK, hxy⟩
          have hpos : 1 ≤ withinDegree G D z :=
            Finset.card_pos.mpr ⟨y, hyMem⟩
          omega
        · exact False.elim (hzK hzK')
      exact actual_carrier_cover_of_star_center_additive hd (by omega)
        G D K W b hDcard hKD hWK (by omega) hWcard hb hcenter hmin hhigh hrestD hfree
        x (Finset.mem_insert_self x K) y (hKD hyK) hxy
    · have hxNotP : x ∉ P.support := fun h => hxK (hPK x h)
      have hyNotP : y ∉ P.support := fun h => hyK (hPK y h)
      exact False.elim (hOutInd x y hxNotP hyNotP hxy)

/-- Whole-graph vertex cover when `K.card = 2 * d + 2` (`h = d + 2`). -/
theorem whole_graph_cover_of_kernel_two_d_plus_two
    (G : SimpleGraph V) (d : ℕ) (K W : Finset V) (c : ℕ)
    (hd : 3 ≤ d) (hconn : G.Connected) (hVlarge : 2 * d + 2 ≤ Fintype.card V)
    (hWK : W ⊆ K) (hKcard : K.card = 2 * d + 2) (hWcard : W.card = d - 1)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (htrace : RestorationTrace G d K Finset.univ c)
    (hfull : ∀ U x, ActualRestorationStep G d K Finset.univ c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ H : Finset V, H.card = d ∧ ∀ x y : V, G.Adj x y → x ∈ H ∨ y ∈ H := by
  classical
  have hSlarge : 2 * d + 2 ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using hVlarge
  obtain ⟨b, hb, _hcenter, hHcard, hKcover⟩ :=
    exists_star_center_and_kernel_cover_of_le_two_d_plus_two
      G d K W Finset.univ c hd hWK (by omega) (by omega) hWcard
      hmin hhigh hSlarge htrace hfull hfree
  let H0 : Finset V := insert b W
  have hH0K : H0 ⊆ K := Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp hb).1, hWK⟩
  obtain ⟨a, P, hP, hPlen, _hPK⟩ :=
    exists_cycle_in_kernel_of_kernel_cover G d K H0 (by omega) hH0K hHcard
      (by omega) hmin hKcover
  exact exists_cover_of_large_kernel_and_cycle G d K hconn hVlarge
    (by omega) hmin hfree P hP hPlen

/-- For any finite graph `G` with empty `d`-core, strict linear edge threshold on `S`,
`P_{2d+2}`-freedom, and no size-`d` vertex cover of `G[S]`, the returned kernel `K`
satisfies `2 * d + 1 ≤ K.card` (eliminating all `d + 3 ≤ |K| ≤ 2 * d`). -/
theorem exists_large_kernel_of_empty_core_and_no_cover
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    (hnocover : ∀ H : Finset V, H.card = d →
      ¬ (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x ∈ H ∨ y ∈ H)) :
    let B : ℕ := (d - 1).choose 2 + (d - 1) * (S.card - d + 1) + 2
    let D0 : ℕ := (d.choose 2 + d * (S.card - d)) - (withinEdges G S).card
    let delta : ℕ := (withinEdges G S).card - (B + 1)
    ∃ K : Finset V, K ⊆ S ∧ S.card - D0 ≤ K.card ∧
      2 * d + 1 ≤ K.card ∧
      (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ Drem : ℕ, Drem ≤ D0 ∧ Drem ≤ K.card - d - 3 ∧
        (withinEdges G K).card + Drem = d.choose 2 + d * (K.card - d) ∧
        ∃ c w : ℕ, RestorationTrace G d K S c ∧ D0 = Drem + c ∧
          c = (S.card - K.card) + w ∧
          Drem + w + delta = (K.card - d) - 3 ∧
          (∀ U x, ActualRestorationStep G d K S c U x →
            d + 2 ≤ withinDegree G U x + (K.card - d) ∧
            (K.card - d ≤ d → d - (K.card - d) + 2 ≤ withinDegree G U x)) ∧
          (∀ x ∈ S, x ∉ K → ∃ U, ActualRestorationStep G d K S c U x) ∧
          ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
            ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  obtain ⟨K, hKS, hKlower, hKsize, hKmin, Drem, hDrem, hDremBound,
      hKcount, c, w, htrace, hcharge, hw, hslack, hsteps, hoccurs,
      W, hWK, hWcard, hWdegree⟩ :=
    TracePrefixSlack1105.exists_actual_kernel_with_trace_high_seed_slack_and_prefix_bounds
      G d S hd hC (by omega) hthreshold
  have hfull : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d) :=
    fun U x hstep => (hsteps U x hstep).1
  have hK4 : d + 4 ≤ K.card := by
    by_contra hlt4
    have hK3 : K.card = d + 3 := by omega
    have hDremZero : Drem = 0 := by omega
    have hsub : K.card - d = 3 := by omega
    have hQ : (withinEdges G K).card = d.choose 2 + 3 * d := by
      simpa only [hDremZero, Nat.add_zero, hsub, Nat.mul_comm] using hKcount
    obtain ⟨A, _a, _b, hKA, hAS, hAcard, _hprefix, _hsuffix, _hcharge,
        _C, _hRange, _hIndependent, _hLate, hAll⟩ :=
      exists_same_trace_prefix_with_all_carrier_degrees_of_small_kernel
        G d K S c hd (by omega) (by omega) hSlarge hKmin htrace hfull hfree
    have hAle : A.card ≤ 2 * d + 2 := by omega
    obtain ⟨D0, hAD0, hD0S, hD0card⟩ :=
      Finset.exists_subsuperset_card_eq hAS hAle hSlarge
    have hKD0 : K ⊆ D0 := hKA.trans hAD0
    have hrest0 : ∀ x ∈ D0, x ∉ K → d + 2 ≤ withinDegree G D0 x + 3 := by
      intro x hxD0 hxK
      have hdeg := hAll D0 hAD0 hD0S x hxD0 hxK
      omega
    obtain ⟨hP4, _hP3P2, _h3P2⟩ :=
      original_residual_forest_free_of_actual_carrier_additive
        (d := d) (h := 3) (by omega) (by omega)
        G D0 K W hD0card hKD0 hWK hK3 hWcard hKmin hWdegree hrest0 hfree
    obtain ⟨z, hz, _hleavesCard, hcenterErase, _hleaves⟩ :=
      H3CountStar1105.original_h3_count_to_residual_star
        G d K W hd hK3 hWcard hWK hQ hKmin hP4
    have hcenter : ∀ x ∈ K \ W, x ≠ z → G.Adj z x := by
      intro x hx hxz
      exact hcenterErase x (Finset.mem_erase.mpr ⟨hxz, hx⟩)
    let H : Finset V := insert z W
    have hzW : z ∉ W := (Finset.mem_sdiff.mp hz).2
    have hHcard : H.card = d := by
      dsimp [H]
      rw [Finset.card_insert_of_notMem hzW, hWcard]
      omega
    have hCover : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x ∈ H ∨ y ∈ H := by
      intro x hxS y hyS hxy
      let B : Finset V := insert x (insert y A)
      have hAB : A ⊆ B :=
        (Finset.subset_insert y A).trans (Finset.subset_insert x (insert y A))
      have hBS : B ⊆ S := by
        intro u hu
        rcases Finset.mem_insert.mp hu with hux | hu
        · simpa only [hux] using hxS
        rcases Finset.mem_insert.mp hu with huy | huA
        · simpa only [huy] using hyS
        · exact hAS huA
      have hBcard : B.card ≤ 2 * d + 2 := by
        have hfirst := Finset.card_insert_le x (insert y A)
        have hsecond := Finset.card_insert_le y A
        dsimp only [B]
        omega
      obtain ⟨D, hBD, hDS, hDcard⟩ :=
        Finset.exists_subsuperset_card_eq hBS hBcard hSlarge
      have hAD : A ⊆ D := hAB.trans hBD
      have hKD : K ⊆ D := hKA.trans hAD
      have hxD : x ∈ D := hBD (Finset.mem_insert_self x (insert y A))
      have hyD : y ∈ D := hBD (Finset.mem_insert_of_mem (Finset.mem_insert_self y A))
      have hrestD : ∀ u ∈ D, u ∉ K → d + 2 ≤ withinDegree G D u + 3 := by
        intro u huD huK
        have hdeg := hAll D hAD hDS u huD huK
        omega
      exact actual_carrier_cover_of_star_center_additive
        (d := d) (h := 3) (by omega) (by omega)
        G D K W z hDcard hKD hWK hK3 hWcard hz hcenter hKmin hWdegree hrestD hfree
        x hxD y hyD hxy
    exact hnocover H hHcard hCover
  have hKlarge : 2 * d + 1 ≤ K.card := by
    by_contra hlt
    have hKsmall : K.card ≤ 2 * d := by omega
    obtain ⟨H, _hHK, hHcard, hCover⟩ :=
      small_kernel_whole_support_cover G d K W S c
        hd hWK hK4 hKsmall hWcard hKmin hWdegree hSlarge htrace hfull hfree
    exact hnocover H hHcard hCover
  exact ⟨K, hKS, hKlower, hKlarge, hKmin, Drem, hDrem, hDremBound,
    hKcount, c, w, htrace, hcharge, hw, hslack, hsteps, hoccurs,
    W, hWK, hWcard, hWdegree⟩

/-- On a connected representative `selectedGraph χ r` with no rainbow `P_{2d+2}`
and palette `q` above the even formula, the nonempty cone `(d+1)`-core branch and
ALL kernel branches `|K| ≤ 2 * d + 2` (`3 ≤ h ≤ d + 2`) are eliminated, forcing a
`d`-core elimination kernel `K` of size `2 * d + 3 ≤ K.card` (and a direct
contradiction whenever `n = 2 * d + 2`). -/
theorem exists_connected_original_color_large_kernel {d n q : ℕ}
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (hconn : (selectedGraph χ r).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    let G : SimpleGraph (Fin n) := selectedGraph χ r
    let S : Finset (Fin n) := Finset.univ
    let B : ℕ := (d - 1).choose 2 + (d - 1) * (S.card - d + 1) + 2
    let D0 : ℕ := (d.choose 2 + d * (S.card - d)) - (withinEdges G S).card
    let delta : ℕ := (withinEdges G S).card - (B + 1)
    degreeCore G d = ∅ ∧
    ∃ K : Finset (Fin n), K ⊆ S ∧ S.card - D0 ≤ K.card ∧
      2 * d + 3 ≤ K.card ∧
      (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ Drem : ℕ, Drem ≤ D0 ∧ Drem ≤ K.card - d - 3 ∧
        (withinEdges G K).card + Drem = d.choose 2 + d * (K.card - d) ∧
        ∃ c w : ℕ, RestorationTrace G d K S c ∧ D0 = Drem + c ∧
          c = (S.card - K.card) + w ∧
          Drem + w + delta = (K.card - d) - 3 ∧
          (∀ U x, ActualRestorationStep G d K S c U x →
            d + 2 ≤ withinDegree G U x + (K.card - d) ∧
            (K.card - d ≤ d → d - (K.card - d) + 2 ≤ withinDegree G U x)) ∧
          (∀ x ∈ S, x ∉ K → ∃ U, ActualRestorationStep G d K S c U x) ∧
          ∃ W : Finset (Fin n), W ⊆ K ∧ W.card = d - 1 ∧
            ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  let S : Finset (Fin n) := Finset.univ
  obtain ⟨J, hcone, _hfreeJ, _hdelete, _hsat, _hlower, hJ⟩ :=
    EvenOriginalNonemptyCore1105.original_even_saturated_first_core_empty
      (by omega) hn χ r hconn hno hq
  have hC : degreeCore G d = ∅ :=
    StrictConeCore1105.degreeCore_eq_empty_of_cone_le G J d hcone hJ
  have hScard : S.card = n := by
    simp only [S, Finset.card_univ, Fintype.card_fin]
  have hSlarge : 2 * d + 2 ≤ S.card := by
    rw [hScard]
    exact hn
  have hEdges : withinEdges G S = G.edgeFinset := by
    ext e
    simp [withinEdges, S]
  have hCount : G.edgeFinset.card = q :=
    selectedGraph_card_edgeFinset χ r
  have hqB : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card := by
    rw [hScard, hEdges, hCount]
    exact hqB
  have hfreeG : (pathGraph (2 * d + 2)).Free G :=
    selectedGraph_free (pathGraph (2 * d + 2)) χ r hno
  have hnocover : ∀ H : Finset (Fin n), H.card = d →
      ¬ (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x ∈ H ∨ y ∈ H) := by
    intro H hHcard hCover
    have hCoverUniv : ∀ u v : Fin n, G.Adj u v → u ∈ H ∨ v ∈ H :=
      fun u v huv => hCover u (Finset.mem_univ u) v (Finset.mem_univ v) huv
    obtain ⟨P, hP⟩ :=
      EvenCoverColorCaller1105.rainbow_path_of_actual_vertex_cover_above_even_max
        hd hn χ r H hHcard hCoverUniv hq
    exact hno P hP
  obtain ⟨K, hKS, hKlower, hK2d1, hKmin, Drem, hDrem, hDremBound,
      hKcount, c, w, htrace, hcharge, hw, hslack, hsteps, hoccurs,
      W, hWK, hWcard, hWdegree⟩ :=
    exists_large_kernel_of_empty_core_and_no_cover
      G d S hd hC hSlarge hthreshold hfreeG hnocover
  have hfull : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d) :=
    fun U x hstep => (hsteps U x hstep).1
  have hVlarge : 2 * d + 2 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hn
  have hKneq2d1 : K.card ≠ 2 * d + 1 := by
    intro hKcard
    obtain ⟨H, _hHK, hHcard, hCoverUniv⟩ :=
      whole_graph_cover_of_kernel_two_d_plus_one G d K W c
        (by omega) hconn hVlarge hWK hKcard hWcard hKmin hWdegree htrace hfull hfreeG
    obtain ⟨P, hP⟩ :=
      EvenCoverColorCaller1105.rainbow_path_of_actual_vertex_cover_above_even_max
        hd hn χ r H hHcard hCoverUniv hq
    exact hno P hP
  have hKneq2d2 : K.card ≠ 2 * d + 2 := by
    intro hKcard
    obtain ⟨H, hHcard, hCoverUniv⟩ :=
      whole_graph_cover_of_kernel_two_d_plus_two G d K W c
        (by omega) hconn hVlarge hWK hKcard hWcard hKmin hWdegree htrace hfull hfreeG
    obtain ⟨P, hP⟩ :=
      EvenCoverColorCaller1105.rainbow_path_of_actual_vertex_cover_above_even_max
        hd hn χ r H hHcard hCoverUniv hq
    exact hno P hP
  have hK2d3 : 2 * d + 3 ≤ K.card := by omega
  exact ⟨hC, K, hKS, hKlower, hK2d3, hKmin, Drem, hDrem, hDremBound,
    hKcount, c, w, htrace, hcharge, hw, hslack, hsteps, hoccurs,
    W, hWK, hWcard, hWdegree⟩

/-- On the diagonal host `n = 2 * d + 2` (`d ≥ 4`), any connected representative
above the even palette formula contains a rainbow `P_{2d+2}` (since `|K| ≥ 2d + 3`
contradicts `|K| ≤ n = 2d + 2`). -/
theorem no_connected_counterexample_at_two_d_plus_two {d q : ℕ}
    (hd : 4 ≤ d)
    (χ : TopEdgeLabeling (Fin (2 * d + 2)) (Fin q)) (r : RepresentativeChoice χ)
    (hconn : (selectedGraph χ r).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin (2 * d + 2))),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * ((2 * d + 2) - d + 1) + 2) < q) : False := by
  obtain ⟨_hC, K, hKS, _hKlower, hK2d3, _⟩ :=
    exists_connected_original_color_large_kernel hd (le_rfl : 2 * d + 2 ≤ 2 * d + 2)
      χ r hconn hno hq
  have hKle : K.card ≤ 2 * d + 2 := by
    have hc := Finset.card_le_card hKS
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  omega

end ErdosProblems.PathUpperReduction.EvenConnectedLargeKernel1105
