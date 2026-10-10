module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import CycleAsymptoticAndPathSeed

@[expose] public section

/-!
# PathKernelAndUniversalExact

Unconditional odd-path exactness, finite host-window reduction, nonempty cone-core and small-kernel (`|K| ≤ 2d + 2`) elimination, large-kernel 2-connected circumference, and `P_8` base-window proofs (`erdos_1105_parts_ii_exact`) for Erdős Problem 1105.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.ActualInducedDegree1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

noncomputable instance graph_neighborSet_fintype {A : Type*} [Finite A]
    (G : SimpleGraph A) (x : A) : Fintype (G.neighborSet x) := Fintype.ofFinite _

theorem degree_induce_eq_withinDegree (G : SimpleGraph V) (W : Finset V)
    (u : (W : Set V)) :
    (G.induce (W : Set V)).degree u = withinDegree G W u.val := by
  classical
  change ((G.induce (W : Set V)).neighborFinset u).card =
    (W.filter (fun z => G.Adj u.val z)).card
  apply Finset.card_bij (fun v _hv => v.val)
  · intro v hv
    have hadj : (G.induce (W : Set V)).Adj u v :=
      (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mp hv
    refine Finset.mem_filter.mpr ⟨v.property, ?_⟩
    exact hadj
  · intro v₁ _hv₁ v₂ _hv₂ hval
    exact Subtype.ext hval
  · intro z hz
    obtain ⟨hzW, hadj⟩ := Finset.mem_filter.mp hz
    let v : (W : Set V) := ⟨z, hzW⟩
    have hv : v ∈ (G.induce (W : Set V)).neighborFinset u := by
      apply (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mpr
      exact hadj
    exact ⟨v, hv, rfl⟩

end ErdosProblems.PathUpperReduction.ActualInducedDegree1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.HighSeedLedgerBridge1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

/- Statement-time classical decisions supply the actual induced edge set;
   no new public decidability or finite-edge hypothesis is introduced. -/
local instance proposition_decidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The exact balance yields the nontruncated twice-edge hypothesis.
No graph or minimum-degree assumption is needed for this arithmetic step. -/
theorem twice_edges_of_deficit_balance {d h e D : ℕ}
    (hd : 1 ≤ d) (hD : D ≤ h - 3)
    (hbalance : e + D = d.choose 2 + d * h) :
    d * (d - 1) + 2 * d * h ≤ 2 * e + 2 * (h - 3) := by
  have hpred : d - 1 + 1 = d := by omega
  have hdouble : 2 * d.choose 2 = d * (d - 1) := by
    have h := Nat.add_one_mul_choose_eq (d - 1) 1
    rw [hpred, Nat.choose_one_right] at h
    simpa only [Nat.reduceAdd, Nat.mul_comm] using h.symm
  calc
    d * (d - 1) + 2 * d * h = 2 * (d.choose 2 + d * h) := by
      rw [Nat.mul_add, hdouble]
      ring
    _ = 2 * (e + D) := congrArg (fun a : ℕ => 2 * a) hbalance.symm
    _ ≤ 2 * e + 2 * (h - 3) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hD) _

/-- Extract an exact-sized subset of original high-degree vertices in the
SAME finite graph whose edge balance is supplied. -/
theorem exists_high_subset_of_deficit_balance {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d h D : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h)
    (horder : Fintype.card V = d + h)
    (hD : D ≤ h - 3)
    (hbalance : G.edgeFinset.card + D = d.choose 2 + d * h) :
    ∃ W : Finset V, W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ G.degree x := by
  classical
  have hedges := twice_edges_of_deficit_balance (by omega : 1 ≤ d) hD hbalance
  have hpool :=
    ErdosProblems.AntiRamseyHighSeedDegreePool1105.high_seed_degree_pool
      G hd hh horder hedges
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hpool
  refine ⟨W, hWcard, ?_⟩
  intro x hx
  have hdegree := (Finset.mem_filter.mp (hWsub hx)).2
  calc
    d + 1 ≤ (Finset.univ.filter (fun w => G.Adj x w)).card := by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using hdegree
    _ = G.degree x := by
      unfold SimpleGraph.degree
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]

/-- The canonical original restricted edge count equals the edge count of
the actual induced graph on every vertex of K, including any isolates. -/
theorem withinEdges_card_eq_induced {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K : Finset V) :
    (withinEdges G K).card = (G.induce (K : Set V)).edgeFinset.card := by
  classical
  unfold withinEdges
  exact G.card_filter_edgeFinset_toFinset_subset K

/-- Obtain exactly d-1 ACTUAL seed vertices, with ORIGINAL degree inside K.
The ledger has the exact output shape of the actual-deficit kernel provider.
No favorable support, filled edge count or replacement graph is substituted. -/
theorem exists_actual_high_seed_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K : Finset V) {d h D : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h) (horder : K.card = d + h)
    (hD : D ≤ h - 3)
    (hbalance : (withinEdges G K).card + D =
      d.choose 2 + d * (K.card - d)) :
    ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  have hkernelOrder : Fintype.card (K : Set V) = d + h := by
    exact (Fintype.card_of_finset' (p := (K : Set V)) K
      (fun _ => Iff.rfl)).trans horder
  have hsub : K.card - d = h := by omega
  have hkernelBalance : (G.induce (K : Set V)).edgeFinset.card + D =
      d.choose 2 + d * h := by
    rw [← withinEdges_card_eq_induced G K, ← hsub]
    exact hbalance
  obtain ⟨W, hWcard, hWdegree⟩ :=
    exists_high_subset_of_deficit_balance (G.induce (K : Set V))
      hd hh hkernelOrder hD hkernelBalance
  let f : (K : Set V) ↪ V := Function.Embedding.subtype (· ∈ (K : Set V))
  refine ⟨W.map f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hx
    exact u.property
  · simpa only [Finset.card_map] using hWcard
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    have hdegree := hWdegree u hu
    rw [ActualInducedDegree1105.degree_induce_eq_withinDegree G K u] at hdegree
    exact hdegree

/-- If D_K is literally the natural edge deficit of the actual K, the
empty-core bound supplies the nontruncation needed for the exact balance.
The same original G is used for the core, deficit and selected degrees. -/
theorem exists_actual_high_seed_subset_of_empty_core_deficit
    {V : Type*} [Fintype V] (G : SimpleGraph V) (K : Finset V)
    {d h : ℕ} (hd : 4 ≤ d) (hh : 3 ≤ h)
    (hcore : ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d = ∅)
    (horder : K.card = d + h)
    (hdeficit : (d.choose 2 + d * (K.card - d)) -
      (withinEdges G K).card ≤ h - 3) :
    ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  have hC : ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d ⊆ K := by
    rw [hcore]
    exact Finset.empty_subset K
  have hM : max d
      (ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d).card ≤
      K.card := by
    rw [hcore, Finset.card_empty, max_eq_left (Nat.zero_le d)]
    omega
  have hcap : (withinEdges G K).card ≤
      d.choose 2 + d * (K.card - d) := by
    simpa only [hcore, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      (core_induced_edge_bound G d K hC hM)
  have hbalance : (withinEdges G K).card +
      ((d.choose 2 + d * (K.card - d)) - (withinEdges G K).card) =
      d.choose 2 + d * (K.card - d) := Nat.add_sub_of_le hcap
  exact exists_actual_high_seed_subset G K hd hh horder hdeficit hbalance

end ErdosProblems.PathUpperReduction.HighSeedLedgerBridge1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.OriginalThresholdTraceHighSeed1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination

/-- Construct one actual minimum-degree kernel, its exact restoration trace,
and an exact-sized original high-degree subset from the literal original
strict linear edge threshold. Public input needs only a finite carrier. -/
theorem exists_actual_kernel_with_trace_and_high_seed_of_strict_linear_edges
    {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hS : d + 3 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card) :
    let D : ℕ := (d.choose 2 + d * (S.card - d)) - (withinEdges G S).card
    ∃ K : Finset V, K ⊆ S ∧ S.card - D ≤ K.card ∧
      d + 3 ≤ K.card ∧ (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ Drem : ℕ, Drem ≤ D ∧ Drem ≤ K.card - d - 3 ∧
        (withinEdges G K).card + Drem =
          d.choose 2 + d * (K.card - d) ∧
        (∃ c : ℕ, RestorationTrace1105.RestorationTrace G d K S c ∧
          D = Drem + c) ∧
        ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
          ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  let Q : ℕ := d.choose 2 + d * (S.card - d)
  let B : ℕ := (d - 1).choose 2 + (d - 1) * (S.card - d + 1) + 2
  let D : ℕ := Q - (withinEdges G S).card
  have hcoreSubset : degreeCore G d ⊆ S := by
    rw [hC]
    exact Finset.empty_subset S
  have hcoreSize : max d (degreeCore G d).card ≤ S.card := by
    rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)]
    omega
  have hcap : (withinEdges G S).card ≤ Q := by
    dsimp only [Q]
    simpa only [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      (core_induced_edge_bound G d S hcoreSubset hcoreSize)
  have hbalance : (withinEdges G S).card + D = Q := by
    dsimp only [D]
    exact Nat.add_sub_of_le hcap
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using
      (Nat.choose_succ_succ' (d - 1) 1)
  have hmul : d * (S.card - d) = ((d - 1) + 1) * (S.card - d) := by
    rw [hpred]
  have hbase : Q =
      ((d - 1).choose 2 + (d - 1) * (S.card - d + 1)) + (S.card - d) := by
    dsimp only [Q]
    rw [hchoose, hmul]
    ring
  /- The additive gap retains all guarded natural subtractions literally. -/
  have hgap : Q = B + (S.card - d - 2) := by
    dsimp only [B]
    rw [hbase]
    omega
  have hgapExact : Q - B = S.card - d - 2 := by omega
  have hstrict : B < (withinEdges G S).card := hthreshold
  have hdeficit : D ≤ S.card - d - 3 := by omega
  obtain ⟨K, hKS, hKlower, hKsize, hKmin, Drem, hDrem, hDremBound,
      hKcount, c, htrace, hcharge⟩ :=
    RestorationTrace1105.exists_actual_kernel_with_restoration_trace_of_empty_core_deficit
      G d S D hC hS hdeficit hbalance
  let h : ℕ := K.card - d
  have hh : 3 ≤ h := by dsimp only [h]; omega
  have horder : K.card = d + h := by dsimp only [h]; omega
  have hrem : Drem ≤ h - 3 := hDremBound
  obtain ⟨W, hWK, hWcard, hWdegree⟩ :=
    HighSeedLedgerBridge1105.exists_actual_high_seed_subset
      G K hd hh horder hrem hKcount
  exact ⟨K, hKS, hKlower, hKsize, hKmin,
    Drem, hDrem, hDremBound, hKcount,
    ⟨c, htrace, hcharge⟩, W, hWK, hWcard, hWdegree⟩

end ErdosProblems.PathUpperReduction.OriginalThresholdTraceHighSeed1105
end

noncomputable section
namespace ErdosProblems.PathUpperReduction.TracePrefixSlack1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- An actual constructor occurrence, with its actual prefix and suffix.
This is Prop-valued decomposition, with exact cumulative charge splitting. -/
def ActualRestorationStep (G : SimpleGraph V) (d : ℕ)
    (K S : Finset V) (c : ℕ) (U : Finset V) (x : V) : Prop :=
  ∃ a b : ℕ, RestorationTrace G d K U a ∧ x ∉ U ∧
    withinDegree G U x < d ∧ RestorationTrace G d (insert x U) S b ∧
    c = a + (d - withinDegree G U x) + b

omit [Fintype V] in
/-- Actual suffix concatenation; elimination is entirely into Prop. -/
theorem restoration_trace_append [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (K U S : Finset V) (a b : ℕ)
    (hprefix : RestorationTrace G d K U a)
    (hsuffix : RestorationTrace G d U S b) :
    RestorationTrace G d K S (a + b) := by
  induction hsuffix with
  | nil => simpa only [Nat.add_zero] using hprefix
  | @snoc T q trace y hfresh hlow ih =>
      have hnew := RestorationTrace.snoc ih y hfresh hlow
      simpa only [Nat.add_assoc] using hnew

omit [Fintype V] in
/-- Every latest actual constructor has an actual decomposition (nil suffix). -/
theorem actual_step_last [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (K U : Finset V) (a : ℕ) (hprefix : RestorationTrace G d K U a)
    (x : V) (hfresh : x ∉ U) (hlow : withinDegree G U x < d) :
    ActualRestorationStep G d K (insert x U)
      (a + (d - withinDegree G U x)) U x := by
  refine ⟨a, 0, hprefix, hfresh, hlow, RestorationTrace.nil, ?_⟩
  omega

omit [Fintype V] in
/-- No favorable prefix is selected. -/
theorem actual_step_preserved_snoc [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (K S U : Finset V) (c : ℕ) (x y : V)
    (hstep : ActualRestorationStep G d K S c U x)
    (hfresh : y ∉ S) (hlow : withinDegree G S y < d) :
    ActualRestorationStep G d K (insert y S)
      (c + (d - withinDegree G S y)) U x := by
  obtain ⟨a, b, hprefix, hx, hj, hsuffix, hcharge⟩ := hstep
  refine ⟨a, b + (d - withinDegree G S y), hprefix, hx, hj,
    RestorationTrace.snoc hsuffix y hfresh hlow, ?_⟩
  omega

/-- Every actual restored vertex has a coupled actual constructor occurrence.
The existential stays in Prop; no data-valued extraction or list is used. -/
theorem restoration_trace_step_exists (G : SimpleGraph V) (d : ℕ)
    (K S : Finset V) (c : ℕ) (htrace : RestorationTrace G d K S c) :
    ∀ x ∈ S, x ∉ K → ∃ U, ActualRestorationStep G d K S c U x := by
  induction htrace with
  | nil =>
      intro x hx hnot
      exact False.elim (hnot hx)
  | @snoc T q trace y hfresh hlow ih =>
      intro x hx hnot
      by_cases hxy : x = y
      · subst x
        exact ⟨T, actual_step_last G d K T q trace y hfresh hlow⟩
      · have hxT : x ∈ T := by
          obtain hxy' | hxT := Finset.mem_insert.mp hx
          · exact False.elim (hxy hxy')
          · exact hxT
        obtain ⟨U, hstep⟩ := ih x hxT hnot
        exact ⟨U, actual_step_preserved_snoc G d K T U q x y hstep hfresh hlow⟩

/-- The excess of ANY actual constructor is at most the whole trace's excess.
The prefix/suffix cardinalities and exact charge splitting supply this bound. -/
theorem actual_step_defect_le_excess (G : SimpleGraph V) (d : ℕ)
    (K S U : Finset V) (c w : ℕ) (x : V)
    (hw : c = (S.card - K.card) + w)
    (hstep : ActualRestorationStep G d K S c U x) :
    (d - 1) - withinDegree G U x ≤ w := by
  classical
  obtain ⟨a, b, hprefix, hfresh, hlow, hsuffix, hcharge⟩ := hstep
  obtain ⟨hKU, _hpCard, _hpEdges, wp, hwp⟩ :=
    restoration_trace_ledgers G d K U a hprefix
  obtain ⟨hUS, _hsCard, _hsEdges, ws, hws⟩ :=
    restoration_trace_ledgers G d (insert x U) S b hsuffix
  have hpLe : K.card ≤ U.card := Finset.card_le_card hKU
  have hsLe : (insert x U).card ≤ S.card := Finset.card_le_card hUS
  have hcard : (insert x U).card = U.card + 1 :=
    Finset.card_insert_of_notMem hfresh
  have hdefect : d - withinDegree G U x =
      1 + ((d - 1) - withinDegree G U x) := by omega
  /- Cancels the actual restored cardinalities, giving
     w = wp + ((d-1)-j) + ws, with all three terms nonnegative. -/
  omega

/-- Preserve every original combined output and add literal slack together
with the safe additive bound for ALL actual restoration-step decompositions.
The natural-subtraction bound is explicitly conditional on K.card-d ≤ d. -/
theorem exists_actual_kernel_with_trace_high_seed_slack_and_prefix_bounds
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
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
            d + 2 ≤ withinDegree G U x + (K.card - d) ∧
            (K.card - d ≤ d → d - (K.card - d) + 2 ≤ withinDegree G U x)) ∧
          (∀ x ∈ S, x ∉ K → ∃ U, ActualRestorationStep G d K S c U x) ∧
          ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
            ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  let B : ℕ := (d - 1).choose 2 + (d - 1) * (S.card - d + 1) + 2
  let Q : ℕ := d.choose 2 + d * (S.card - d)
  let D : ℕ := Q - (withinEdges G S).card
  let delta : ℕ := (withinEdges G S).card - (B + 1)
  have hcoreSubset : degreeCore G d ⊆ S := by
    rw [hC]
    exact Finset.empty_subset S
  have hcoreSize : max d (degreeCore G d).card ≤ S.card := by
    rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)]
    omega
  have hcap : (withinEdges G S).card ≤ Q := by
    dsimp only [Q]
    simpa only [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      (core_induced_edge_bound G d S hcoreSubset hcoreSize)
  have hbalance : (withinEdges G S).card + D = Q := by
    dsimp only [D]
    exact Nat.add_sub_of_le hcap
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using
      (Nat.choose_succ_succ' (d - 1) 1)
  have hmul : d * (S.card - d) = ((d - 1) + 1) * (S.card - d) := by
    rw [hpred]
  have hbase : Q =
      ((d - 1).choose 2 + (d - 1) * (S.card - d + 1)) + (S.card - d) := by
    dsimp only [Q]
    rw [hchoose, hmul]
    ring
  have hgap : Q = B + (S.card - d - 2) := by
    dsimp only [B]
    rw [hbase]
    omega
  have hstrict : B < (withinEdges G S).card := hthreshold
  have hdelta : (withinEdges G S).card = B + 1 + delta := by
    dsimp only [delta]
    omega
  have hslack : D + delta = S.card - d - 3 := by omega
  obtain ⟨K, hKS, hKlower, hKsize, hKmin, Drem, hDrem, hDremBound,
      hKcount, htraceCharge, W, hWK, hWcard, hWdegree⟩ :=
    OriginalThresholdTraceHighSeed1105.exists_actual_kernel_with_trace_and_high_seed_of_strict_linear_edges
      G d S hd hC hS hthreshold
  obtain ⟨c, htrace, hcharge⟩ := htraceCharge
  obtain ⟨_hKS, hcard, _hedges, w, hw⟩ :=
    restoration_trace_ledgers G d K S c htrace
  have hfinalSlack : Drem + w + delta = (K.card - d) - 3 := by omega
  have hsteps : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d) ∧
      (K.card - d ≤ d → d - (K.card - d) + 2 ≤ withinDegree G U x) := by
    intro U x hstep
    have hdefect := actual_step_defect_le_excess G d K S U c w x hw hstep
    obtain ⟨_a, _b, _hp, _hf, hlow, _hs, _hc⟩ := hstep
    constructor
    · omega
    · intro hsmall
      omega
  exact ⟨K, hKS, hKlower, hKsize, hKmin, Drem, hDrem, hDremBound,
    hKcount, c, w, htrace, hcharge, hw, hfinalSlack, hsteps,
    restoration_trace_step_exists G d K S c htrace,
    W, hWK, hWcard, hWdegree⟩

end ErdosProblems.PathUpperReduction.TracePrefixSlack1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.ActualPrefixCarrierDegree1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualTraceCarrierCut1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Extend the ACTUAL local occurrence through its ACTUAL carrier suffix.
The earlier support and vertex are unchanged; cumulative charge is exact. -/
theorem actual_step_extend_suffix
    (G : SimpleGraph V) (d : ℕ) (K D S U : Finset V) (a b : ℕ) (x : V)
    (hstep : ActualRestorationStep G d K D a U x)
    (hsuffix : RestorationTrace G d D S b) :
    ActualRestorationStep G d K S (a + b) U x := by
  obtain ⟨p, q, hprefix, hfresh, hlow, htail, hcharge⟩ := hstep
  have hfullTail := restoration_trace_append G d (insert x U) D S q b
    htail hsuffix
  refine ⟨p, q + b, hprefix, hfresh, hlow, hfullTail, ?_⟩
  omega

/-- Internally construct the actual 2d+2 prefix carrier and derive the
original carrier degree of EVERY retained vertex outside the SAME K.
The universal actual-step guard is exactly the earlier structural output;
K.card≤2d selects its valid smaller-seed branch without choosing a kernel. -/
theorem exists_actual_prefix_carrier_with_restored_degree_bounds
    (G : SimpleGraph V) (d : ℕ) (K S : Finset V) (c : ℕ)
    (htrace : RestorationTrace G d K S c)
    (hKsmall : K.card ≤ 2 * d) (hSlarge : 2 * d + 2 ≤ S.card)
    (hsteps : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d)) :
    ∃ D : Finset V, ∃ a b : ℕ,
      K ⊆ D ∧ D ⊆ S ∧ D.card = 2 * d + 2 ∧
      RestorationTrace G d K D a ∧ RestorationTrace G d D S b ∧
      c = a + b ∧
      ∀ x ∈ D, x ∉ K →
        d - (K.card - d) + 2 ≤ withinDegree G D x := by
  classical
  have hKfeasible : K.card ≤ 2 * d + 2 := by omega
  obtain ⟨D, a, b, hKD, hDS, hDcard, hprefix, hsuffix, hcharge⟩ :=
    exists_actual_restoration_trace_cut G d K S c htrace
      (2 * d + 2) hKfeasible hSlarge
  refine ⟨D, a, b, hKD, hDS, hDcard, hprefix, hsuffix, hcharge, ?_⟩
  intro x hxD hxK
  obtain ⟨U, hstepD⟩ :=
    restoration_trace_step_exists G d K D a hprefix x hxD hxK
  have hstepAb := actual_step_extend_suffix G d K D S U a b x hstepD hsuffix
  have hstepFull : ActualRestorationStep G d K S c U x := by
    rw [hcharge]
    exact hstepAb
  have hguard := hsteps U x hstepFull
  obtain ⟨p, q, _hlocalPrefix, _hfresh, _hlow, hlocalSuffix, _hlocalCharge⟩ :=
    hstepD
  have hUDinsert : insert x U ⊆ D :=
    (restoration_trace_ledgers G d (insert x U) D q hlocalSuffix).1
  have hUD : U ⊆ D := (Finset.subset_insert x U).trans hUDinsert
  have hmono := withinDegree_le_of_subset G U D x hUD
  have hsmall : K.card - d ≤ d := by omega
  omega

/-- Literal original threshold: construct ONE actual kernel, trace and W
internally, then export its carrier degrees in the explicit smaller branch.
No kernel, trace, deficit, favorable occurrence or degree guard is an input. -/
theorem exists_actual_kernel_high_seed_and_guarded_prefix_carrier
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card) :
    ∃ K : Finset V, K ⊆ S ∧ d + 3 ≤ K.card ∧
      (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
        (∀ x ∈ W, d + 1 ≤ withinDegree G K x) ∧
        (K.card ≤ 2 * d →
          ∃ D : Finset V, ∃ a b c : ℕ,
            K ⊆ D ∧ D ⊆ S ∧ D.card = 2 * d + 2 ∧
            RestorationTrace G d K D a ∧ RestorationTrace G d D S b ∧
            RestorationTrace G d K S c ∧ c = a + b ∧
            ∀ x ∈ D, x ∉ K →
              d - (K.card - d) + 2 ≤ withinDegree G D x) := by
  classical
  have hS : d + 3 ≤ S.card := by omega
  obtain ⟨K, hKS, _hKlower, hKsize, hKmin, Drem, _hDrem, _hDremBound,
      _hKcount, c, w, htrace, _hcharge, _hw, _hslack, hsteps, _hoccurs,
      W, hWK, hWcard, hWdegree⟩ :=
    exists_actual_kernel_with_trace_high_seed_slack_and_prefix_bounds
      G d S hd hC hS hthreshold
  have hstepsAdd : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d) := by
    intro U x hstep
    exact (hsteps U x hstep).1
  refine ⟨K, hKS, hKsize, hKmin, W, hWK, hWcard, hWdegree, ?_⟩
  intro hKsmall
  obtain ⟨D, a, b, hKD, hDS, hDcard, hprefix, hsuffix, hsplit, hdegrees⟩ :=
    exists_actual_prefix_carrier_with_restored_degree_bounds
      G d K S c htrace hKsmall hSlarge hstepsAdd
  exact ⟨D, a, b, c, hKD, hDS, hDcard, hprefix, hsuffix, htrace, hsplit, hdegrees⟩

end ErdosProblems.PathUpperReduction.ActualPrefixCarrierDegree1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.ActualNestedPrefixGuards1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualTraceCarrierCut1105
open ErdosProblems.PathUpperReduction.ActualPrefixCarrierDegree1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Every ACTUAL occurrence in this prefix inherits the original full-trace
bound at the SAME earlier support and vertex, via the ACTUAL suffix. -/
theorem actual_prefix_steps_lower_bound
    (G : SimpleGraph V) (d : ℕ) (K A S : Finset V) (a b c : ℕ)
    (hKsmall : K.card ≤ 2 * d)
    (hsuffix : RestorationTrace G d A S b) (hcharge : c = a + b)
    (hfull : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d)) :
    ∀ U x, ActualRestorationStep G d K A a U x →
      d - (K.card - d) + 2 ≤ withinDegree G U x := by
  intro U x hstep
  have hextended := actual_step_extend_suffix G d K A S U a b x hstep hsuffix
  have hwhole : ActualRestorationStep G d K S c U x := by
    rw [hcharge]
    exact hextended
  have hbound := hfull U x hwhole
  have hsmall : K.card - d ≤ d := by omega
  omega

/-- Recorded earlier degrees give original retained-prefix degrees because
the ACTUAL occurrence's local suffix proves support inclusion. -/
theorem retained_degree_of_actual_prefix_steps
    (G : SimpleGraph V) (d : ℕ) (K A : Finset V) (a r : ℕ)
    (hprefix : RestorationTrace G d K A a)
    (hsteps : ∀ U x, ActualRestorationStep G d K A a U x →
      r ≤ withinDegree G U x) :
    ∀ x ∈ A, x ∉ K → r ≤ withinDegree G A x := by
  classical
  intro x hxA hxK
  obtain ⟨U, hstep⟩ := restoration_trace_step_exists G d K A a hprefix x hxA hxK
  have hbound := hsteps U x hstep
  obtain ⟨p, q, _hp, _hfresh, _hlow, hsuffix, _hcharge⟩ := hstep
  have hUA : U ⊆ A := (Finset.subset_insert x U).trans
    (restoration_trace_ledgers G d (insert x U) A q hsuffix).1
  exact hbound.trans (withinDegree_le_of_subset G U A x hUA)

/-- Original strict B chooses ONE K and W. In its smaller-kernel branch,
internally choose nested actual A2d/D2d+2 and derive EVERY recorded earlier
degree, retained degree and seed degree required by the cycle route. -/
theorem exists_actual_kernel_with_nested_prefix_guards
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card) :
    ∃ K : Finset V, K ⊆ S ∧ d + 3 ≤ K.card ∧
      (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
        (∀ x ∈ W, d + 1 ≤ withinDegree G K x) ∧
        (K.card ≤ 2 * d →
          ∃ A D : Finset V, ∃ a b t c : ℕ,
            K ⊆ A ∧ A ⊆ D ∧ D ⊆ S ∧
            A.card = 2 * d ∧ D.card = 2 * d + 2 ∧
            RestorationTrace G d K A a ∧
            RestorationTrace G d K D (a + b) ∧
            RestorationTrace G d A D b ∧ RestorationTrace G d D S t ∧
            RestorationTrace G d K S c ∧ c = a + b + t ∧
            (∀ U x, ActualRestorationStep G d K A a U x →
              d - (K.card - d) + 2 ≤ withinDegree G U x) ∧
            (∀ U x, ActualRestorationStep G d K D (a + b) U x →
              d - (K.card - d) + 2 ≤ withinDegree G U x) ∧
            (∀ x ∈ K, d ≤ withinDegree G A x) ∧
            (∀ x ∈ W, d + 1 ≤ withinDegree G A x) ∧
            (∀ x ∈ A, x ∉ K →
              d - (K.card - d) + 2 ≤ withinDegree G A x) ∧
            (∀ x ∈ D, x ∉ K →
              d - (K.card - d) + 2 ≤ withinDegree G D x)) := by
  classical
  have hS : d + 3 ≤ S.card := by omega
  obtain ⟨K, hKS, _hKlower, hKsize, hKmin, Drem, _hDrem, _hDremBound,
      _hKcount, c, w, htrace, _hcharge, _hw, _hslack, hfull, _hoccurs,
      W, hWK, hWcard, hWdegree⟩ :=
    exists_actual_kernel_with_trace_high_seed_slack_and_prefix_bounds
      G d S hd hC hS hthreshold
  have hfullAdd : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d) := by
    intro U x hstep
    exact (hfull U x hstep).1
  refine ⟨K, hKS, hKsize, hKmin, W, hWK, hWcard, hWdegree, ?_⟩
  intro hKsmall
  have hKlargeCarrier : K.card ≤ 2 * d + 2 := by omega
  obtain ⟨D, q, t, hKD, hDS, hDcard, hprefixD, hsuffixD, hsplitD⟩ :=
    exists_actual_restoration_trace_cut G d K S c htrace
      (2 * d + 2) hKlargeCarrier hSlarge
  have hDlarge : 2 * d ≤ D.card := by omega
  obtain ⟨A, a, b, hKA, hAD, hAcard, hprefixA, hmiddle, hsplitA⟩ :=
    exists_actual_restoration_trace_cut G d K D q hprefixD
      (2 * d) hKsmall hDlarge
  have hprefixDab : RestorationTrace G d K D (a + b) := by
    rw [← hsplitA]
    exact hprefixD
  have hsuffixA : RestorationTrace G d A S (b + t) :=
    restoration_trace_append G d A D S b t hmiddle hsuffixD
  have htotal : c = a + b + t := by omega
  have htotalA : c = a + (b + t) := by omega
  have hstepsA := actual_prefix_steps_lower_bound G d K A S a (b + t) c
    hKsmall hsuffixA htotalA hfullAdd
  have hstepsD := actual_prefix_steps_lower_bound G d K D S (a + b) t c
    hKsmall hsuffixD htotal hfullAdd
  have hdegreesA := retained_degree_of_actual_prefix_steps G d K A a
    (d - (K.card - d) + 2) hprefixA hstepsA
  have hdegreesD := retained_degree_of_actual_prefix_steps G d K D (a + b)
    (d - (K.card - d) + 2) hprefixDab hstepsD
  refine ⟨A, D, a, b, t, c, hKA, hAD, hDS, hAcard, hDcard,
    hprefixA, hprefixDab, hmiddle, hsuffixD, htrace, htotal,
    hstepsA, hstepsD, ?_, ?_, hdegreesA, hdegreesD⟩
  · intro x hxK
    exact (hKmin x hxK).trans (withinDegree_le_of_subset G K A x hKA)
  · intro x hxW
    exact (hWdegree x hxW).trans (withinDegree_le_of_subset G K A x hKA)

end ErdosProblems.PathUpperReduction.ActualNestedPrefixGuards1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.ActualPrefixFilledCycle1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualNestedPrefixGuards1105
open ErdosProblems.PathUpperReduction.SeedFillCycleClosure1105
open ErdosProblems.PathUpperReduction.KernelCycleInsertion1105
open ErdosProblems.PathUpperReduction.CycleCopy1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Prop-valued exact support; the separate order equality avoids extracting
a data-valued cycle copy from a Prop-valued restoration trace. -/
def HasExactCycleCopy (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∃ n : ℕ, ∃ c : Copy (cycleGraph n) G,
    n = U.card ∧ Set.range c = (U : Set V)

omit [Fintype V] in
/-- The existing clique-copy API lacks a support conclusion, so apply it
INSIDE the actual seed subtype and project its copy back to the same graph.
Equal finite cardinalities then give surjectivity onto precisely the seed. -/
theorem filled_seed_has_exact_cycle_copy [Fintype V] (G : SimpleGraph V) (K : Finset V) :
    HasExactCycleCopy (fillSeed G K) K := by
  classical
  let J := fillSeed G K
  let H := J.induce (K : Set V)
  have hcl : ∀ x ∈ (Finset.univ : Finset (K : Set V)),
      ∀ y ∈ (Finset.univ : Finset (K : Set V)), x ≠ y → H.Adj x y := by
    intro x _hx y _hy hxy
    exact fillSeed_isClique G K x.property y.property
      (fun h => hxy (Subtype.ext h))
  obtain ⟨c⟩ :=
    ErdosProblems.PathUpperReduction.CoreSizeUpper1105.clique_cycle_copy H
      (Finset.univ : Finset (K : Set V)) K.card hcl (by simp)
  have hsurj : Function.Surjective c :=
    ((Fintype.bijective_iff_injective_and_card c).mpr
      ⟨c.injective, by simp⟩).2
  let C : Copy (cycleGraph K.card) J := (Copy.induce J (K : Set V)).comp c
  refine ⟨K.card, C, rfl, ?_⟩
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact (c i).property
  · intro hv
    obtain ⟨i, hi⟩ := hsurj ⟨v, hv⟩
    refine ⟨i, ?_⟩
    exact congrArg Subtype.val hi

omit [Fintype V] in
/-- The copy's FULL exact support determines its actual contact count.
The bijection uses the actual copy map, never a caller-supplied count. -/
theorem copy_contact_count_eq_withinDegree (G : SimpleGraph V) (U : Finset V)
    {n : ℕ} (c : Copy (cycleGraph n) G)
    (hrange : Set.range c = (U : Set V)) (x : V) :
    (Finset.univ.filter (fun i : Fin n => G.Adj x (c i))).card =
      withinDegree G U x := by
  classical
  unfold withinDegree
  apply Finset.card_bij (fun i _hi => c i)
  · intro i hi
    have hxci := (Finset.mem_filter.mp hi).2
    have hciU : c i ∈ U := by
      have hci : c i ∈ Set.range c := ⟨i, rfl⟩
      simpa only [hrange, Finset.mem_coe] using hci
    exact Finset.mem_filter.mpr ⟨hciU, hxci⟩
  · intro i _hi j _hj hij
    exact c.injective hij
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzrange : z ∈ Set.range c := by
      rw [hrange]
      exact hz'.1
    obtain ⟨i, hi⟩ := hzrange
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hi⟩
    exact hi.symm ▸ hz'.2

/-- One ACTUAL restoration extends an exact cycle. The cover bound and
original contact count are derived from the same filled seed and support. -/
theorem exact_filled_cycle_copy_after_actual_restoration
    (G : SimpleGraph V) (d : ℕ) (K U : Finset V) (x : V)
    (hKlarge : d + 3 ≤ K.card) (hKU : K ⊆ U)
    (hUupper : U.card + 1 ≤ 2 * d) (hfresh : x ∉ U)
    (hcontact : d - (K.card - d) + 2 ≤ withinDegree G U x)
    (hcycle : HasExactCycleCopy (fillSeed G K) U) :
    HasExactCycleCopy (fillSeed G K) (insert x U) := by
  classical
  obtain ⟨m, c, hm, hrange⟩ := hcycle
  subst m
  have hKle : K.card ≤ U.card := Finset.card_le_card hKU
  have hthree : 3 ≤ U.card := by omega
  let n := U.card - 3
  have hn : n + 3 = U.card := by dsimp only [n]; omega
  let J := fillSeed G K
  obtain ⟨c', hrange'⟩ :
      ∃ c' : Copy (cycleGraph (n + 3)) J, Set.range c' = (U : Set V) := by
    rw [hn]
    exact ⟨c, hrange⟩
  have hxK : x ∉ K := fun hx => hfresh (hKU hx)
  have hcount : (Finset.univ.filter
      (fun i : Fin (n + 3) => J.Adj x (c' i))).card = withinDegree G U x := by
    rw [copy_contact_count_eq_withinDegree J U c' hrange' x]
    exact fillSeed_withinDegree_outside G K U hxK
  have hKrange : ∀ v ∈ K, v ∈ Set.range c' := by
    intro v hv
    rw [hrange']
    exact hKU hv
  have hcover : ∀ X : Finset V,
      (∀ u ∈ K, ∀ v ∈ K, J.Adj u v → u ∈ X ∨ v ∈ X) → K.card - 1 ≤ X.card := by
    intro X hX
    exact fillSeed_cover_bound G K X hX
  have hgap : n + 3 - withinDegree G U x < K.card - 1 := by
    have hsmall : K.card - d ≤ d := by omega
    omega
  have hxfresh : x ∉ Set.range c' := by
    rw [hrange']
    exact hfresh
  obtain ⟨C, hC, hlength, hsupport⟩ :=
    cycle_with_exact_support_of_cover_gap J c' x K
      (withinDegree G U x) (K.card - 1) hKrange hcover hcount hgap hxfresh
  obtain ⟨cnew, _henum, hnewrange⟩ := exists_cycle_copy_with_exact_support J C hC
  refine ⟨C.length, cnew, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hfresh]
    omega
  · rw [hnewrange]
    ext v
    change v ∈ C.support ↔ v ∈ ((insert x U : Finset V) : Set V)
    rw [hsupport v, hrange']
    simp only [Finset.mem_coe, Finset.mem_insert]

/-- Structural induction follows the ACTUAL restoration constructors.
Every earlier guard is inherited by extending its actual recorded suffix. -/
theorem actual_trace_has_exact_filled_cycle_copy
    (G : SimpleGraph V) (d : ℕ) (K U : Finset V) (a : ℕ)
    (htrace : RestorationTrace G d K U a)
    (hKlarge : d + 3 ≤ K.card) (hUupper : U.card ≤ 2 * d)
    (hsteps : ∀ T x, ActualRestorationStep G d K U a T x →
      d - (K.card - d) + 2 ≤ withinDegree G T x) :
    HasExactCycleCopy (fillSeed G K) U := by
  classical
  revert hUupper hsteps
  induction htrace with
  | nil =>
      intro _hupper _hsteps
      exact filled_seed_has_exact_cycle_copy G K
  | @snoc T q trace x hfresh hlow ih =>
      intro hupper hsteps
      have hcard : (insert x T).card = T.card + 1 :=
        Finset.card_insert_of_notMem hfresh
      have hTupper : T.card ≤ 2 * d := by omega
      have hprevious : ∀ U y, ActualRestorationStep G d K T q U y →
          d - (K.card - d) + 2 ≤ withinDegree G U y := by
        intro U y hstep
        exact hsteps U y
          (actual_step_preserved_snoc G d K T U q y x hstep hfresh hlow)
      have hcycle := ih hTupper hprevious
      have hKU : K ⊆ T := (restoration_trace_ledgers G d K T q trace).1
      have hcontact := hsteps T x (actual_step_last G d K T q trace x hfresh hlow)
      exact exact_filled_cycle_copy_after_actual_restoration G d K T x
        hKlarge hKU (by omega) hfresh hcontact hcycle

/-- ORIGINAL strict B selects ONE actual kernel/prefix and derives all step
guards internally. This endpoint honestly concludes only the filled cycle;
the seed reversal adapter and actual-carrier transport are not assumed here. -/
theorem exists_actual_prefix_with_exact_filled_cycle
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card) :
    ∃ K : Finset V, K ⊆ S ∧ d + 3 ≤ K.card ∧
      (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      (K.card ≤ 2 * d → ∃ A : Finset V, K ⊆ A ∧ A ⊆ S ∧
        A.card = 2 * d ∧ (∀ x ∈ K, d ≤ withinDegree G A x) ∧
        HasExactCycleCopy (fillSeed G K) A) := by
  obtain ⟨K, hKS, hKlarge, hKmin, W, _hWK, _hWcard, _hWdegree, hbranch⟩ :=
    exists_actual_kernel_with_nested_prefix_guards G d S hd hC hSlarge hthreshold
  refine ⟨K, hKS, hKlarge, hKmin, ?_⟩
  intro hKsmall
  obtain ⟨A, D, a, b, t, c, hKA, hAD, hDS, hAcard, _hDcard,
    hprefixA, _hprefixD, _hmiddle, _hsuffixD, _hwhole, _hcharge,
    hstepsA, _hstepsD, hseedA, _hhighA, _hretainedA, _hretainedD⟩ := hbranch hKsmall
  exact ⟨A, hKA, hAD.trans hDS, hAcard, hseedA,
    actual_trace_has_exact_filled_cycle_copy G d K A a hprefixA hKlarge
      (by omega) hstepsA⟩

end ErdosProblems.PathUpperReduction.ActualPrefixFilledCycle1105
end

noncomputable section
namespace ErdosProblems.PathUpperReduction.ActualPrefixCycle1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.ActualInducedDegree1105
open ErdosProblems.PathUpperReduction.SeedFillCycleClosure1105
open ErdosProblems.PathUpperReduction.ActualPrefixFilledCycle1105
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualNestedPrefixGuards1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

noncomputable instance graph_neighborSet_fintype {T : Type*} [Finite T]
    (G : SimpleGraph T) (x : T) : Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Lift the actual filled-prefix copy to its whole finite carrier, reverse
only seed pairs there, and project the resulting ORIGINAL copy back. No cycle
or favorable subset is selected after changing the graph. -/
theorem original_cycle_copy_of_actual_seed_filling
    (G : SimpleGraph V) (d : ℕ) (K A : Finset V)
    (hd : 2 ≤ d) (hAcard : A.card = 2 * d)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G A x)
    (hfilled : HasExactCycleCopy (fillSeed G K) A) :
    ∃ C : Copy (cycleGraph (2 * d)) G, Set.range C = (A : Set V) := by
  classical
  let e : (A : Set V) ≃ Fin (2 * d) :=
    Fintype.equivFinOfCardEq (by simpa using hAcard)
  let H := G.induce (A : Set V)
  let J : SimpleGraph (Fin (2 * d)) := H.map e.toEmbedding
  let L : Finset (Fin (2 * d)) :=
    Finset.univ.filter (fun i => (e.symm i).val ∈ K)
  have hLdegree : ∀ i ∈ L, d ≤ J.degree i := by
    intro i hi
    have hiK : (e.symm i).val ∈ K := (Finset.mem_filter.mp hi).2
    have hmap : J.degree (e (e.symm i)) = H.degree (e.symm i) :=
      H.degree_map_apply e.toEmbedding (e.symm i)
    rw [e.apply_symm_apply] at hmap
    rw [hmap, degree_induce_eq_withinDegree G A (e.symm i)]
    exact hseed _ hiK
  obtain ⟨n, c, hn, hrange⟩ := hfilled
  have hn2d : n = 2 * d := hn.trans hAcard
  subst hn2d
  have hcA : ∀ i, c i ∈ A := by
    intro i
    have hi : c i ∈ Set.range c := ⟨i, rfl⟩
    simpa only [hrange, Finset.mem_coe] using hi
  let f : Fin (2 * d) → Fin (2 * d) := fun i => e ⟨c i, hcA i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hsub := e.injective hij
    exact c.injective (congrArg Subtype.val hsub)
  have hfL : ∀ i, c i ∈ K → f i ∈ L := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [f, Equiv.symm_apply_apply] using hi
  let cf : Copy (cycleGraph (2 * d)) (fillSeed J L) :=
    { toHom :=
        { toFun := f
          map_rel' := by
            intro i j hij
            have hfilledAdj := c.toHom.map_rel' hij
            apply (fillSeed_adj_iff J L (f i) (f j)).mpr
            rcases (fillSeed_adj_iff G K (c i) (c j)).mp hfilledAdj with hG | hK
            · apply Or.inl
              apply (SimpleGraph.map_adj e.toEmbedding H (f i) (f j)).mpr
              exact ⟨⟨c i, hcA i⟩, ⟨c j, hcA j⟩, hG, rfl, rfl⟩
            · exact Or.inr ⟨hfL i hK.1, hfL j hK.2.1,
                fun h => hij.ne (hf h)⟩ }
      injective' := hf }
  have hfinFilled : cycleGraph (2 * d) ⊑ fillSeed J L := ⟨cf⟩
  have hfinOriginal : cycleGraph (2 * d) ⊑ J :=
    (cycle_contained_fill_seed_iff hd J L hLdegree).mp hfinFilled
  obtain ⟨cOriginal⟩ := hfinOriginal
  let cInduced : Copy (cycleGraph (2 * d)) H :=
    (SimpleGraph.Iso.map e H).symm.toCopy.comp cOriginal
  let C : Copy (cycleGraph (2 * d)) G :=
    (Copy.induce G (A : Set V)).comp cInduced
  have hsurj : Function.Surjective cOriginal :=
    Finite.surjective_of_injective cOriginal.injective
  refine ⟨C, ?_⟩
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact (cInduced i).property
  · intro hv
    obtain ⟨i, hi⟩ := hsurj (e ⟨v, hv⟩)
    refine ⟨i, ?_⟩
    change (e.symm (cOriginal i)).val = v
    rw [hi, Equiv.symm_apply_apply]

/-- Literal ORIGINAL B internally constructs one kernel and its actual2d
prefix. In the explicit3≤h≤d branch it acquires an ORIGINAL spanning cycle
with exact support, without a supplied cycle, min-degree, prefix or fill oracle. -/
theorem exists_actual_kernel_with_original_prefix_cycle
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hd : 4 ≤ d) (hC : degreeCore G d = ∅)
    (hSlarge : 2 * d + 2 ≤ S.card)
    (hthreshold : (d - 1).choose 2 +
      (d - 1) * (S.card - d + 1) + 2 < (withinEdges G S).card) :
    ∃ K : Finset V, K ⊆ S ∧ d + 3 ≤ K.card ∧
      (∀ x ∈ K, d ≤ withinDegree G K x) ∧
      ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
        (∀ x ∈ W, d + 1 ≤ withinDegree G K x) ∧
        (K.card ≤ 2 * d → ∃ A D : Finset V, ∃ a b t c : ℕ,
          K ⊆ A ∧ A ⊆ D ∧ D ⊆ S ∧
          A.card = 2 * d ∧ D.card = 2 * d + 2 ∧
          RestorationTrace G d K A a ∧ RestorationTrace G d A D b ∧
          RestorationTrace G d D S t ∧ RestorationTrace G d K S c ∧
          c = a + b + t ∧
          (∀ U x, ActualRestorationStep G d K A a U x →
            d - (K.card - d) + 2 ≤ withinDegree G U x) ∧
          (∀ x ∈ W, d + 1 ≤ withinDegree G A x) ∧
          ∃ C : Copy (cycleGraph (2 * d)) G, Set.range C = (A : Set V)) := by
  obtain ⟨K, hKS, hKlarge, hKmin, W, hWK, hWcard, hWdegree, hbranch⟩ :=
    exists_actual_kernel_with_nested_prefix_guards G d S hd hC hSlarge hthreshold
  refine ⟨K, hKS, hKlarge, hKmin, W, hWK, hWcard, hWdegree, ?_⟩
  intro hKsmall
  obtain ⟨A, D, a, b, t, c, hKA, hAD, hDS, hAcard, hDcard,
    hprefixA, _hprefixD, hmiddle, hsuffixD, hwhole, hcharge,
    hstepsA, _hstepsD, hseed, hhighA, _hretainedA, _hretainedD⟩ := hbranch hKsmall
  have hfilled := actual_trace_has_exact_filled_cycle_copy G d K A a
    hprefixA hKlarge (by omega) hstepsA
  obtain ⟨C, hrange⟩ := original_cycle_copy_of_actual_seed_filling G d K A
    (by omega) hAcard hseed hfilled
  exact ⟨A, D, a, b, t, c, hKA, hAD, hDS, hAcard, hDcard,
    hprefixA, hmiddle, hsuffixD, hwhole, hcharge, hstepsA, hhighA, C, hrange⟩

end ErdosProblems.PathUpperReduction.ActualPrefixCycle1105
end

noncomputable section
namespace ErdosProblems.PathUpperReduction.ActualSuffixIndependence1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
open ErdosProblems.PathUpperReduction.TracePrefixSlack1105
open ErdosProblems.PathUpperReduction.ActualPrefixCarrierDegree1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-- The canonical cycle visits EVERY vertex. This is support fidelity for the
copy-to-walk direction; cycleGraph_isContained_iff alone exports only length. -/
theorem mem_support_canonical_cycle (n : ℕ) (i : Fin (n + 3)) :
    i ∈ (cycleGraph.cycle n).support := by
  classical
  let Q := cycleGraph.cycle n
  have hQ : Q.IsCycle := cycleGraph.isCycle_cycle
  have hlen : Q.support.dropLast.length = n + 3 := by
    have hs := Q.length_support
    have hc : Q.length = n + 3 := cycleGraph.length_cycle
    have hd := List.length_dropLast (xs := Q.support)
    omega
  have hcard : Q.support.dropLast.toFinset.card = n + 3 := by
    rw [List.toFinset_card_of_nodup hQ.nodup_dropLast_support, hlen]
  have hall : Q.support.dropLast.toFinset = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, Fintype.card_fin] using hcard.ge
  have hi : i ∈ Q.support.dropLast.toFinset := by rw [hall]; exact Finset.mem_univ i
  exact List.mem_of_mem_dropLast (List.mem_toFinset.mp hi)

omit [Fintype V] in
/-- An actual original cycle COPY gives an original cycle WALK with exactly
the same range/support. No filled graph, abstract cardinality or new vertices. -/
theorem exists_original_cycle_walk_of_copy (G : SimpleGraph V) (N : ℕ)
    (hN : 3 ≤ N) (C : (cycleGraph N).Copy G) :
    ∃ a : V, ∃ P : G.Walk a a, P.IsCycle ∧ P.length = N ∧
      ∀ v, v ∈ P.support ↔ v ∈ Set.range C := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 3 := ⟨N - 3, by omega⟩
  let Q := cycleGraph.cycle n
  let P := Q.map C.toHom
  refine ⟨C 0, P, cycleGraph.isCycle_cycle.map C.injective, ?_, ?_⟩
  · simpa only [P, Q, SimpleGraph.Walk.length_map] using
      (cycleGraph.length_cycle (n := n))
  · intro v
    change v ∈ (Q.map C.toHom).support ↔ v ∈ Set.range C
    rw [SimpleGraph.Walk.support_map]
    constructor
    · intro hv
      obtain ⟨i, _hi, hiv⟩ := List.mem_map.mp hv
      exact ⟨i, hiv⟩
    · rintro ⟨i, rfl⟩
      exact List.mem_map.mpr ⟨i, mem_support_canonical_cycle n i, rfl⟩

omit [Fintype V] in
/-- The precise falsifying path: two consecutive fresh outside vertices,
then all cycle vertices. It lies in the ORIGINAL induced graph G[S]. -/
theorem path_copy_in_induce_of_two_step_attachment (G : SimpleGraph V)
    (S : Finset V) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (x z v : V) (hx : x ∉ C.support) (hz : z ∉ C.support)
    (hv : v ∈ C.support) (hxz : G.Adj x z) (hzv : G.Adj z v)
    (hxS : x ∈ S) (hzS : z ∈ S)
    (hCS : ∀ w ∈ C.support, w ∈ S) :
    pathGraph (C.length + 2) ⊑ G.induce (S : Set V) := by
  classical
  let rot := C.rotate v hv
  have hrot : rot.IsCycle := hC.rotate hv
  have hdropSupport : ∀ w ∈ rot.dropLast.support, w ∈ C.support := by
    intro w hw
    rw [rot.support_dropLast hrot.not_nil] at hw
    exact (C.mem_support_rotate_iff v hv).mp (List.mem_of_mem_dropLast hw)
  have hzDrop : z ∉ rot.dropLast.support := fun h => hz (hdropSupport z h)
  have hxDrop : x ∉ rot.dropLast.support := fun h => hx (hdropSupport x h)
  let q1 := SimpleGraph.Walk.cons hzv rot.dropLast
  have hq1 : q1.IsPath := hrot.isPath_dropLast.cons hzDrop
  have hxQ1 : x ∉ q1.support := by
    intro h
    change x ∈ z :: rot.dropLast.support at h
    rcases List.mem_cons.mp h with h | h
    · exact hxz.ne h
    · exact hxDrop h
  let q2 := SimpleGraph.Walk.cons hxz q1
  have hq2 : q2.IsPath := hq1.cons hxQ1
  have hdrop : rot.dropLast.length + 1 = C.length := by
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = C.length := SimpleGraph.Walk.length_rotate C v hv
  have hlength : q2.length + 1 = C.length + 2 := by
    change (rot.dropLast.length + 1 + 1) + 1 = C.length + 2
    omega
  have hsupport : ∀ w ∈ q2.support, w ∈ (S : Set V) := by
    intro w hw
    change w ∈ x :: z :: rot.dropLast.support at hw
    rcases List.mem_cons.mp hw with hw | hw
    · rw [hw]; exact hxS
    · rcases List.mem_cons.mp hw with hw | hw
      · rw [hw]; exact hzS
      · exact hCS w (hdropSupport w hw)
  let qS := q2.induce (S : Set V) hsupport
  have hmap : qS.map (Embedding.induce (S : Set V)).toHom = q2 :=
    SimpleGraph.Walk.map_induce q2 hsupport
  have hmapped : (qS.map (Embedding.induce (S : Set V)).toHom).IsPath := by
    rw [hmap]
    exact hq2
  have hqS : qS.IsPath := hmapped.of_map
  have hlengthS : qS.length + 1 = C.length + 2 := by
    have hm : (qS.map (Embedding.induce (S : Set V)).toHom).length = q2.length :=
      congrArg SimpleGraph.Walk.length hmap
    rw [SimpleGraph.Walk.length_map] at hm
    omega
  have hcopy := hqS.pathGraphCopy
  rw [hlengthS] at hcopy
  exact ⟨hcopy⟩

/-- Prepend the SAME actual kernel-to-A prefix to a specified suffix
constructor. Its earlier support U and x are unchanged, and charges add. -/
theorem actual_step_prepend_prefix (G : SimpleGraph V) (d : ℕ)
    (K A S U : Finset V) (a b : ℕ) (x : V)
    (hprefix : RestorationTrace G d K A a)
    (hstep : ActualRestorationStep G d A S b U x) :
    ActualRestorationStep G d K S (a + b) U x := by
  obtain ⟨p, q, hlocalPrefix, hfresh, hlow, htail, hcharge⟩ := hstep
  refine ⟨a + p, q,
    restoration_trace_append G d K A U a p hprefix hlocalPrefix,
    hfresh, hlow, htail, ?_⟩
  omega

/-- Direct suffix induction. ALL bounds apply to the specified actual
constructor through prefix/suffix decomposition, never to an arbitrary order.
The cycle is original G and the forbidden path is restricted to original S. -/
theorem suffix_independent_of_original_cycle_and_actual_step_bounds
    (G : SimpleGraph V) (d : ℕ) (A S : Finset V) (b : ℕ)
    (htrace : RestorationTrace G d A S b)
    (hsteps : ∀ U x, ActualRestorationStep G d A S b U x →
      2 ≤ withinDegree G U x)
    (hfree : (pathGraph (2 * d + 2)).Free (G.induce (S : Set V)))
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hLength : C.length = 2 * d)
    (hSupport : ∀ v, v ∈ C.support ↔ v ∈ A) :
    (∀ x ∈ S, x ∉ A → ∀ y ∈ S, y ∉ A → ¬G.Adj x y) ∧
    (∀ x ∈ S, x ∉ A → 2 ≤ withinDegree G A x) := by
  classical
  have hAS : A ⊆ S := (restoration_trace_ledgers G d A S b htrace).1
  have hCS : ∀ v ∈ C.support, v ∈ S := fun v hv => hAS ((hSupport v).mp hv)
  have hInvariant : ∀ (T : Finset V) (q : ℕ),
      RestorationTrace G d A T q → T ⊆ S →
      (∀ U x, ActualRestorationStep G d A T q U x → 2 ≤ withinDegree G U x) →
      (∀ x ∈ T, x ∉ A → ∀ y ∈ T, y ∉ A → ¬G.Adj x y) ∧
      (∀ x ∈ T, x ∉ A → 2 ≤ withinDegree G A x) := by
    intro T q trace
    induction trace with
    | nil =>
        intro _ _
        constructor
        · intro x hx hxA
          exact False.elim (hxA hx)
        · intro x hx hxA
          exact False.elim (hxA hx)
    | @snoc T q trace x hfresh hlow ih =>
        intro hnewS hnewSteps
        have hTS : T ⊆ S := (Finset.subset_insert x T).trans hnewS
        have hAT : A ⊆ T := (restoration_trace_ledgers G d A T q trace).1
        have hprevSteps : ∀ U z, ActualRestorationStep G d A T q U z →
            2 ≤ withinDegree G U z := by
          intro U z hstep
          exact hnewSteps U z (actual_step_preserved_snoc G d A T U q z x
            hstep hfresh hlow)
        obtain ⟨hIndependent, hContacts⟩ := ih hTS hprevSteps
        have hxA : x ∉ A := fun hx => hfresh (hAT hx)
        have hxS : x ∈ S := hnewS (Finset.mem_insert_self x T)
        have hnewDegree : 2 ≤ withinDegree G T x :=
          hnewSteps T x (actual_step_last G d A T q trace x hfresh hlow)
        have hNoOutside : ∀ z ∈ T, z ∉ A → ¬G.Adj x z := by
          intro z hzT hzA hxz
          have hcontactDegree := hContacts z hzT hzA
          have hcontactPositive : 0 < (A.filter (fun v => G.Adj z v)).card := by
            change 0 < withinDegree G A z
            omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hcontactPositive
          obtain ⟨hvA, hzv⟩ := Finset.mem_filter.mp hv
          have hxCycle : x ∉ C.support := fun hx => hxA ((hSupport x).mp hx)
          have hzCycle : z ∉ C.support := fun hz => hzA ((hSupport z).mp hz)
          have hcopy := path_copy_in_induce_of_two_step_attachment G S C hC
            x z v hxCycle hzCycle ((hSupport v).mpr hvA) hxz hzv hxS
            (hTS hzT) hCS
          rw [hLength] at hcopy
          exact hfree hcopy
        have hfilter : T.filter (fun v => G.Adj x v) =
            A.filter (fun v => G.Adj x v) := by
          ext v
          constructor
          · intro hv
            obtain ⟨hvT, hxv⟩ := Finset.mem_filter.mp hv
            have hvA : v ∈ A := by
              by_contra hvA
              exact hNoOutside v hvT hvA hxv
            exact Finset.mem_filter.mpr ⟨hvA, hxv⟩
          · intro hv
            obtain ⟨hvA, hxv⟩ := Finset.mem_filter.mp hv
            exact Finset.mem_filter.mpr ⟨hAT hvA, hxv⟩
        have hnewContact : 2 ≤ withinDegree G A x := by
          have hdeg : withinDegree G T x = withinDegree G A x :=
            congrArg Finset.card hfilter
          omega
        constructor
        · intro u hu huA v hv hvA huv
          rcases Finset.mem_insert.mp hu with hux | huT
          · subst u
            rcases Finset.mem_insert.mp hv with hvx | hvT
            · subst v
              exact G.irrefl huv
            · exact hNoOutside v hvT hvA huv
          · rcases Finset.mem_insert.mp hv with hvx | hvT
            · subst v
              exact hNoOutside u huT huA huv.symm
            · exact hIndependent u huT huA v hvT hvA huv
        · intro z hz hzA
          rcases Finset.mem_insert.mp hz with hzx | hzT
          · subst z
            exact hnewContact
          · exact hContacts z hzT hzA
  exact hInvariant S b htrace (fun _ hx => hx) hsteps

/-- SAME kernel coupling: the original-threshold caller's ALL additive bound
and smaller-seed branch derive all suffix degrees >=2 internally. The cycle
premise is the precise separate original-cycle acquisition obligation. -/
theorem suffix_independent_of_same_kernel_prefix_and_original_cycle
    (G : SimpleGraph V) (d : ℕ) (K A S : Finset V) (a b c : ℕ)
    (hprefix : RestorationTrace G d K A a)
    (hsuffix : RestorationTrace G d A S b) (hcharge : c = a + b)
    (hKsmall : K.card ≤ 2 * d)
    (hsteps : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free (G.induce (S : Set V)))
    {v : V} (C : G.Walk v v) (hC : C.IsCycle)
    (hLength : C.length = 2 * d)
    (hSupport : ∀ x, x ∈ C.support ↔ x ∈ A) :
    (∀ x ∈ S, x ∉ A → ∀ y ∈ S, y ∉ A → ¬G.Adj x y) ∧
    (∀ x ∈ S, x ∉ A → 2 ≤ withinDegree G A x) := by
  have hsmall : K.card - d ≤ d := by omega
  have hsuffixSteps : ∀ U x, ActualRestorationStep G d A S b U x →
      2 ≤ withinDegree G U x := by
    intro U x hstep
    have hfull := actual_step_prepend_prefix G d K A S U a b x hprefix hstep
    have hfullC : ActualRestorationStep G d K S c U x := by
      rw [hcharge]
      exact hfull
    have hguard := hsteps U x hfullC
    omega
  exact suffix_independent_of_original_cycle_and_actual_step_bounds G d A S b
    hsuffix hsuffixSteps hfree C hC hLength hSupport

/-- Consumer matching the actual-cycle author's output: ORIGINAL copy range
is exactly A, with the SAME kernel/prefix/suffix/charge and original G[S]. -/
theorem suffix_independent_of_same_kernel_prefix_and_original_cycle_copy
    (G : SimpleGraph V) (d : ℕ) (K A S : Finset V) (a b c : ℕ)
    (hd : 2 ≤ d) (hprefix : RestorationTrace G d K A a)
    (hsuffix : RestorationTrace G d A S b) (hcharge : c = a + b)
    (hKsmall : K.card ≤ 2 * d)
    (hsteps : ∀ U x, ActualRestorationStep G d K S c U x →
      d + 2 ≤ withinDegree G U x + (K.card - d))
    (hfree : (pathGraph (2 * d + 2)).Free (G.induce (S : Set V)))
    (C : (cycleGraph (2 * d)).Copy G)
    (hRange : Set.range C = (A : Set V)) :
    (∀ x ∈ S, x ∉ A → ∀ y ∈ S, y ∉ A → ¬G.Adj x y) ∧
    (∀ x ∈ S, x ∉ A → 2 ≤ withinDegree G A x) := by
  have hN : 3 ≤ 2 * d := by omega
  obtain ⟨v, P, hP, hLength, hSupport⟩ :=
    exists_original_cycle_walk_of_copy G (2 * d) hN C
  have hA : ∀ x, x ∈ P.support ↔ x ∈ A := by
    intro x
    rw [hSupport x, hRange]
    rfl
  exact suffix_independent_of_same_kernel_prefix_and_original_cycle
    G d K A S a b c hprefix hsuffix hcharge hKsmall hsteps hfree
    P hP hLength hA

omit [Fintype V] in
/-- The resulting ORIGINAL neighbor filter is retained on EVERY nested
carrier D. This equality follows from independence, rather than cardinality. -/
theorem neighbor_filter_eq_of_suffix_independent (G : SimpleGraph V)
    (A D S : Finset V) (hAD : A ⊆ D) (hDS : D ⊆ S)
    (hIndependent : ∀ x ∈ S, x ∉ A → ∀ y ∈ S, y ∉ A → ¬G.Adj x y)
    (x : V) (hxS : x ∈ S) (hxA : x ∉ A) :
    D.filter (fun y => G.Adj x y) = A.filter (fun y => G.Adj x y) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyD, hxy⟩ := Finset.mem_filter.mp hy
    have hyA : y ∈ A := by
      by_contra hyA
      exact hIndependent x hxS hxA y (hDS hyD) hyA hxy
    exact Finset.mem_filter.mpr ⟨hyA, hxy⟩
  · intro hy
    obtain ⟨hyA, hxy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hAD hyA, hxy⟩

end ErdosProblems.PathUpperReduction.ActualSuffixIndependence1105
end

namespace ErdosProblems.PathHighNewStageTwo

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion
open ErdosProblems.PathHighNewStageOne

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem component_hamiltonian_cycle_selected_path
    (G : SimpleGraph (Fin n)) (D : G.ConnectedComponent)
    (u : D) (c : D.toSimpleGraph.Walk u u) (hc : c.IsHamiltonianCycle) :
    ∃ f : (pathGraph D.supp.ncard).Copy G, ∀ i, f i ∈ D.supp := by
  classical
  let : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have horder : c.dropLast.length + 1 = D.supp.ncard := by
    calc
      c.dropLast.length + 1 = c.length :=
        Walk.length_dropLast_add_one hc.isCycle.not_nil
      _ = Fintype.card D := hc.length_eq
      _ = D.supp.ncard := hcard
  let p : (pathGraph D.supp.ncard).Copy D.toSimpleGraph :=
    horder ▸ hc.isCycle.isPath_dropLast.pathGraphCopy
  refine ⟨(Copy.induce G D.supp).comp p, ?_⟩
  intro i
  exact (p i).property

theorem selected_edge_color_mem_new_union
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : (selectedGraph χ r).edgeSet) :
    restrictedColor χ r e ∈ newColorUnion χ := by
  have hm : e.val ∈ Set.range fun c : newColorUnion χ => (r.edge c).val := by
    rw [← selectedGraph_edgeSet χ r]
    exact e.property
  obtain ⟨c, hc⟩ := hm
  have he : (⟨e.val, edgeSet_mono le_top e.property⟩ : HostEdge n) = r.edge c :=
    Subtype.ext hc.symm
  change χ ⟨e.val, edgeSet_mono le_top e.property⟩ ∈ newColorUnion χ
  rw [he, r.color_eq]
  exact c.property

theorem host_color_of_selected_copy
    {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (f : H.Copy (selectedGraph χ r)) (e : H.edgeSet) :
    χ (((Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom.mapEdgeSet e) =
      restrictedColor χ r (f.mapEdgeSet e) := by
  exact congrArg χ (Subtype.ext rfl)

theorem selected_component_path_palettes_disjoint
    {a b : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (D E : (selectedGraph χ r).ConnectedComponent) (hDE : D ≠ E)
    (A : (pathGraph a).Copy (selectedGraph χ r))
    (B : (pathGraph b).Copy (selectedGraph χ r))
    (hA : ∀ i, A i ∈ D.supp) (hB : ∀ j, B j ∈ E.supp) :
    ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      restrictedColor χ r (A.mapEdgeSet e) ≠
        restrictedColor χ r (B.mapEdgeSet d) := by
  intro e d heq
  have hdis := (selectedGraph χ r).pairwise_disjoint_supp_connectedComponent hDE
  have hedges := congrArg
    (fun q : (selectedGraph χ r).edgeSet => q.val)
    (restrictedColor_injective χ r heq)
  obtain ⟨⟨i, j⟩, hij⟩ := Sym2.mk_surjective e.val
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective d.val
  change Sym2.map A e.val = Sym2.map B d.val at hedges
  rw [← hij, ← huv] at hedges
  change s(A i, A j) = s(B u, B v) at hedges
  rcases Sym2.eq_iff.mp hedges with h | h
  · have hboth : A i ∈ E.supp := h.1.symm ▸ hB u
    exact Set.disjoint_left.mp hdis (hA i) hboth
  · have hboth : A i ∈ E.supp := h.1.symm ▸ hB v
    exact Set.disjoint_left.mp hdis (hA i) hboth

def path_prefix_copy {a b : ℕ} (hab : a ≤ b) :
    (pathGraph a).Copy (pathGraph b) where
  toHom :=
    { toFun := Fin.castLE hab
      map_rel' := by
        intro i j hij
        apply pathGraph_adj.mpr
        simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
  injective' := Fin.castLE_injective hab

omit [DecidableEq C] in
theorem rainbow_copy_comp
    {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (χ : TopEdgeLabeling (Fin n) C)
    (f : A.Copy B) (g : B.Copy (⊤ : SimpleGraph (Fin n)))
    (hg : IsRainbow g.toHom χ) :
    IsRainbow (g.comp f).toHom χ := by
  have hmap (e : A.edgeSet) :
      (g.comp f).toHom.mapEdgeSet e =
        g.toHom.mapEdgeSet (f.toHom.mapEdgeSet e) := by
    apply Subtype.ext
    simpa only [Copy.comp, Hom.mapEdgeSet, Hom.coe_comp] using
      (Sym2.map_map (f := f.toHom) (g := g.toHom) e.val).symm
  intro e d heq
  apply Hom.mapEdgeSet.injective f.toHom f.injective
  apply hg
  simpa only [EdgeLabeling.pullback_apply, hmap] using heq

/-- Every-vertex high NEW and the literal odd-cycle exclusion force an
original rainbow even path. All component bounds, paths and palette
conditions used below are derived for the same canonical NEW choice. -/
theorem rainbow_even_path_of_high_new_and_no_odd_cycle
    {ell : ℕ} (χ : TopEdgeLabeling (Fin n) C)
    (hell : 2 ≤ ell) (hn : 2 * ell + 2 ≤ n)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card)
    (hno : ∀ f : (cycleGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    ∃ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  let r : NewChoice χ := canonicalChoice χ
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  have hk : 5 ≤ 2 * ell + 1 := by omega
  have hnew2 : ∀ v : Fin n, 2 ≤ (newColors χ v).card := by
    intro v
    exact hell.trans (hnew v)
  have hpair : ∀ u v : Fin n, u ≠ v →
      (2 * ell + 1) - 1 ≤ (newColors χ u).card + (newColors χ v).card := by
    intro u v _
    have hu := hnew u
    have hv := hnew v
    omega
  let v0 : Fin n := ⟨0, by omega⟩
  let D : G.ConnectedComponent := G.connectedComponentMk v0
  obtain ⟨hD3, hDlow, hDup, _, hDHam⟩ :=
    selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew2 hpair hno D
  have houtside : ∃ w : Fin n, w ∉ D.supp := by
    by_contra! hfull
    have hset : D.supp = Set.univ := Set.eq_univ_of_forall hfull
    have hcard : D.supp.ncard = n := by simp only [hset, Set.ncard_univ, Nat.card_fin]
    omega
  obtain ⟨w, hw⟩ := houtside
  let E : G.ConnectedComponent := G.connectedComponentMk w
  have hwE : w ∈ E.supp := ConnectedComponent.connectedComponentMk_mem
  have hDE : D ≠ E := by
    intro h
    exact hw (h.symm ▸ hwE)
  obtain ⟨hE3, hElow, _, _, hEHam⟩ :=
    selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew2 hpair hno E
  obtain ⟨uD, cD, hcD⟩ := hDHam
  obtain ⟨uE, cE, hcE⟩ := hEHam
  obtain ⟨fD, hfD⟩ := component_hamiltonian_cycle_selected_path G D uD cD hcD
  obtain ⟨fE, hfE⟩ := component_hamiltonian_cycle_selected_path G E uE cE hcE
  let A : (pathGraph D.supp.ncard).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fD
  let B : (pathGraph E.supp.ncard).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fE
  have hArainbow : IsRainbow A.toHom χ := copy_in_selectedGraph_isRainbow χ r fD
  have hBrainbow : IsRainbow B.toHom χ := copy_in_selectedGraph_isRainbow χ r fE
  have hAmem (i : Fin D.supp.ncard) : A i ∈ D.supp := hfD i
  have hBmem (j : Fin E.supp.ncard) : B j ∈ E.supp := hfE j
  have hdis := G.pairwise_disjoint_supp_connectedComponent hDE
  have hArange : Set.range (fun i : Fin D.supp.ncard => A i) ⊆ D.supp := by
    rintro x ⟨i, rfl⟩
    exact hAmem i
  have hBrange : Set.range (fun j : Fin E.supp.ncard => B j) ⊆ E.supp := by
    rintro x ⟨j, rfl⟩
    exact hBmem j
  have hpathsDis := hdis.mono hArange hBrange
  have hpalette : ∀ e : (pathGraph D.supp.ncard).edgeSet,
      ∀ d : (pathGraph E.supp.ncard).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ (B.toHom.mapEdgeSet d) := by
    intro e d
    change χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fD).toHom.mapEdgeSet e) ≠
      χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fE).toHom.mapEdgeSet d)
    rw [host_color_of_selected_copy χ r fD e, host_color_of_selected_copy χ r fE d]
    exact selected_component_path_palettes_disjoint χ r D E hDE fD fE hfD hfE e d
  have hDa : 1 ≤ D.supp.ncard := by omega
  have hEb : 1 ≤ E.supp.ncard := by omega
  let u : Fin n := A ⟨D.supp.ncard - 1, by omega⟩
  let v : Fin n := B ⟨0, by omega⟩
  have hu : u ∈ D.supp := hAmem _
  have hv : v ∈ E.supp := hBmem _
  have huv : u ≠ v := by
    intro h
    exact Set.disjoint_left.mp hdis hu (h.symm ▸ hv)
  let join : HostEdge n := ⟨s(u, v), by exact (⊤ : SimpleGraph (Fin n)).mem_edgeSet.mpr ((top_adj u v).mpr huv)⟩
  have hjcolor : χ join ∉ newColorUnion χ :=
    cross_edge_color_not_new_union hk χ r hnew2 hpair hno D E hDE u v hu hv join rfl
  have hfreshA : ∀ e : (pathGraph D.supp.ncard).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ join := by
    intro e heq
    apply hjcolor
    rw [← heq]
    change χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fD).toHom.mapEdgeSet e) ∈ _
    rw [host_color_of_selected_copy χ r fD e]
    exact selected_edge_color_mem_new_union χ r (fD.mapEdgeSet e)
  have hfreshB : ∀ d : (pathGraph E.supp.ncard).edgeSet,
      χ (B.toHom.mapEdgeSet d) ≠ χ join := by
    intro d heq
    apply hjcolor
    rw [← heq]
    change χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fE).toHom.mapEdgeSet d) ∈ _
    rw [host_color_of_selected_copy χ r fE d]
    exact selected_edge_color_mem_new_union χ r (fE.mapEdgeSet d)
  obtain ⟨f, hf, _, _⟩ :=
    rainbow_path_of_original_disjoint_paths_and_fresh_join hDa hEb χ A B
      hArainbow hBrainbow hpathsDis hpalette join rfl hfreshA hfreshB
  have hsum : 2 * ell + 2 ≤ D.supp.ncard + E.supp.ncard := by omega
  exact ⟨f.comp (path_prefix_copy hsum), rainbow_copy_comp χ (path_prefix_copy hsum) f hf⟩

end ErdosProblems.PathHighNewStageTwo

namespace ErdosProblems.PathHighNew

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Every original NEW-color set has at least ell colors, so the original
complete-host coloring has a rainbow path on 2 * ell + 2 vertices. -/
theorem exists_rainbow_even_path_of_high_new {ell : ℕ}
    (hell : 2 ≤ ell) (hn : 2 * ell + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card) :
    ∃ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  classical
  by_contra h
  have hnoP :
      ∀ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
        ¬ IsRainbow p.toHom χ := by
    intro p hp
    exact h ⟨p, hp⟩
  have hnoC :=
    ErdosProblems.PathHighNewStageOne.no_rainbow_odd_cycle_of_high_new_and_no_even_path
      hell hn χ hnew hnoP
  exact h
    (ErdosProblems.PathHighNewStageTwo.rainbow_even_path_of_high_new_and_no_odd_cycle
      χ hell hn hnew hnoC)

end ErdosProblems.PathHighNew

namespace ErdosProblems.PathSpanningNonedgeDeficit

open SimpleGraph Finset

noncomputable instance neighbor_fintype {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) : Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

/-- Add precisely the one unordered pair; copies remain non-induced. -/
def augment {k : ℕ} (G : SimpleGraph (Fin k)) (u v : Fin k) :
    SimpleGraph (Fin k) := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}

/-- The one-apex cone, with all old edges unchanged. -/
def cone {k : ℕ} (G : SimpleGraph (Fin k)) : SimpleGraph (Option (Fin k)) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a
    · exact id
    · exact G.loopless.irrefl _⟩

theorem cone_degree_some {k : ℕ} (G : SimpleGraph (Fin k))
    (u : Fin k) : (cone G).degree (some u) = G.degree u + 1 := by
  classical
  have hset : (cone G).neighborFinset (some u) =
      insert none ((G.neighborFinset u).image some) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    cases w <;> simp [SimpleGraph.mem_neighborFinset, cone]
  change ((cone G).neighborFinset (some u)).card = G.degree u + 1
  rw [hset]
  calc
    _ = ((G.neighborFinset u).image some).card + 1 :=
      Finset.card_insert_of_notMem (by simp)
    _ = G.degree u + 1 := congrArg (fun t : ℕ => t + 1)
      (Finset.card_image_of_injective _ (Option.some_injective _))

/-- Deleting the unique apex from a spanning ordinary cycle produces an
ordinary spanning path, by the literal cyclic rotation after that apex. -/
theorem cone_cycle_free_of_path_free {k : ℕ}
    (G : SimpleGraph (Fin k)) (hfree : (pathGraph k).Free G) :
    (cycleGraph (k + 1)).Free (cone G) := by
  classical
  intro hcopy
  obtain ⟨f⟩ := hcopy
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp⟩
  obtain ⟨j, hj⟩ := hbij.2 none
  let q : Fin k → Fin (k + 1) := fun i => j + Fin.succ i
  have hq : Function.Injective q := by
    intro a b h
    apply Fin.succ_injective k
    exact add_left_cancel h
  have hsome (i : Fin k) : ∃ v : Fin k, f (q i) = some v := by
    cases he : f (q i) with
    | none =>
        have hi : q i = j := f.injective (he.trans hj.symm)
        have hz : Fin.succ i = (0 : Fin (k + 1)) := by
          apply add_left_cancel (a := j)
          simpa only [q, add_zero] using hi
        exact (Fin.succ_ne_zero i hz).elim
    | some v => exact ⟨v, rfl⟩
  let p : Fin k → Fin k := fun i => Classical.choose (hsome i)
  have hp_eq (i : Fin k) : f (q i) = some (p i) :=
    Classical.choose_spec (hsome i)
  have hp : Function.Injective p := by
    intro a b h
    apply hq
    apply f.injective
    change f (q a) = f (q b)
    rw [hp_eq a, hp_eq b, h]
  have hstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      G.Adj (p a) (p b) := by
    have hle : Fin.succ a ≤ Fin.succ b := by
      simpa only [Fin.le_iff_val_le_val, Fin.val_succ] using (by omega :
        a.val + 1 ≤ b.val + 1)
    have hsub : ((Fin.succ b : Fin (k + 1)) - Fin.succ a).val = 1 := by
      rw [Fin.sub_val_of_le hle]
      simp only [Fin.val_succ]
      omega
    have hrot : (q b - q a).val = 1 := by
      have heq : q b - q a = Fin.succ b - Fin.succ a := by
        dsimp [q]
        abel
      rw [heq]
      exact hsub
    have hc : (cycleGraph (k + 1)).Adj (q a) (q b) :=
      cycleGraph_adj'.mpr (Or.inr hrot)
    have hm := f.toHom.map_adj hc
    change (cone G).Adj (f (q a)) (f (q b)) at hm
    rw [hp_eq a, hp_eq b] at hm
    exact hm
  let φ : (pathGraph k) →g G := ⟨p, by
    intro a b hab
    rcases pathGraph_adj.mp hab with h | h
    · exact hstep h
    · exact (hstep h).symm⟩
  exact hfree ⟨φ.toCopy hp⟩

/-- An ordinary augmented spanning path must contain the added pair, at a
literal consecutive position. No favorable orientation is assumed. -/
theorem added_pair_occurs {k : ℕ} (G : SimpleGraph (Fin k))
    (hfree : (pathGraph k).Free G) (u v : Fin k)
    (p : (pathGraph k).Copy (augment G u v)) :
    ∃ j : Fin k, ∃ hj : j.val + 1 < k,
      s(p j, p ⟨j.val + 1, hj⟩) = s(u, v) := by
  classical
  have hex : ∃ a b : Fin k, (pathGraph k).Adj a b ∧
      ¬ G.Adj (p a) (p b) := by
    by_contra! h
    let φ : (pathGraph k) →g G := ⟨p, by
      intro a b hab
      exact h a b hab⟩
    exact hfree ⟨φ.toCopy p.injective⟩
  obtain ⟨a, b, hab, hnot⟩ := hex
  have hnew : s(p a, p b) = s(u, v) := by
    have hm := p.toHom.map_adj hab
    change (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj (p a) (p b) at hm
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hm with h | h
    · exact (hnot h).elim
    · exact Set.mem_singleton_iff.mp ((SimpleGraph.fromEdgeSet_adj _).mp h).1
  rcases pathGraph_adj.mp hab with hab | hba
  · have hj : a.val + 1 < k := by omega
    have hn : (⟨a.val + 1, hj⟩ : Fin k) = b := Fin.ext hab
    exact ⟨a, hj, by simpa only [hn] using hnew⟩
  · have hj : b.val + 1 < k := by omega
    have hn : (⟨b.val + 1, hj⟩ : Fin k) = a := Fin.ext hba
    refine ⟨b, hj, ?_⟩
    rw [hn]
    exact Sym2.eq_swap.trans hnew

def splitOrder {k : ℕ} (p : Fin k → Fin k)
    (j : Fin k) (hj : j.val + 1 < k) (i : Fin (k + 1)) : Option (Fin k) :=
  if h : i.val ≤ j.val then
    some (p ⟨j.val - i.val,
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_succ_lt hj)⟩)
  else if h' : i.val = j.val + 1 then none
  else some (p ⟨k + j.val + 1 - i.val, by omega⟩)

theorem splitOrder_injective {k : ℕ} (p : Fin k → Fin k)
    (hp : Function.Injective p) (j : Fin k) (hj : j.val + 1 < k) :
    Function.Injective (splitOrder p j hj) := by
  intro a b hab
  by_cases ha : a.val ≤ j.val
  · by_cases hb : b.val ≤ j.val
    · simp only [splitOrder, dite_eq_left ha, dite_eq_left hb] at hab
      have hv := congrArg Fin.val (hp (Option.some.inj hab))
      dsimp at hv
      apply Fin.ext
      omega
    · by_cases hb' : b.val = j.val + 1
      · simp only [splitOrder, dite_eq_left ha, dite_eq_right hb, dite_eq_left hb'] at hab
        cases hab
      · simp only [splitOrder, dite_eq_left ha, dite_eq_right hb, dite_eq_right hb'] at hab
        have hv := congrArg Fin.val (hp (Option.some.inj hab))
        dsimp at hv
        have hblt := b.isLt
        omega
  · by_cases ha' : a.val = j.val + 1
    · by_cases hb : b.val ≤ j.val
      · simp only [splitOrder, dite_eq_right ha, dite_eq_left ha', dite_eq_left hb] at hab
        cases hab
      · by_cases hb' : b.val = j.val + 1
        · apply Fin.ext
          omega
        · simp only [splitOrder, dite_eq_right ha, dite_eq_left ha', dite_eq_right hb,
            dite_eq_right hb'] at hab
          cases hab
    · by_cases hb : b.val ≤ j.val
      · simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_left hb] at hab
        have hv := congrArg Fin.val (hp (Option.some.inj hab))
        dsimp at hv
        have halt := a.isLt
        omega
      · by_cases hb' : b.val = j.val + 1
        · simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_right hb,
            dite_eq_left hb'] at hab
          cases hab
        · simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_right hb,
            dite_eq_right hb'] at hab
          have hv := congrArg Fin.val (hp (Option.some.inj hab))
          dsimp at hv
          have halt := a.isLt
          have hblt := b.isLt
          apply Fin.ext
          omega

theorem splitOrder_zero {k : ℕ} (p : Fin k → Fin k)
    (j : Fin k) (hj : j.val + 1 < k) :
    splitOrder p j hj 0 = some (p j) := by
  simp [splitOrder]

theorem splitOrder_last {k : ℕ} (p : Fin k → Fin k)
    (j : Fin k) (hj : j.val + 1 < k) :
    splitOrder p j hj (Fin.last k) = some (p ⟨j.val + 1, hj⟩) := by
  have h1 : ¬ (Fin.last k).val ≤ j.val := by simp only [Fin.val_last]; omega
  have h2 : ¬ (Fin.last k).val = j.val + 1 := by simp only [Fin.val_last]; omega
  simp only [splitOrder, dite_eq_right h1, dite_eq_right h2]
  congr 2
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- The split order uses the reversed prefix, the single apex, then the
reversed suffix. Every old edge avoids the unique removed added pair. -/
theorem splitOrder_path {k : ℕ} (G : SimpleGraph (Fin k))
    (u v : Fin k) (p : (pathGraph k).Copy (augment G u v))
    (j : Fin k) (hj : j.val + 1 < k)
    (hpair : s(p j, p ⟨j.val + 1, hj⟩) = s(u, v)) :
    ∀ a b : Fin (k + 1), a.val + 1 = b.val →
      (cone G).Adj (splitOrder p j hj a) (splitOrder p j hj b) := by
  have hnormal (a b : Fin k) (hab : (pathGraph k).Adj a b)
      (hne : s(a, b) ≠ s(j, ⟨j.val + 1, hj⟩)) : G.Adj (p a) (p b) := by
    have hm := p.toHom.map_adj hab
    change (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj (p a) (p b) at hm
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hm with h | h
    · exact h
    · have he := Set.mem_singleton_iff.mp ((SimpleGraph.fromEdgeSet_adj _).mp h).1
      rw [← hpair] at he
      apply False.elim
      apply hne
      rcases Sym2.eq_iff.mp he with h | h
      · exact Sym2.eq_iff.mpr (Or.inl ⟨p.injective h.1, p.injective h.2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨p.injective h.1, p.injective h.2⟩)
  intro a b hab
  by_cases ha : a.val ≤ j.val
  · by_cases hb : b.val ≤ j.val
    · simp only [splitOrder, dite_eq_left ha, dite_eq_left hb, cone]
      apply hnormal
      · apply pathGraph_adj.mpr
        right
        dsimp
        omega
      · intro he
        rcases Sym2.eq_iff.mp he with h | h
        · have hv := congrArg Fin.val h.2
          dsimp at hv
          omega
        · have hv := congrArg Fin.val h.1
          dsimp at hv
          omega
    · have hb' : b.val = j.val + 1 := by omega
      simp only [splitOrder, dite_eq_left ha, dite_eq_right hb, dite_eq_left hb', cone]
  · by_cases ha' : a.val = j.val + 1
    · have hb : ¬ b.val ≤ j.val := by omega
      have hb' : ¬ b.val = j.val + 1 := by omega
      simp only [splitOrder, dite_eq_right ha, dite_eq_left ha', dite_eq_right hb,
        dite_eq_right hb', cone]
    · have hb : ¬ b.val ≤ j.val := by omega
      have hb' : ¬ b.val = j.val + 1 := by omega
      simp only [splitOrder, dite_eq_right ha, dite_eq_right ha', dite_eq_right hb,
        dite_eq_right hb', cone]
      apply hnormal
      · apply pathGraph_adj.mpr
        right
        dsimp
        have halt := a.isLt
        have hblt := b.isLt
        omega
      · intro he
        rcases Sym2.eq_iff.mp he with h | h
        · have hv := congrArg Fin.val h.1
          dsimp at hv
          have halt := a.isLt
          omega
        · have hv := congrArg Fin.val h.2
          dsimp at hv
          have hblt := b.isLt
          omega

/-- Spanning non-induced path augmentation at one missing unordered pair
forces the ordinary endpoint degree deficit. The literal pair premises are
retained; the Copy and Free hypotheses themselves force its actual use. -/
theorem degree_sum_le_of_spanning_path_augmentation {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin k)) (hfree : (pathGraph k).Free G)
    (u v : Fin k) (_huv : u ≠ v) (_hmissing : ¬ G.Adj u v)
    (hcopy : Nonempty ((pathGraph k).Copy (augment G u v))) :
    G.degree u + G.degree v ≤ k - 2 := by
  classical
  obtain ⟨p⟩ := hcopy
  obtain ⟨j, hj, hpair⟩ := added_pair_occurs G hfree u v p
  let q := splitOrder p j hj
  have hq : Function.Injective q := splitOrder_injective p p.injective j hj
  have hbij : Function.Bijective q :=
    (Fintype.bijective_iff_injective_and_card q).mpr ⟨hq, by simp⟩
  let e : Fin (k + 1) ≃ Option (Fin k) := Equiv.ofBijective q hbij
  let K : SimpleGraph (Fin (k + 1)) := (cone G).comap e
  have hKfree : (cycleGraph (k + 1)).Free K := by
    intro hc
    obtain ⟨f⟩ := hc
    exact cone_cycle_free_of_path_free G hfree
      ⟨(SimpleGraph.Iso.comap e (cone G)).toCopy.comp f⟩
  have hpath : ∀ a b : Fin (k + 1), a.val + 1 = b.val → K.Adj a b := by
    intro a b hab
    exact splitOrder_path G u v p j hj hpair a b hab
  have hbound := ErdosProblems.AntiRamseyCyclePathOre.path_endpoint_degree_sum_lt
    (by omega : 2 ≤ k) K hpath hKfree
  have hdeg0 := (SimpleGraph.Iso.comap e (cone G)).degree_eq (0 : Fin (k + 1))
  have hdeglast := (SimpleGraph.Iso.comap e (cone G)).degree_eq (Fin.last k)
  change (cone G).degree (q 0) = K.degree 0 at hdeg0
  change (cone G).degree (q (Fin.last k)) = K.degree (Fin.last k) at hdeglast
  rw [← hdeg0, ← hdeglast] at hbound
  change (cone G).degree (splitOrder p j hj 0) +
    (cone G).degree (splitOrder p j hj (Fin.last k)) < k + 1 at hbound
  rw [splitOrder_zero, splitOrder_last, cone_degree_some, cone_degree_some] at hbound
  have hpair' : (p j = u ∧ p ⟨j.val + 1, hj⟩ = v) ∨
      (p j = v ∧ p ⟨j.val + 1, hj⟩ = u) := Sym2.eq_iff.mp hpair
  have hD : G.degree (p j) + G.degree (p ⟨j.val + 1, hj⟩) ≤ k - 2 := by omega
  rcases hpair' with h | h
  · rw [h.1, h.2] at hD
    exact hD
  · rw [h.1, h.2] at hD
    simpa only [Nat.add_comm] using hD

end ErdosProblems.PathSpanningNonedgeDeficit

namespace ErdosProblems.PathDegreeClosedSupergraph

open SimpleGraph

/-- A supplied ordinary spanning-path-free graph extends on the same carrier
to a path-free graph whose every missing distinct pair has endpoint degree
sum at most k-2. No connectedness or coloring assumption is imposed. -/
theorem exists_degree_closed_path_free_supergraph {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin k)) (hfree : (pathGraph k).Free G) :
    ∃ H : SimpleGraph (Fin k), G ≤ H ∧ (pathGraph k).Free H ∧
      ∀ x y : Fin k, x ≠ y → ¬ H.Adj x y →
        H.degree x + H.degree y ≤ k - 2 := by
  classical
  obtain ⟨H, hGH, hHfree, hsat⟩ :=
    ErdosProblems.PathUpperReduction.exists_saturated_free_supergraph
      (pathGraph k) G hfree
  refine ⟨H, hGH, hHfree, ?_⟩
  intro x y hxy hmissing
  exact ErdosProblems.PathSpanningNonedgeDeficit.degree_sum_le_of_spanning_path_augmentation
    hk H hHfree x y hxy hmissing (hsat x y hxy hmissing)

end ErdosProblems.PathDegreeClosedSupergraph

namespace ErdosProblems.PathHighNewOdd

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree

variable {C : Type*} [DecidableEq C]

theorem rainbow_odd_path_on_spanning_carrier {ell : ℕ}
    (hell : 2 ≤ ell)
    (χ : TopEdgeLabeling (Fin (2 * ell + 1)) C)
    (hnew : ∀ v : Fin (2 * ell + 1), ell ≤ (newColors χ v).card) :
    ∃ p : (pathGraph (2 * ell + 1)).Copy
        (⊤ : SimpleGraph (Fin (2 * ell + 1))),
      IsRainbow p.toHom χ := by
  classical
  by_contra h
  have hno : ∀ p : (pathGraph (2 * ell + 1)).Copy
      (⊤ : SimpleGraph (Fin (2 * ell + 1))), ¬ IsRainbow p.toHom χ := by
    intro p hp
    exact h ⟨p, hp⟩
  let r : NewChoice χ := canonicalChoice χ
  let G : SimpleGraph (Fin (2 * ell + 1)) := selectedGraph χ r
  have hfree : (pathGraph (2 * ell + 1)).Free G :=
    selectedGraph_free (pathGraph (2 * ell + 1)) χ r hno
  obtain ⟨H, hGH, hHfree, hmissing⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by omega) G hfree
  have hdegree : ∀ v : Fin (2 * ell + 1), ell ≤ H.degree v := by
    intro v
    exact (hnew v).trans
      ((newChoice_degree_ge_newColors χ r v).trans (G.degree_le_of_le hGH))
  have htop : H = ⊤ := by
    apply le_antisymm le_top
    intro x y hxy
    by_contra hnonadj
    have hne : x ≠ y := (top_adj x y).mp hxy
    have hsum := hmissing x y hne hnonadj
    have hx := hdegree x
    have hy := hdegree y
    omega
  have hcopy : Nonempty ((pathGraph (2 * ell + 1)).Copy H) := by
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph (2 * ell + 1))
      (⊤ : SimpleGraph (Fin (2 * ell + 1))) le_top⟩
  exact hHfree hcopy

/-- Every original NEW-color set has at least ell colors, so the original
complete-host coloring has a rainbow path on 2 * ell + 1 vertices. -/
theorem exists_rainbow_odd_path_of_high_new {ell n : ℕ}
    (hell : 2 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card) :
    ∃ p : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  classical
  by_cases hspan : n = 2 * ell + 1
  · subst n
    exact rainbow_odd_path_on_spanning_carrier hell χ hnew
  · obtain ⟨p, hp⟩ :=
      ErdosProblems.PathHighNew.exists_rainbow_even_path_of_high_new
        hell (by omega) χ hnew
    have hab : 2 * ell + 1 ≤ 2 * ell + 2 := by omega
    -- The checked Stage2V6 prefix/composition helpers are private.
    -- This literal adapter uses the same Fin.castLE and mapEdgeSet APIs.
    let q : (pathGraph (2 * ell + 1)).Copy (pathGraph (2 * ell + 2)) :=
      { toHom :=
          { toFun := Fin.castLE hab
            map_rel' := by
              intro i j hij
              apply pathGraph_adj.mpr
              simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
        injective' := Fin.castLE_injective hab }
    have hmap (e : (pathGraph (2 * ell + 1)).edgeSet) :
        (p.comp q).toHom.mapEdgeSet e =
          p.toHom.mapEdgeSet (q.toHom.mapEdgeSet e) := by
      apply Subtype.ext
      simpa only [Copy.comp, Hom.mapEdgeSet, Hom.coe_comp] using
        (Sym2.map_map (f := q.toHom) (g := p.toHom) e.val).symm
    refine ⟨p.comp q, ?_⟩
    intro e d heq
    apply Hom.mapEdgeSet.injective q.toHom q.injective
    apply hp
    simpa only [EdgeLabeling.pullback_apply, hmap] using heq

end ErdosProblems.PathHighNewOdd

namespace ErdosProblems.PathSevenSpanningBase

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Every original surjective coloring of K7 avoiding literal rainbow P7
uses at most twelve colors. -/
theorem palette_le_twelve_of_no_rainbow_path_seven {q : ℕ}
    (χ : TopEdgeLabeling (Fin 7) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 7).Copy (⊤ : SimpleGraph (Fin 7)),
      ¬ IsRainbow f.toHom χ) : q ≤ 12 := by
  classical
  by_contra hlarge
  have hq : 13 ≤ q := by omega
  have hdense : (7 - 2).choose 2 + 2 ≤ q := by
    have hc52 : (7 - 2 : ℕ).choose 2 = 10 := by decide
    omega
  obtain ⟨r, hconn⟩ := exists_connected_representative_of_dense_palette
    χ hχ (by decide : 0 < 7) hdense
  let G : SimpleGraph (Fin 7) := selectedGraph χ r
  have hGfree : (pathGraph 7).Free G := selectedGraph_free (pathGraph 7) χ r hno
  have hGcount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  obtain ⟨H, hGH, hHfree, hclosure⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by decide : 3 ≤ 7) G hGfree
  have hHconn : H.Connected := SimpleGraph.Connected.mono hGH hconn
  have hHedges : 13 ≤ H.edgeFinset.card := by
    calc
      13 ≤ q := hq
      _ = G.edgeFinset.card := hGcount.symm
      _ ≤ H.edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  have hneTop : H ≠ ⊤ := by
    intro htop
    apply hHfree
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph 7) (⊤ : SimpleGraph (Fin 7)) le_top⟩
  have hclosureLocal : ∀ x y : Fin 7, x ≠ y → ¬ H.Adj x y →
      @SimpleGraph.degree (Fin 7) H x (Subtype.fintype (· ∈ H.neighborSet x)) +
      @SimpleGraph.degree (Fin 7) H y (Subtype.fintype (· ∈ H.neighborSet y)) ≤ 7 - 2 := by
    intro x y hxy hnon
    have h := hclosure x y hxy hnon
    have hx : @SimpleGraph.degree (Fin 7) H x (Subtype.fintype (· ∈ H.neighborSet x)) = H.degree x := by
      congr 1; exact Subsingleton.elim _ _
    have hy : @SimpleGraph.degree (Fin 7) H y (Subtype.fintype (· ∈ H.neighborSet y)) = H.degree y := by
      congr 1; exact Subsingleton.elim _ _
    rw [hx, hy]
    exact h
  obtain ⟨a, _L, ha, htwice, _hLcard, _hLdegree, hCap⟩ :=
    spanning_degree_slots_and_edge_count 7 (by decide) H hHconn hneTop hclosureLocal
  have hc52 : (7 - 1 - 1 : ℕ).choose 2 = 10 := by decide
  have hc42 : (7 - 1 - 2 : ℕ).choose 2 = 6 := by decide
  have hcases : a = 1 ∨ a = 2 := by omega
  rcases hcases with hOne | hTwo
  · subst a
    omega
  · subst a
    omega

/-- Literal order-seven anti-Ramsey upper in the original definition. -/
theorem antiRamseyNum_path_seven_seven_le_twelve :
    antiRamseyNum (pathGraph 7) 7 ≤ 12 := by
  unfold antiRamseyNum
  apply csSup_le'
  rintro q ⟨χ, hχ, hno⟩
  exact palette_le_twelve_of_no_rainbow_path_seven χ hχ hno

/-- Literal order-seven equality, reusing the registered maximum lower bound. -/
theorem antiRamseyNum_path_seven_seven_eq_twelve :
    antiRamseyNum (pathGraph 7) 7 = 12 := by
  apply Nat.le_antisymm antiRamseyNum_path_seven_seven_le_twelve
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 7 7 (by decide) (by decide)
  have hOdd : Odd (7 : ℕ) := by decide
  have hc52 : (7 - 2 : ℕ).choose 2 = 10 := by decide
  have hc22 : (((7 - 1 : ℕ) / 2) - 1).choose 2 = 1 := by decide
  simp only [hOdd, ite_true] at hlower
  omega

end ErdosProblems.PathSevenSpanningBase

namespace ErdosProblems.PathSevenOriginalAllHostExact1105

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

theorem palette_le_of_smaller_host_bound {m q : ℕ} (hm : 7 ≤ m)
    (hIH : antiRamseyNum (pathGraph 7) m ≤ 2 * m - 2)
    (χ : TopEdgeLabeling (Fin (m + 1)) (Fin q))
    (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 7).Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬ IsRainbow f.toHom χ) : q ≤ 2 * (m + 1) - 2 := by
  classical
  by_contra hnot
  have hlarge : 2 * (m + 1) - 2 < q := by omega
  have hnew : ∀ v : Fin (m + 1), 3 ≤ (newColors χ v).card := by
    intro v
    have hdelete := surjective_color_count_le_antiRamseyNum_add_newColors
      (pathGraph 7) χ hχ hno v
    have hstep : q ≤ (2 * m - 2) + (newColors χ v).card :=
      le_trans hdelete (Nat.add_le_add_right hIH (newColors χ v).card)
    omega
  obtain ⟨f, hf⟩ :=
    ErdosProblems.PathHighNewOdd.exists_rainbow_odd_path_of_high_new
      (ell := 3) (by decide) (by omega) χ hnew
  exact hno f hf

theorem antiRamseyNum_path_seven_le (n : ℕ) :
    7 ≤ n → antiRamseyNum (pathGraph 7) n ≤ 2 * n - 2 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hbase : n = 7
    · subst n
      simpa using ErdosProblems.PathSevenSpanningBase.antiRamseyNum_path_seven_seven_le_twelve
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (by omega)
    have hm : 7 ≤ m := by omega
    have hIH : antiRamseyNum (pathGraph 7) m ≤ 2 * m - 2 :=
      ih m (by omega) hm
    unfold antiRamseyNum
    apply csSup_le'
    rintro q ⟨χ, hχ, hno⟩
    exact palette_le_of_smaller_host_bound hm hIH χ hχ hno

/-- The exact original-host P7 anti-Ramsey number on every n>=7. -/
theorem antiRamseyNum_path_seven_eq (n : ℕ) (hn : 7 ≤ n) :
    antiRamseyNum (pathGraph 7) n = 2 * n - 2 := by
  have hupper := antiRamseyNum_path_seven_le n hn
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 7 n (by decide) hn
  have hOdd : Odd (7 : ℕ) := by decide
  have hc52 : (7 - 2 : ℕ).choose 2 = 10 := by decide
  have hc22 : (((7 - 1 : ℕ) / 2) - 1).choose 2 = 1 := by decide
  simp only [hOdd, ite_true] at hlower
  exact Nat.le_antisymm hupper (by omega)

/-- The literal fixed-k=7 slice of FC1105(ii), retaining all n>=7. -/
theorem path_seven_formal_conjectures_slice (n : ℕ) (hn : 7 ≤ n) :
    let ℓ := (7 - 1 : ℕ) / 2
    let ε := if Odd (7 : ℕ) then 1 else 2
    antiRamseyNum (pathGraph 7) n =
      max ((7 - 2 : ℕ).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  simp only [show Odd (7 : ℕ) by decide, ite_true]
  change antiRamseyNum (pathGraph 7) n =
    max ((5 : ℕ).choose 2 + 1)
      ((2 : ℕ).choose 2 + 2 * (n - 3 + 1) + 1)
  have hA : ((5 : ℕ).choose 2 + 1) = 11 := by decide
  have hB : ((2 : ℕ).choose 2 + 2 * (n - 3 + 1) + 1) = 2 * n - 2 := by
    simp only [show (2 : ℕ).choose 2 = 1 by decide]
    omega
  rw [hA, hB, max_eq_right (show (11 : ℕ) ≤ 2 * n - 2 by omega)]
  exact antiRamseyNum_path_seven_eq n hn

end ErdosProblems.PathSevenOriginalAllHostExact1105

namespace ErdosProblems.PathUpperReduction.OddPathsUniversalExact1105

open SimpleGraph

/-- For every odd `k ≥ 9` and `n ≥ k`, the anti-Ramsey number `AR(n, P_k)` equals
the literal Formal Conjectures formula. -/
theorem antiRamseyNum_odd_path_ge_nine_eq_formula (k n : ℕ)
    (hk : 9 ≤ k) (hodd : Odd k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  dsimp only
  have hupper :=
    OddUniversalUpper1105.antiRamseyNum_odd_path_le_formula k n hk hodd hkn
  have hupper' :
      antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          (((k - 1) / 2 - 1).choose 2 +
            ((k - 1) / 2 - 1) * (n - (k - 1) / 2 + 1) +
              (if Odd k then 1 else 2)) := by
    simpa only [ite_eq_left hodd] using hupper
  have hlower :=
    ErdosProblems.PathSetLower.pathMaxLower k n (by omega) hkn
  exact Nat.le_antisymm hupper' hlower

/-- Unconditional exact formula of Erdős #1105 part (ii) for every odd path order
`k ≥ 5` and every complete host size `n ≥ k`. -/
theorem erdos_1105_odd_paths_exact (k n : ℕ)
    (hk : 5 ≤ k) (hodd : Odd k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  have hmod : k % 2 = 1 := Nat.odd_iff.mp hodd
  have hcases : k = 5 ∨ k = 7 ∨ 9 ≤ k := by omega
  rcases hcases with rfl | rfl | hk9
  · exact ErdosProblems.AntiRamseyPathFiveExact.path_five_formal_slice n hkn
  · exact ErdosProblems.PathSevenOriginalAllHostExact1105.path_seven_formal_conjectures_slice n hkn
  · exact antiRamseyNum_odd_path_ge_nine_eq_formula k n hk9 hodd hkn

end ErdosProblems.PathUpperReduction.OddPathsUniversalExact1105

namespace ErdosProblems.PathSixOriginalColourEight

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.AntiRamseyPathSixTransfer
open ErdosProblems.AntiRamseyPathSixK23Transfer

theorem starCore_of_actual_s1_shape
    (H : SimpleGraph (Fin 6)) (L : Finset (Fin 6)) (hL : L.card = 2)
    (w : Fin 6) (hw : w ∉ L)
    (hshape : ∀ x y, H.Adj x y ↔ x ≠ y ∧
      ((x ∉ L ∧ y ∉ L) ∨ (x ∈ L ∧ y = w) ∨ (y ∈ L ∧ x = w))) :
    ∃ u : Fin 6 → Fin 6, Function.Injective u ∧ RepresentativeStarCoreOn H u := by
  classical
  let C : Finset (Fin 6) := Lᶜ
  have hC : C.card = 4 := by
    simpa only [Fintype.card_fin, hL] using Finset.card_compl L
  have hwC : w ∈ C := Finset.mem_compl.mpr hw
  let T := C.erase w
  have hT : T.card = 3 := by
    simpa only [hC] using Finset.card_erase_of_mem hwC
  let leaves : Fin 2 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hL).symm i).val
  let others : Fin 3 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hT).symm i).val
  have hLeavesL (i : Fin 2) : leaves i ∈ L :=
    ((Finset.equivFinOfCardEq hL).symm i).property
  have hOthersT (i : Fin 3) : others i ∈ T :=
    ((Finset.equivFinOfCardEq hT).symm i).property
  have hLeaves : Function.Injective leaves := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hL).symm.injective
    exact Subtype.ext heq
  have hOthers : Function.Injective others := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hT).symm.injective
    exact Subtype.ext heq
  let hub : Fin 1 → Fin 6 := fun _ => w
  have hHub : Function.Injective hub := fun _i _j _h => Subsingleton.elim _ _
  let core : Fin 4 → Fin 6 := Fin.append hub others
  have hCore : Function.Injective core := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hHub, hOthers, ?_⟩
    intro i j heq
    exact (Finset.mem_erase.mp (hOthersT j)).1 heq.symm
  have hCoreC (i : Fin 4) : core i ∈ C := by
    refine Fin.addCases (m := 1) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simpa only [core, Fin.append_left, hub] using hwC
    · simpa only [core, Fin.append_right] using (Finset.mem_erase.mp (hOthersT j)).2
  have hCoreEdge (i j : Fin 4) (hij : i ≠ j) : H.Adj (core i) (core j) :=
    (hshape _ _).mpr ⟨hCore.ne hij,
      Or.inl ⟨Finset.mem_compl.mp (hCoreC i), Finset.mem_compl.mp (hCoreC j)⟩⟩
  have hLeafEdge (i : Fin 2) : H.Adj (leaves i) w := by
    apply (hshape _ _).mpr
    refine ⟨?_, Or.inr (Or.inl ⟨hLeavesL i, rfl⟩)⟩
    intro heq
    exact hw (heq ▸ hLeavesL i)
  let u : Fin 6 → Fin 6 := Fin.append leaves core
  have hu : Function.Injective u := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hLeaves, hCore, ?_⟩
    intro i j heq
    exact (Finset.mem_compl.mp (hCoreC j)) (heq ▸ hLeavesL i)
  refine ⟨u, hu, ?_⟩
  constructor
  · change H.Adj (core 0) (core 1)
    exact hCoreEdge 0 1 (by decide)
  · change H.Adj (core 0) (core 2)
    exact hCoreEdge 0 2 (by decide)
  · change H.Adj (core 0) (core 3)
    exact hCoreEdge 0 3 (by decide)
  · change H.Adj (core 1) (core 2)
    exact hCoreEdge 1 2 (by decide)
  · change H.Adj (core 1) (core 3)
    exact hCoreEdge 1 3 (by decide)
  · change H.Adj (core 2) (core 3)
    exact hCoreEdge 2 3 (by decide)
  · change H.Adj (leaves 0) w
    exact hLeafEdge 0
  · change H.Adj (leaves 1) w
    exact hLeafEdge 1

/-- The original six-vertex coloring cannot have eight or more colors and
avoid every rainbow six-vertex path. All graph/owner witnesses are derived. -/
theorem no_surjective_no_rainbow_path_six_palette_ge_eight
    {q : ℕ} (hq : 8 ≤ q)
    (χ : TopEdgeLabeling (Fin 6) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
      ¬ IsRainbow f.toHom χ) : False := by
  classical
  have hDensity : (6 - 2).choose 2 + 2 ≤ q := by change 8 ≤ q; exact hq
  obtain ⟨r, hGconn⟩ := exists_connected_representative_of_dense_palette χ hχ
    (by decide) hDensity
  let G := selectedGraph χ r
  have hGfree : (pathGraph 6).Free G := selectedGraph_free (pathGraph 6) χ r hno
  have hGcount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  have hGedges : 8 ≤ G.edgeFinset.card := by rw [hGcount]; exact hq
  obtain ⟨H, hGH, hHfree, hclosed⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by decide : 3 ≤ 6) G hGfree
  have hHconn : H.Connected := SimpleGraph.Connected.mono hGH hGconn
  have hHedges : 8 ≤ H.edgeFinset.card :=
    hGedges.trans (Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH))
  have hneTop : H ≠ ⊤ := by
    intro htop
    apply hHfree
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph 6) (⊤ : SimpleGraph (Fin 6)) le_top⟩
  obtain ⟨a, L, ha, htwo, hLcard, hLdeg, _hCount, hCap⟩ :=
    spanning_degree_slots_with_nonuniversal_cap 6 (by decide) H hHconn hneTop
      (by
        intro x y hxy hnon
        convert hclosed x y hxy hnon using 1
        congr 2 <;> exact Subsingleton.elim _ _)
  have hcases : a = 1 ∨ a = 2 := by omega
  rcases hcases with haOne | haTwo
  · subst a
    have hLtwo : L.card = 2 := by simpa using hLcard
    have hHthreshold : (6 - 2).choose 2 + 2 ≤ H.edgeFinset.card := hHedges
    obtain ⟨w, hw, _hDegreeOne, hHcount, _hCoreTop, _hIndependent, hShape⟩ :=
      a_one_slots_force_s1 6 (by decide) H hHconn
        (by
          intro x y hxy hnon
          convert hclosed x y hxy hnon using 1
          congr 2 <;> exact Subsingleton.elim _ _)
        L hLtwo hLdeg hHthreshold
    change H.edgeFinset.card = 8 at hHcount
    have hEdgeEq : G.edgeFinset = H.edgeFinset :=
      Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hGH) (by omega)
    have hGeqH : G = H := SimpleGraph.edgeFinset_inj.mp hEdgeEq
    obtain ⟨u, hu, hStarH⟩ := starCore_of_actual_s1_shape H L hLtwo w hw hShape
    have hStarG : RepresentativeStarCoreOn (selectedGraph χ r) u := by
      change RepresentativeStarCoreOn G u
      rw [hGeqH]
      exact hStarH
    obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_starCore χ r u hu hStarG
    exact hno f hf
  · subst a
    obtain ⟨U, _hUniversals, hUtwo, _hNeighbors, hShape, hHcount⟩ :=
      ErdosProblems.PathUpperFinSixJoin.fin_six_join_of_nonuniversal_degree_cap
        H hneTop hHedges (by intro x hx; exact hCap x hx)
    obtain ⟨u, hu, hK23⟩ :=
      ErdosProblems.PathUpperFinSixExtractor.representative_k23_of_dense_fin_six_join
        G H hGH
        (by
          convert hGedges using 1
          (congr 2; exact Subsingleton.elim _ _))
        U hUtwo hShape hHcount
    obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_k23 χ r u hu hK23
    exact hno f hf

end ErdosProblems.PathSixOriginalColourEight

namespace ErdosProblems.PathSixNumericalExact

open SimpleGraph
open ErdosProblems.PathSixOriginalColourEight
open ErdosProblems.AntiRamseyPathSixSixConditionalCollapse

/-- Every original surjective coloring of K6 avoiding literal rainbow P6
uses at most seven colors. No owner/graph witness is supplied. -/
theorem palette_le_seven_of_no_rainbow_path_six {q : ℕ}
    (χ : TopEdgeLabeling (Fin 6) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
      ¬ IsRainbow f.toHom χ) : q ≤ 7 := by
  by_contra hq
  exact no_surjective_no_rainbow_path_six_palette_ge_eight (by omega) χ hχ hno

/-- Literal original anti-Ramsey upper at n=k=6, consuming the checked
conditional numerical adapter after deriving its eight-color input. -/
theorem antiRamseyNum_path_six_six_le_seven :
    antiRamseyNum (pathGraph 6) 6 ≤ 7 := by
  apply antiRamseyNum_pathGraph_six_six_le_seven_of_eight_exclusion
  rintro ⟨χ, hχ, hno⟩
  exact no_surjective_no_rainbow_path_six_palette_ge_eight (by decide) χ hχ hno

/-- Literal original equality at n=k=6. The registered maximum lower
construction and its numerical reduction are reused through the adapter. -/
theorem antiRamseyNum_path_six_six_eq_seven :
    antiRamseyNum (pathGraph 6) 6 = 7 := by
  apply antiRamseyNum_pathGraph_six_six_eq_seven_of_eight_exclusion
  rintro ⟨χ, hχ, hno⟩
  exact no_surjective_no_rainbow_path_six_palette_ge_eight (by decide) χ hχ hno

end ErdosProblems.PathSixNumericalExact

namespace ErdosProblems.PathSixOriginalAllHostUpper1105

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

theorem pathSixEvenBound_eq (n : ℕ) (hn : 6 ≤ n) :
    max ((2 * 2 : ℕ).choose 2 + 1)
      ((2 - 1 : ℕ).choose 2 + (2 - 1) * (n - 2 + 1) + 2) = n + 1 := by
  have hA : ((2 * 2 : ℕ).choose 2 + 1) = 7 := by decide
  have hB : ((2 - 1 : ℕ).choose 2 + (2 - 1) * (n - 2 + 1) + 2) = n + 1 := by
    simp only [show (2 - 1 : ℕ) = 1 by decide,
      show (1 : ℕ).choose 2 = 0 by decide, zero_add, one_mul]
    omega
  rw [hA, hB]
  exact max_eq_right (by omega)

/-- The original anti-Ramsey P6 upper holds for every n>=6. The finite base,
original high NEW and graph choices are all derived internally. -/
theorem antiRamseyNum_path_six_le (n : ℕ) (hn : 6 ≤ n) :
    antiRamseyNum (pathGraph 6) n ≤ n + 1 := by
  classical
  have hhigh :
      ∀ (m : ℕ), 2 * 2 + 2 ≤ m →
        ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin m) C),
          (∀ v : Fin m, 2 ≤ (newColors χ v).card) →
          ∃ f : (pathGraph (2 * 2 + 2)).Copy (⊤ : SimpleGraph (Fin m)),
            IsRainbow f.toHom χ := by
    intro m hm C _ χ hnew
    by_contra h
    have hnoP :
        ∀ p : (pathGraph (2 * 2 + 2)).Copy (⊤ : SimpleGraph (Fin m)),
          ¬ IsRainbow p.toHom χ := by
      intro p hp
      exact h ⟨p, hp⟩
    have hnoC :=
      ErdosProblems.PathHighNewStageOne.no_rainbow_odd_cycle_of_high_new_and_no_even_path
        (ell := 2) (by decide) hm χ hnew hnoP
    exact h
      (ErdosProblems.PathHighNewStageTwo.rainbow_even_path_of_high_new_and_no_odd_cycle
        (ell := 2) χ (by decide) hm hnew hnoC)
  have hbases :
      ∀ (m : ℕ), 2 * 2 + 2 ≤ m →
        m ≤ 2 * 2 + 2 + (2 - 1) / 2 →
        antiRamseyNum (pathGraph (2 * 2 + 2)) m ≤
          max ((2 * 2 : ℕ).choose 2 + 1)
            ((2 - 1 : ℕ).choose 2 + (2 - 1) * (m - 2 + 1) + 2) := by
    intro m hm hwindow
    have hm6 : m = 6 := by omega
    subst m
    simpa only [show (2 * 2 + 2 : ℕ) = 6 by decide,
      show ((2 * 2 : ℕ).choose 2 + 1) = 7 by decide,
      show ((2 - 1 : ℕ).choose 2 + (2 - 1) * (6 - 2 + 1) + 2) = 7 by decide,
      max_self] using
      ErdosProblems.PathSixNumericalExact.antiRamseyNum_path_six_six_le_seven
  have hall :=
    ErdosProblems.AntiRamseyEvenPathFiniteWindow.antiRamseyNum_even_path_le_of_high_new_and_window
      2 (by decide) hhigh hbases
  have hwhole := hall n (by omega)
  simpa only [show (2 * 2 + 2 : ℕ) = 6 by decide,
    pathSixEvenBound_eq n hn] using hwhole

end ErdosProblems.PathSixOriginalAllHostUpper1105

namespace ErdosProblems.PathSixOriginalAllHostExact1105

open SimpleGraph

/-- The exact original-host anti-Ramsey P6 value for every n>=6. -/
theorem antiRamseyNum_path_six_eq (n : ℕ) (hn : 6 ≤ n) :
    antiRamseyNum (pathGraph 6) n = n + 1 := by
  have hupper :=
    ErdosProblems.PathSixOriginalAllHostUpper1105.antiRamseyNum_path_six_le n hn
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 6 n (by decide) hn
  norm_num at hlower
  exact Nat.le_antisymm hupper (by omega)

/-- The literal FC1105(ii) maximum on its full original fixed-k=6 domain. -/
theorem path_six_formal_conjectures_slice (n : ℕ) (hn : 6 ≤ n) :
    let ℓ := (6 - 1 : ℕ) / 2
    let ε := if Odd (6 : ℕ) then 1 else 2
    antiRamseyNum (pathGraph 6) n =
      max ((6 - 2 : ℕ).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  simp only [show ¬ Odd (6 : ℕ) by decide, ite_false]
  change antiRamseyNum (pathGraph 6) n =
    max ((4 : ℕ).choose 2 + 1)
      ((1 : ℕ).choose 2 + 1 * (n - 2 + 1) + 2)
  have hA : ((4 : ℕ).choose 2 + 1) = 7 := by decide
  have hB : ((1 : ℕ).choose 2 + 1 * (n - 2 + 1) + 2) = n + 1 := by
    simp only [show (1 : ℕ).choose 2 = 0 by decide, zero_add, one_mul]
    omega
  rw [hA, hB, max_eq_right (show (7 : ℕ) ≤ n + 1 by omega)]
  exact antiRamseyNum_path_six_eq n hn

end ErdosProblems.PathSixOriginalAllHostExact1105

namespace ErdosProblems.PathGeneralFiniteWindowReduction

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

def oddBound (ell n : ℕ) : ℕ :=
  max ((2 * ell - 1).choose 2 + 1)
    ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1)

def oddWindowEnd (ell : ℕ) : ℕ :=
  2 * ell + 1 + (ell - 3) / 2

theorem odd_constant_le_linear (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : oddWindowEnd ell ≤ m) :
    (2 * ell - 1).choose 2 + 1 ≤
      (ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 1 := by
  have hmell : ell ≤ m := by dsimp [oddWindowEnd] at hm; omega
  have hthreshold : 5 * ell ≤ 2 * m + 2 := by
    dsimp [oddWindowEnd] at hm
    omega
  have hthresholdR : (5 : ℝ) * (ell : ℝ) ≤ 2 * (m : ℝ) + 2 := by
    exact_mod_cast hthreshold
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast (show 1 ≤ ell by omega)
  have hpredR : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    have hsum : ((ell - 1 : ℕ) : ℝ) + 1 = (ell : ℝ) := by
      exact_mod_cast (show ell - 1 + 1 = ell by omega)
    linarith
  have hmajorR : ((2 * ell - 1 : ℕ) : ℝ) = 2 * (ell : ℝ) - 1 := by
    have hsum : ((2 * ell - 1 : ℕ) : ℝ) + 1 = 2 * (ell : ℝ) := by
      exact_mod_cast (show 2 * ell - 1 + 1 = 2 * ell by omega)
    linarith
  have hsubR : ((m - ell : ℕ) : ℝ) = (m : ℝ) - (ell : ℝ) := by
    have hsum : ((m - ell : ℕ) : ℝ) + (ell : ℝ) = (m : ℝ) := by
      exact_mod_cast (show m - ell + ell = m by omega)
    linarith
  have hproduct : 0 ≤ ((ell : ℝ) - 1) *
      (2 * (m : ℝ) - 5 * (ell : ℝ) + 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hreal :
      (((2 * ell - 1).choose 2 + 1 : ℕ) : ℝ) ≤
        (((ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 1 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [Nat.cast_choose_two ℝ (2 * ell - 1), Nat.cast_choose_two ℝ (ell - 1)]
    simp only [hpredR, hmajorR, hsubR]
    nlinarith [hproduct]
  exact_mod_cast hreal

theorem odd_bound_succ (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : oddWindowEnd ell ≤ m) :
    oddBound ell (m + 1) = oddBound ell m + (ell - 1) := by
  have hmell : ell ≤ m := by dsimp [oddWindowEnd] at hm; omega
  have hleft := odd_constant_le_linear ell m hell hm
  have hright := odd_constant_le_linear ell (m + 1) hell (by omega)
  have hsub : m + 1 - ell + 1 = (m - ell + 1) + 1 := by omega
  simp only [oddBound, max_eq_right hleft, max_eq_right hright]
  rw [hsub]
  ring

theorem odd_upper_of_window (ell : ℕ) (hell : 2 ≤ ell)
    (hbases : ∀ n : ℕ, 2 * ell + 1 ≤ n → n ≤ oddWindowEnd ell →
      antiRamseyNum (pathGraph (2 * ell + 1)) n ≤ oddBound ell n) :
    ∀ n : ℕ, 2 * ell + 1 ≤ n →
      antiRamseyNum (pathGraph (2 * ell + 1)) n ≤ oddBound ell n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hwindow : n ≤ oddWindowEnd ell
    · exact hbases n hn hwindow
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (by omega)
    have hm : oddWindowEnd ell ≤ m := by omega
    have hmk : 2 * ell + 1 ≤ m := by
      dsimp [oddWindowEnd] at hm
      omega
    have hind : antiRamseyNum (pathGraph (2 * ell + 1)) m ≤ oddBound ell m :=
      ih m (by omega) hmk
    have hjump := odd_bound_succ ell m hell hm
    let S : Set ℕ :=
      {q | ∃ χ : TopEdgeLabeling (Fin (m + 1)) (Fin q),
        Function.Surjective χ ∧
        ∀ f : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin (m + 1))),
          ¬IsRainbow f.toHom χ}
    have hbounded : BddAbove S := by
      refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin (m + 1))).edgeSet), ?_⟩
      intro q hq
      obtain ⟨χ, hχ, _⟩ := hq
      simpa using Fintype.card_le_of_surjective χ hχ
    change sSup S ≤ oddBound ell (m + 1)
    refine (csSup_le_iff' hbounded).2 ?_
    intro q hq
    obtain ⟨χ, hχ, hno⟩ := hq
    by_contra hnot
    have hlarge : oddBound ell (m + 1) < q := by omega
    have hnew : ∀ v : Fin (m + 1), ell ≤ (newColors χ v).card := by
      intro v
      have hdelete := surjective_color_count_le_antiRamseyNum_add_newColors
        (pathGraph (2 * ell + 1)) χ hχ hno v
      have hstep : q ≤ oddBound ell m + (newColors χ v).card :=
        le_trans hdelete (Nat.add_le_add_right hind (newColors χ v).card)
      rw [hjump] at hlarge
      omega
    obtain ⟨f, hf⟩ :=
      ErdosProblems.PathHighNewOdd.exists_rainbow_odd_path_of_high_new hell hn χ hnew
    exact hno f hf

/-- The literal universal FC1105(ii) upper direction
to every odd and even original whole-host finite window. Its imported positive
original high-NEW theorems are used, not supplied as public hypotheses. -/
theorem original_path_upper_iff_finite_windows :
    (∀ k n : ℕ, 5 ≤ k → k ≤ n →
      let ell := (k - 1) / 2
      let eps := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + eps)) ↔
    ((∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 1 ≤ n → n ≤ 2 * ell + 1 + (ell - 3) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 1)) n ≤
          max ((2 * ell - 1).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1)) ∧
      (∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 2 ≤ n → n ≤ 2 * ell + 2 + (ell - 1) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
          max ((2 * ell).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2))) := by
  classical
  constructor
  · intro hall
    constructor
    · intro ell hell n hn _
      have hodd : Odd (2 * ell + 1) := ⟨ell, by omega⟩
      have hquot : (2 * ell + 1 - 1) / 2 = ell := by omega
      have hsub : 2 * ell + 1 - 2 = 2 * ell - 1 := by omega
      simpa only [hquot, hsub, ite_eq_left hodd] using
        hall (2 * ell + 1) n (by omega) hn
    · intro ell hell n hn _
      have heven : ¬Odd (2 * ell + 2) := by rintro ⟨r, hr⟩; omega
      have hquot : (2 * ell + 2 - 1) / 2 = ell := by omega
      have hsub : 2 * ell + 2 - 2 = 2 * ell := by omega
      simpa only [hquot, hsub, ite_eq_right heven] using
        hall (2 * ell + 2) n (by omega) hn
  · rintro ⟨hoddWindow, hevenWindow⟩ k n hk hn
    let ell := (k - 1) / 2
    have hell : 2 ≤ ell := by dsimp [ell]; omega
    have hrepr : k = 2 * ell + 1 ∨ k = 2 * ell + 2 := by dsimp [ell]; omega
    rcases hrepr with hoddK | hevenK
    · have hupper := odd_upper_of_window ell hell (hoddWindow ell hell) n (by omega)
      have hodd : Odd k := ⟨ell, by omega⟩
      have hsub : k - 2 = 2 * ell - 1 := by omega
      change antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) +
            (if Odd k then 1 else 2))
      rw [hsub, ite_eq_left hodd, hoddK]
      exact hupper
    · have hhigh : ∀ m : ℕ, 2 * ell + 2 ≤ m →
          ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin m) C),
            (∀ v : Fin m, ell ≤ (newColors χ v).card) →
            ∃ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin m)),
              IsRainbow f.toHom χ := by
        intro m hm C _ χ hnew
        exact ErdosProblems.PathHighNew.exists_rainbow_even_path_of_high_new
          hell hm χ hnew
      have hupper :=
        ErdosProblems.AntiRamseyEvenPathFiniteWindow.antiRamseyNum_even_path_le_of_high_new_and_window
            ell hell hhigh (hevenWindow ell hell) n (by omega)
      have heven : ¬Odd k := by rintro ⟨r, hr⟩; omega
      have hsub : k - 2 = 2 * ell := by omega
      change antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) +
            (if Odd k then 1 else 2))
      rw [hsub, ite_eq_right heven, hevenK]
      exact hupper

end ErdosProblems.PathGeneralFiniteWindowReduction

namespace ErdosProblems.LiteralPathEqualityFiniteWindows1105

open SimpleGraph

/-- The full literal FC1105(ii) equality is equivalent to all original odd
and even finite-window upper bounds; no coloring or graph premise is supplied. -/
theorem original_path_equality_iff_finite_windows :
    (∀ k n : ℕ, 5 ≤ k → k ≤ n →
      let ell := (k - 1) / 2
      let eps := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + eps)) ↔
    ((∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 1 ≤ n → n ≤ 2 * ell + 1 + (ell - 3) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 1)) n ≤
          max ((2 * ell - 1).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1)) ∧
      (∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 2 ≤ n → n ≤ 2 * ell + 2 + (ell - 1) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
          max ((2 * ell).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2))) := by
  constructor
  · intro hall
    apply ErdosProblems.PathGeneralFiniteWindowReduction.original_path_upper_iff_finite_windows.mp
    intro k n hk hn
    exact le_of_eq (hall k n hk hn)
  · intro hwindows
    have hupper :=
      ErdosProblems.PathGeneralFiniteWindowReduction.original_path_upper_iff_finite_windows.mpr hwindows
    intro k n hk hn
    exact Nat.le_antisymm (hupper k n hk hn)
      (ErdosProblems.PathSetLower.pathMaxLower k n hk hn)

end ErdosProblems.LiteralPathEqualityFiniteWindows1105

namespace ErdosProblems.PathUpperReduction.Erdos1105UniversalPathReduction

open SimpleGraph
open ErdosProblems.PathUpperReduction.OddPathsUniversalExact1105

/-- For any fixed `ℓ ≥ 2` (`k = 2 * ℓ + 2`), if the upper bound holds on the finite
host window `2 * ℓ + 2 ≤ n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2`, then the exact Formal Conjectures
equality holds for every `n ≥ 2 * ℓ + 2`. -/
theorem even_path_exact_of_finite_window (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (hwindow : ∀ n : ℕ, 2 * ℓ + 2 ≤ n → n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2 →
      antiRamseyNum (pathGraph (2 * ℓ + 2)) n ≤
        max ((2 * ℓ).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + 2)) :
    ∀ n : ℕ, 2 * ℓ + 2 ≤ n →
      let k := 2 * ℓ + 2
      let ℓ' := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ' - 1).choose 2 + (ℓ' - 1) * (n - ℓ' + 1) + ε) := by
  intro n hn
  have hhigh : ∀ m : ℕ, 2 * ℓ + 2 ≤ m →
      ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin m) C),
        (∀ v : Fin m, ℓ ≤ (ErdosProblems.AntiRamseyCycleNewColors.newColors χ v).card) →
        ∃ f : (pathGraph (2 * ℓ + 2)).Copy (⊤ : SimpleGraph (Fin m)),
          IsRainbow f.toHom χ := by
    intro m hm C _ χ hnew
    exact ErdosProblems.PathHighNew.exists_rainbow_even_path_of_high_new hℓ hm χ hnew
  have hupper :=
    ErdosProblems.AntiRamseyEvenPathFiniteWindow.antiRamseyNum_even_path_le_of_high_new_and_window
      ℓ hℓ hhigh hwindow n hn
  have heven : ¬ Odd (2 * ℓ + 2) := by rintro ⟨r, hr⟩; omega
  have hquot : (2 * ℓ + 2 - 1) / 2 = ℓ := by omega
  have hsub : 2 * ℓ + 2 - 2 = 2 * ℓ := by omega
  have hupper' :
      antiRamseyNum (pathGraph (2 * ℓ + 2)) n ≤
        max (((2 * ℓ + 2) - 2).choose 2 + 1)
          ((((2 * ℓ + 2 - 1) / 2) - 1).choose 2 +
            (((2 * ℓ + 2 - 1) / 2) - 1) * (n - ((2 * ℓ + 2 - 1) / 2) + 1) +
              (if Odd (2 * ℓ + 2) then 1 else 2)) := by
    simpa only [hquot, hsub, ite_eq_right heven] using hupper
  have hlower :=
    ErdosProblems.PathSetLower.pathMaxLower (2 * ℓ + 2) n (by omega) hn
  exact Nat.le_antisymm hupper' hlower

/-- The full literal statement of `Erdos1105.erdos_1105.parts.ii` is equivalent to
the finite base window `2 * ℓ + 2 ≤ n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2` for even paths
`P_{2ℓ+2}` with `ℓ ≥ 3` (`k ≥ 8` even). All odd paths `k ≥ 5`, `P_6` (`k = 6`),
all lower bounds, and all even hosts above the window are discharged unconditionally. -/
theorem erdos_1105_parts_ii_iff_even_windows_ge_three :
    (∀ (k n : ℕ), 5 ≤ k → k ≤ n →
      let ℓ := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)) ↔
    (∀ ℓ : ℕ, 3 ≤ ℓ → ∀ n : ℕ,
      2 * ℓ + 2 ≤ n → n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2 →
      antiRamseyNum (pathGraph (2 * ℓ + 2)) n ≤
        max ((2 * ℓ).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + 2)) := by
  rw [ErdosProblems.LiteralPathEqualityFiniteWindows1105.original_path_equality_iff_finite_windows]
  constructor
  · intro h ℓ hℓ n hn hwin
    exact h.2 ℓ (by omega) n hn hwin
  · intro heven3
    refine ⟨?_, ?_⟩
    · intro ℓ hℓ n hn _hwin
      have hodd : Odd (2 * ℓ + 1) := ⟨ℓ, by omega⟩
      have heq := erdos_1105_odd_paths_exact (2 * ℓ + 1) n (by omega) hodd hn
      have hquot : (2 * ℓ + 1 - 1) / 2 = ℓ := by omega
      have hsub : 2 * ℓ + 1 - 2 = 2 * ℓ - 1 := by omega
      dsimp only at heq
      rw [hquot, hsub, ite_eq_left hodd] at heq
      exact le_of_eq heq
    · intro ℓ hℓ n hn hwin
      have hcases : ℓ = 2 ∨ 3 ≤ ℓ := by omega
      rcases hcases with rfl | hℓ3
      · have hn6 : n = 6 := by omega
        subst n
        have heq := ErdosProblems.PathSixOriginalAllHostExact1105.antiRamseyNum_path_six_eq 6 (by decide)
        change antiRamseyNum (pathGraph 6) 6 ≤
          max ((4 : ℕ).choose 2 + 1) ((1 : ℕ).choose 2 + 1 * (6 - 2 + 1) + 2)
        have hmax : max ((4 : ℕ).choose 2 + 1) ((1 : ℕ).choose 2 + 1 * (6 - 2 + 1) + 2) = 7 := by decide
        rw [heq, hmax]
      · exact heven3 ℓ hℓ3 n hn hwin

end ErdosProblems.PathUpperReduction.Erdos1105UniversalPathReduction

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenFiniteCarrierAdapter1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenActualContactClosure1105

variable {V W : Type*} [Fintype V] [Fintype W]

-- Statement-side equality choices match the literal canonical filter definitions.
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W

noncomputable instance graph_neighborSet_fintype {A : Type*} [Finite A]
    (G : SimpleGraph A) (x : A) : Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- The identical actual-contact filter on an arbitrary finite carrier.
The imported `originalContacts` definition is specialized to `Fin n`. -/
noncomputable def actualContacts (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact S.filter (fun a => ∃ x, x ∉ S ∧ G.Adj x a)

omit [Fintype V] [Fintype W] in
theorem mapped_edge_subset_iff (f : V ↪ W) (e : Sym2 V) (A : Finset V) :
    (f.sym2Map e).toFinset ⊆ A.map f ↔ e.toFinset ⊆ A := by
  classical
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [Finset.subset_iff, Sym2.mem_toFinset, Function.Embedding.sym2Map_apply,
    Sym2.map_mk, Sym2.mem_iff]
  constructor
  · intro h z hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact (Finset.mem_map' f).mp (h (Or.inl rfl))
    · rw [hzy]; exact (Finset.mem_map' f).mp (h (Or.inr rfl))
  · intro h w hw
    rcases hw with hwx | hwy
    · rw [hwx]; exact (Finset.mem_map' f).mpr (h (Or.inl rfl))
    · rw [hwy]; exact (Finset.mem_map' f).mpr (h (Or.inr rfl))

/-- Exact transport of the ORIGINAL unordered within-support edge population.
No equality of filtered counts is supplied to the caller. -/
theorem withinEdges_map_embedding (G : SimpleGraph V) (f : V ↪ W)
    (A : Finset V) :
    withinEdges (G.map f) (A.map f) = (withinEdges G A).map f.sym2Map := by
  classical
  unfold withinEdges
  ext e
  simp only [Finset.mem_filter, Finset.mem_map, mem_edgeFinset]
  constructor
  · revert e
    intro e
    refine Sym2.inductionOn e ?_
    intro x y
    rintro ⟨hxy, heA⟩
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f G x y).mp hxy
    refine ⟨s(u, v), ⟨huv, ?_⟩, rfl⟩
    exact (mapped_edge_subset_iff f s(u, v) A).mp heA
  · rintro ⟨t, ⟨htG, htA⟩, rfl⟩
    refine ⟨?_, (mapped_edge_subset_iff f t A).mpr htA⟩
    revert htG
    refine Sym2.inductionOn t ?_
    intro u v huv
    change (G.map f).Adj (f u) (f v)
    exact (SimpleGraph.map_adj f G (f u) (f v)).mpr ⟨u, v, huv, rfl, rfl⟩

/-- Exact transport of the canonical ORIGINAL unordered cross population;
both exclusion filters refer to the actual transported supports. -/
theorem coreCrossEdges_map_embedding (G : SimpleGraph V) (f : V ↪ W)
    (S U : Finset V) :
    coreCrossEdges (G.map f) (S.map f) (U.map f) =
      (coreCrossEdges G S U).map f.sym2Map := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heNonCore, heNotOutside⟩ := Finset.mem_filter.mp he
    obtain ⟨heWithin, heNotCore⟩ := Finset.mem_filter.mp heNonCore
    rw [withinEdges_map_embedding] at heWithin
    obtain ⟨t, htWithin, rfl⟩ := Finset.mem_map.mp heWithin
    have htNotCore : ¬ t.toFinset ⊆ S := by
      intro htS
      exact heNotCore ((mapped_edge_subset_iff f t S).mpr htS)
    have htNotOutside : ¬ t.toFinset ⊆ U \ S := by
      intro htO
      have hmapped := (mapped_edge_subset_iff f t (U \ S)).mpr htO
      rw [Finset.map_sdiff] at hmapped
      exact heNotOutside hmapped
    exact Finset.mem_map.mpr ⟨t,
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨htWithin, htNotCore⟩, htNotOutside⟩, rfl⟩
  · intro he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨htNonCore, htNotOutside⟩ := Finset.mem_filter.mp ht
    obtain ⟨htWithin, htNotCore⟩ := Finset.mem_filter.mp htNonCore
    have hmappedWithin : f.sym2Map t ∈ withinEdges (G.map f) (U.map f) := by
      rw [withinEdges_map_embedding]
      exact Finset.mem_map.mpr ⟨t, htWithin, rfl⟩
    have hmappedNotCore : ¬ (f.sym2Map t).toFinset ⊆ S.map f := by
      intro heS
      exact htNotCore ((mapped_edge_subset_iff f t S).mp heS)
    have hmappedNotOutside :
        ¬ (f.sym2Map t).toFinset ⊆ U.map f \ S.map f := by
      intro heO
      rw [← Finset.map_sdiff] at heO
      exact htNotOutside ((mapped_edge_subset_iff f t (U \ S)).mp heO)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hmappedWithin, hmappedNotCore⟩, hmappedNotOutside⟩

/-- Actual original contacts are transported by the derived carrier
equivalence; no contact set or correspondence is supplied as an oracle. -/
theorem actualContacts_map_equiv (G : SimpleGraph V) (e : V ≃ W)
    (S : Finset V) :
    actualContacts (G.map e.toEmbedding) (S.map e.toEmbedding) =
      (actualContacts G S).map e.toEmbedding := by
  classical
  have hmem (A : Finset V) (x : V) :
      e x ∈ A.map e.toEmbedding ↔ x ∈ A := Finset.mem_map' e.toEmbedding
  have hadj (x y : V) : (G.map e.toEmbedding).Adj (e x) (e y) ↔ G.Adj x y :=
    (SimpleGraph.Iso.map e G).map_rel_iff'
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  constructor
  · intro hy
    unfold actualContacts at hy ⊢
    simp only [Finset.mem_filter] at hy
    rcases hy with ⟨hxS, z, hzS, hzx⟩
    obtain ⟨w, rfl⟩ := e.surjective z
    apply Finset.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨(hmem S x).mp hxS, w, fun hw => hzS ((hmem S w).mpr hw), (hadj w x).mp hzx⟩
  · intro hy
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hy
    have hzx' : z = x := e.injective hzx
    subst z
    unfold actualContacts at hz ⊢
    simp only [Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hxS, w, hwS, hwx⟩
    exact ⟨(hmem S x).mpr hxS, e w, fun hw => hwS ((hmem S w).mp hw), (hadj w x).mpr hwx⟩

/-- Generic actual finite-carrier contact rigidity. The only carrier-size
guard is its actual cardinality; the Fin equivalence, edge population,
degree/cycle transport and original contacts are all derived internally.
In particular V may be the actual subtype of a replacement support. -/
theorem actual_finite_contact_rigidity {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph V) (hN : Fintype.card V = 2 * d + 3) (S : Finset V)
    (hScard : S.card = d + 3) (hclique : G.IsClique (S : Set V))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hledger : d * d ≤ (coreCrossEdges G S Finset.univ).card +
      (withinEdges G (Finset.univ \ S)).card) :
    (actualContacts G S).card = d ∧
      actualContacts G S ⊆ S ∧
      (S \ actualContacts G S).card = 3 ∧
      (Finset.univ \ S).card = d ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ actualContacts G S) ∨
          (v ∉ S ∧ u ∈ actualContacts G S)) := by
  classical
  let e : V ≃ Fin (2 * d + 3) := Fintype.equivFinOfCardEq hN
  let J := G.map e.toEmbedding
  let S' := S.map e.toEmbedding
  let C := actualContacts G S
  let C' := originalContacts J S'
  have hmemS (x : V) : e x ∈ S' ↔ x ∈ S := Finset.mem_map' e.toEmbedding
  have hadj (x y : V) : J.Adj (e x) (e y) ↔ G.Adj x y :=
    (SimpleGraph.Iso.map e G).map_rel_iff'
  have hS'card : S'.card = d + 3 := by
    change (S.map e.toEmbedding).card = d + 3
    rw [Finset.card_map, hScard]
  have hclique' : J.IsClique (S' : Set (Fin (2 * d + 3))) := by
    intro u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
    exact (hadj a b).mpr (hclique ha hb (fun hab => huv (congrArg e hab)))
  have houtsider' : ∀ x, x ∉ S' → d ≤ J.degree x := by
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hxS : x ∉ S := fun hx => hy ((hmemS x).mpr hx)
    have hdegree := SimpleGraph.degree_map_apply G e.toEmbedding x
    exact hdegree.symm ▸ houtsider x hxS
  have hfree' : (cycleGraph (2 * d + 3)).Free J := by
    rintro ⟨f⟩
    exact hfree ⟨(SimpleGraph.Iso.map e G).symm.toCopy.comp f⟩
  have hcrossMap : coreCrossEdges J S' Finset.univ =
      (coreCrossEdges G S Finset.univ).map e.toEmbedding.sym2Map := by
    have h := coreCrossEdges_map_embedding G e.toEmbedding S Finset.univ
    rw [Finset.map_univ_equiv] at h
    exact h
  have hOutsideMap : (Finset.univ \ S).map e.toEmbedding =
      Finset.univ \ S' := by
    change (Finset.univ \ S).map e.toEmbedding = Finset.univ \ S.map e.toEmbedding
    rw [Finset.map_sdiff, Finset.map_univ_equiv]
  have houtMap : withinEdges J (Finset.univ \ S') =
      (withinEdges G (Finset.univ \ S)).map e.toEmbedding.sym2Map := by
    have h := withinEdges_map_embedding G e.toEmbedding (Finset.univ \ S)
    rw [hOutsideMap] at h
    exact h
  have hledger' : d * d ≤ (coreCrossEdges J S' Finset.univ).card +
      (withinEdges J (Finset.univ \ S')).card := by
    rw [hcrossMap, houtMap, Finset.card_map, Finset.card_map]
    exact hledger
  have hCmap : C' = C.map e.toEmbedding := by
    refine Eq.trans ?_ (actualContacts_map_equiv G e S)
    dsimp only [C']
    unfold originalContacts actualContacts
    congr 1
  have hCcard : C.card = d := by
    have h := EvenOriginalContactCount1105.original_contacts_card_eq
      hd J S' hS'card hclique' houtsider' hfree' hledger'
    change C'.card = d at h
    rw [hCmap, Finset.card_map] at h
    exact h
  have hCS : C ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hthree : (S \ C).card = 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hCS
    rw [hCcard, hScard] at hcard
    omega
  have hOcard : (Finset.univ \ S).card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, hN, hScard] at hcard
    omega
  obtain ⟨_hCS', _hthree', _hOcard', hAdj'⟩ :=
    EvenOriginalContactCount1105.original_contact_rigidity_of_suffix_ledger
      hd J S' hS'card hclique' houtsider' hfree' hledger'
  have hmemC (x : V) : e x ∈ C' ↔ x ∈ C := by
    rw [hCmap]
    exact Finset.mem_map' e.toEmbedding
  refine ⟨hCcard, hCS, hthree, hOcard, ?_⟩
  intro u v
  have h := hAdj' (e u) (e v)
  change J.Adj (e u) (e v) ↔ e u ≠ e v ∧
    ((e u ∈ S' ∧ e v ∈ S') ∨
      (e u ∉ S' ∧ e v ∈ C') ∨
      (e v ∉ S' ∧ e u ∈ C')) at h
  simpa only [hadj, hmemS, hmemC, ne_eq, e.injective.eq_iff] using h

end ErdosProblems.PathUpperReduction.EvenFiniteCarrierAdapter1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenInducedCarrier1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105

variable {V : Type*} [Fintype V]

local instance : DecidableEq V := Classical.decEq V

noncomputable instance graph_neighborSet_fintype {A : Type*} [Finite A]
    (G : SimpleGraph A) (x : A) : Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Lift an actual ambient support to the whole induced carrier W. -/
noncomputable def liftSupport (W A : Finset V) : Finset (W : Set V) := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ A)

omit [Fintype V] in
@[simp] theorem mem_liftSupport (W A : Finset V) (x : (W : Set V)) :
    x ∈ liftSupport W A ↔ x.val ∈ A := by
  classical
  simp only [liftSupport, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] in
@[simp] theorem liftSupport_self (W : Finset V) :
    liftSupport W W = Finset.univ := by
  classical
  ext x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    exact (mem_liftSupport W W x).mpr x.property

omit [Fintype V] in
theorem liftSupport_sdiff (W A B : Finset V) :
    liftSupport W (A \ B) = liftSupport W A \ liftSupport W B := by
  classical
  ext x
  simp only [mem_liftSupport, Finset.mem_sdiff]

omit [Fintype V] in
/-- Projection is a genuine bijection onto A when A is inside W. -/
theorem liftSupport_map (W A : Finset V) (hAW : A ⊆ W) :
    (liftSupport W A).map (Function.Embedding.subtype (· ∈ (W : Set V))) = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_liftSupport W A y).mp hy
  · intro hx
    exact Finset.mem_map.mpr
      ⟨⟨x, hAW hx⟩, (mem_liftSupport W A ⟨x, hAW hx⟩).mpr hx, rfl⟩

omit [Fintype V] in
theorem liftSupport_card (W A : Finset V) (hAW : A ⊆ W) :
    (liftSupport W A).card = A.card := by
  classical
  have h := congrArg Finset.card (liftSupport_map W A hAW)
  rw [Finset.card_map] at h
  exact h

omit [Fintype V] in
/-- The full induced carrier has its actual support cardinality. -/
theorem induced_carrier_card (W : Finset V) :
    Fintype.card (W : Set V) = W.card := Fintype.card_coe W

omit [Fintype V] in
theorem clique_lift (G : SimpleGraph V) (W S : Finset V)
    (hclique : G.IsClique (S : Set V)) :
    (G.induce (W : Set V)).IsClique (liftSupport W S : Set (W : Set V)) := by
  classical
  intro u hu v hv huv
  exact hclique ((mem_liftSupport W S u).mp hu) ((mem_liftSupport W S v).mp hv)
    (fun hval => huv (Subtype.ext hval))

omit [Fintype V] in
/-- Noninduced copy freedom is inherited through the actual subtype projection. -/
theorem cycle_free_induce (G : SimpleGraph V) (W : Finset V) (m : ℕ)
    (hfree : (cycleGraph m).Free G) :
    (cycleGraph m).Free (G.induce (W : Set V)) := by
  rintro ⟨f⟩
  exact hfree ⟨(SimpleGraph.Copy.induce G (W : Set V)).comp f⟩

/-- Actual restricted degree is the ambient original neighbor filter count. -/
theorem degree_induce_eq_withinDegree (G : SimpleGraph V) (W : Finset V)
    (u : (W : Set V)) :
    (G.induce (W : Set V)).degree u = withinDegree G W u.val := by
  classical
  change ((G.induce (W : Set V)).neighborFinset u).card =
    (W.filter (fun z => G.Adj u.val z)).card
  apply Finset.card_bij (fun v _hv => v.val)
  · intro v hv
    have hadj : (G.induce (W : Set V)).Adj u v :=
      (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mp hv
    exact Finset.mem_filter.mpr ⟨v.property, hadj⟩
  · intro v₁ _hv₁ v₂ _hv₂ hval
    exact Subtype.ext hval
  · intro z hz
    obtain ⟨hzW, hadj⟩ := Finset.mem_filter.mp hz
    let v : (W : Set V) := ⟨z, hzW⟩
    have hv : v ∈ (G.induce (W : Set V)).neighborFinset u :=
      (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mpr hadj
    exact ⟨v, hv, rfl⟩

omit [Fintype V] in
/-- Contacts in the induced graph have an actual ORIGINAL witness in W.
This does not equate them to ambient contacts witnessed outside W. -/
theorem actualContacts_lift_iff (G : SimpleGraph V) (W S : Finset V)
    (u : (W : Set V)) :
    u ∈ EvenFiniteCarrierAdapter1105.actualContacts
        (G.induce (W : Set V)) (liftSupport W S) ↔
      u.val ∈ S ∧ ∃ v ∈ W, v ∉ S ∧ G.Adj v u.val := by
  classical
  unfold EvenFiniteCarrierAdapter1105.actualContacts
  simp only [Finset.mem_filter]
  constructor
  · intro hu
    rcases hu with ⟨huS, v, hvS, hvu⟩
    refine ⟨(mem_liftSupport W S u).mp huS, v.val, v.property, ?_, hvu⟩
    exact fun hv => hvS ((mem_liftSupport W S v).mpr hv)
  · rintro ⟨huS, v, hvW, hvS, hvu⟩
    exact ⟨(mem_liftSupport W S u).mpr huS,
      ⟨v, hvW⟩, (fun hv => hvS ((mem_liftSupport W S ⟨v, hvW⟩).mp hv)), hvu⟩

omit [Fintype V] in
theorem projected_edge_subset_iff (W A : Finset V)
    (e : Sym2 (W : Set V)) :
    (∀ z ∈ (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map e, z ∈ A) ↔
      (∀ z ∈ e, z ∈ liftSupport W A) := by
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.mem_iff,
    mem_liftSupport]
  constructor
  · intro h z hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact h x.val (Or.inl rfl)
    · rw [hzy]; exact h y.val (Or.inr rfl)
  · intro h z hz
    rcases hz with hzx | hzy
    · rw [hzx]; exact h x (Or.inl rfl)
    · rw [hzy]; exact h y (Or.inr rfl)

/-- Projection of an actual induced within-support edge population is exactly
the ambient original population, not just an inequality of counts. -/
theorem withinEdges_lift_map (G : SimpleGraph V) (W A : Finset V)
    (hAW : A ⊆ W) :
    (withinEdges (G.induce (W : Set V)) (liftSupport W A)).map
        (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map = withinEdges G A := by
  classical
  unfold withinEdges
  ext e
  simp only [Finset.mem_map, Finset.mem_filter, mem_edgeFinset,
    Finset.subset_iff, Sym2.mem_toFinset]
  constructor
  · rintro ⟨t, ⟨htG, htA⟩, rfl⟩
    refine ⟨?_, (projected_edge_subset_iff W A t).mpr htA⟩
    revert htG
    refine Sym2.inductionOn t ?_
    intro u v huv
    exact huv
  · revert e
    intro e
    refine Sym2.inductionOn e ?_
    intro x y
    rintro ⟨hxy, hsub⟩
    have hxA : x ∈ A := hsub (Sym2.mem_iff.mpr (Or.inl rfl))
    have hyA : y ∈ A := hsub (Sym2.mem_iff.mpr (Or.inr rfl))
    let u : (W : Set V) := ⟨x, hAW hxA⟩
    let v : (W : Set V) := ⟨y, hAW hyA⟩
    refine ⟨s(u, v), ⟨hxy, ?_⟩, rfl⟩
    exact (projected_edge_subset_iff W A s(u, v)).mp hsub

theorem withinEdges_lift_card (G : SimpleGraph V) (W A : Finset V)
    (hAW : A ⊆ W) :
    (withinEdges (G.induce (W : Set V)) (liftSupport W A)).card =
      (withinEdges G A).card := by
  classical
  have h := congrArg Finset.card (withinEdges_lift_map G W A hAW)
  rw [Finset.card_map] at h
  exact h

/-- Canonical original unordered cross edges project exactly, with BOTH
exclusion filters preserved on the actual supports. -/
theorem coreCrossEdges_lift_map (G : SimpleGraph V) (W S U : Finset V)
    (_hSW : S ⊆ W) (hUW : U ⊆ W) :
    (coreCrossEdges (G.induce (W : Set V)) (liftSupport W S) (liftSupport W U)).map
        (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map =
      coreCrossEdges G S U := by
  classical
  let f := Function.Embedding.subtype (· ∈ (W : Set V))
  let H := G.induce (W : Set V)
  have hdiff (e : Sym2 (W : Set V)) :
      (∀ z ∈ f.sym2Map e, z ∈ U ∧ z ∉ S) ↔
        (∀ z ∈ e, z ∈ liftSupport W U ∧ z ∉ liftSupport W S) := by
    have hp := projected_edge_subset_iff W (U \ S) e
    simpa only [liftSupport_sdiff, Finset.mem_sdiff] using hp
  ext e
  unfold coreCrossEdges nonCoreEdges
  simp only [Finset.mem_map, Finset.mem_filter, Finset.subset_iff, Sym2.mem_toFinset,
    Finset.mem_sdiff]
  constructor
  · intro he
    rcases he with ⟨t, ⟨⟨htWithin, htNotCore⟩, htNotOutside⟩, rfl⟩
    have hmappedWithin : f.sym2Map t ∈ withinEdges G U := by
      rw [← withinEdges_lift_map G W U hUW]
      exact Finset.mem_map.mpr ⟨t, htWithin, rfl⟩
    have hmappedNotCore : ¬ ∀ z ∈ f.sym2Map t, z ∈ S := by
      intro hS
      exact htNotCore ((projected_edge_subset_iff W S t).mp hS)
    have hmappedNotOutside : ¬ ∀ z ∈ f.sym2Map t, z ∈ U ∧ z ∉ S := by
      intro hO
      exact htNotOutside ((hdiff t).mp hO)
    exact ⟨⟨hmappedWithin, hmappedNotCore⟩, hmappedNotOutside⟩
  · intro he
    rcases he with ⟨⟨heWithin, heNotCore⟩, heNotOutside⟩
    rw [← withinEdges_lift_map G W U hUW] at heWithin
    obtain ⟨t, htWithin, rfl⟩ := Finset.mem_map.mp heWithin
    have htNotCore : ¬ ∀ z ∈ t, z ∈ liftSupport W S := by
      intro htS
      exact heNotCore ((projected_edge_subset_iff W S t).mpr htS)
    have htNotOutside : ¬ ∀ z ∈ t, z ∈ liftSupport W U ∧ z ∉ liftSupport W S := by
      intro htO
      exact heNotOutside ((hdiff t).mpr htO)
    exact ⟨t, ⟨⟨htWithin, htNotCore⟩, htNotOutside⟩, rfl⟩

theorem coreCrossEdges_lift_card (G : SimpleGraph V) (W S U : Finset V)
    (hSW : S ⊆ W) (hUW : U ⊆ W) :
    (coreCrossEdges (G.induce (W : Set V)) (liftSupport W S) (liftSupport W U)).card =
      (coreCrossEdges G S U).card := by
  classical
  have h := congrArg Finset.card (coreCrossEdges_lift_map G W S U hSW hUW)
  rw [Finset.card_map] at h
  exact h

/-- The exact original suffix population in the induced carrier, with no
supplied transport equality or duplicated outside-edge incidence count. -/
theorem suffix_ledger_induce (G : SimpleGraph V) (W S : Finset V)
    (hSW : S ⊆ W) :
    (coreCrossEdges (G.induce (W : Set V)) (liftSupport W S) Finset.univ).card +
        (withinEdges (G.induce (W : Set V))
          (Finset.univ \ liftSupport W S)).card =
      (coreCrossEdges G S W).card + (withinEdges G (W \ S)).card := by
  classical
  have hcross := coreCrossEdges_lift_card G W S W hSW (Finset.Subset.refl W)
  rw [liftSupport_self] at hcross
  have hout := withinEdges_lift_card G W (W \ S) Finset.sdiff_subset
  rw [liftSupport_sdiff, liftSupport_self] at hout
  rw [hcross, hout]

end ErdosProblems.PathUpperReduction.EvenInducedCarrier1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenActualSuffixClassification1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenInducedCarrier1105

variable {V : Type*} [Fintype V]

local instance : DecidableEq V := Classical.decEq V

omit [Fintype V] in
/-- Every complete same-G certificate retains the entire terminal core. -/
theorem certificate_core_subset {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (hcertificate : ExactCoreDeletion G d S T) : S ⊆ T := by
  classical
  induction hcertificate with
  | stop => exact fun _ hx => hx
  | delete T x hx hxS hdegree tail ih =>
      intro z hz
      exact (Finset.mem_erase.mp (ih hz)).2

omit [Fintype V] in
/-- Exact forward degrees imply the actual inside-carrier lower bound for
every outsider, including outsiders removed later in the certificate. -/
theorem certificate_outsider_degree_ge {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (hcertificate : ExactCoreDeletion G d S T) :
    ∀ x ∈ T, x ∉ S → d ≤ withinDegree G T x := by
  classical
  induction hcertificate with
  | stop =>
      intro x hx hxS
      exact False.elim (hxS hx)
  | delete T y hy hyS hdegree tail ih =>
      intro x hx hxS
      by_cases hxy : x = y
      · subst x
        exact le_of_eq hdegree.symm
      · have hxTail : x ∈ T.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
        have htailDegree := ih x hxTail hxS
        have hmono : withinDegree G (T.erase y) x ≤ withinDegree G T x := by
          unfold withinDegree
          exact Finset.card_le_card (Finset.filter_subset_filter
            (fun z => G.Adj x z) (Finset.erase_subset y T))
        exact htailDegree.trans hmono

/-- The actual last d outsiders have one common d-element core neighborhood
and no internal edges. The original full certificate supplies every degree
and edge-ledger premise of the finite classifier on the induced carrier T.
All adjacency conclusions concern the original G and pairs actually in T. -/
theorem actual_suffix_classification (G : SimpleGraph V) (d : ℕ)
    (S T : Finset V) (hd : 2 ≤ d)
    (hcertificate : ExactCoreDeletion G d S T)
    (hScard : S.card = d + 3) (hclique : G.IsClique (S : Set V))
    (houtside : (T \ S).card = d)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    ∃ C : Finset V, C ⊆ S ∧ C.card = d ∧
      ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ C) ∨
          (v ∉ S ∧ u ∈ C)) := by
  classical
  have hST : S ⊆ T := certificate_core_subset hcertificate
  have hTcard : T.card = 2 * d + 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hST
    rw [houtside, hScard] at hcard
    omega
  let H := G.induce (T : Set V)
  let S' := liftSupport T S
  have hN : Fintype.card (T : Set V) = 2 * d + 3 := by
    rw [induced_carrier_card, hTcard]
  have hS'card : S'.card = d + 3 := by
    change (liftSupport T S).card = d + 3
    rw [liftSupport_card T S hST, hScard]
  have hclique' : H.IsClique (S' : Set (T : Set V)) :=
    clique_lift G T S hclique
  have houtsider' : ∀ x, x ∉ S' → d ≤ H.degree x := by
    intro x hxS'
    have hxS : x.val ∉ S := by
      intro hxS
      exact hxS' ((mem_liftSupport T S x).mpr hxS)
    change d ≤ (G.induce (T : Set V)).degree x
    rw [degree_induce_eq_withinDegree G T x]
    exact certificate_outsider_degree_ge hcertificate x.val x.property hxS
  have hfree' : (cycleGraph (2 * d + 3)).Free H :=
    cycle_free_induce G T (2 * d + 3) hfree
  have hledger := last_block_cross_edge_ledger hST hcertificate houtside
  have hledger' : d * d ≤ (coreCrossEdges H S' Finset.univ).card +
      (withinEdges H (Finset.univ \ S')).card := by
    have htransport := suffix_ledger_induce G T S hST
    change (coreCrossEdges H S' Finset.univ).card +
        (withinEdges H (Finset.univ \ S')).card =
      (coreCrossEdges G S T).card + (withinEdges G (T \ S)).card at htransport
    rw [htransport, hledger]
  have hsdiffEq : @SDiff.sdiff (Finset (T : Set V))
      (@Finset.instSDiff (T : Set V) (Classical.decEq _)) Finset.univ S' =
      Finset.univ \ S' := by
    ext x; simp only [Finset.mem_sdiff]
  rw [← hsdiffEq] at hledger'
  obtain ⟨hCcard, hCS, _hthree, _hOcard, hAdj⟩ :=
    EvenFiniteCarrierAdapter1105.actual_finite_contact_rigidity
      (by omega : 1 ≤ d) H hN S' hS'card hclique' houtsider' hfree' hledger'
  let C' := EvenFiniteCarrierAdapter1105.actualContacts H S'
  let f := Function.Embedding.subtype (· ∈ (T : Set V))
  let C := C'.map f
  have hmemC (x : (T : Set V)) : x.val ∈ C ↔ x ∈ C' := by
    change f x ∈ C'.map f ↔ x ∈ C'
    exact Finset.mem_map' f
  have hCsub : C ⊆ S := by
    intro z hzC
    obtain ⟨x, hxC, hxz⟩ := Finset.mem_map.mp hzC
    have hxS' : x ∈ S' := hCS hxC
    have hxS : x.val ∈ S := (mem_liftSupport T S x).mp hxS'
    change x.val = z at hxz
    exact hxz ▸ hxS
  have hCcount : C.card = d := by
    change (C'.map f).card = d
    rw [Finset.card_map]
    exact hCcard
  refine ⟨C, hCsub, hCcount, ?_⟩
  intro u hu v hv
  let u' : (T : Set V) := ⟨u, hu⟩
  let v' : (T : Set V) := ⟨v, hv⟩
  have hne : u' ≠ v' ↔ u ≠ v := by
    constructor
    · intro h huv
      apply h
      exact Subtype.ext huv
    · intro h huv
      exact h (congrArg Subtype.val huv)
  have hSu : u' ∈ S' ↔ u ∈ S := mem_liftSupport T S u'
  have hSv : v' ∈ S' ↔ v ∈ S := mem_liftSupport T S v'
  have hCu : u' ∈ C' ↔ u ∈ C := (hmemC u').symm
  have hCv : v' ∈ C' ↔ v ∈ C := (hmemC v').symm
  have h := hAdj u' v'
  change G.Adj u v ↔ u' ≠ v' ∧
    ((u' ∈ S' ∧ v' ∈ S') ∨
      (u' ∉ S' ∧ v' ∈ C') ∨
      (v' ∉ S' ∧ u' ∈ C')) at h
  simpa only [hne, hSu, hSv, hCu, hCv] using h

end ErdosProblems.PathUpperReduction.EvenActualSuffixClassification1105
end

namespace ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105

open SimpleGraph
open ErdosProblems.PathSpanningNonedgeDeficit

/-- Adding one original distinct missing pair preserves ordinary spanning
path freedom on the SAME `Fin N` carrier when the ORIGINAL whole-carrier
endpoint degrees sum to at least `N - 1`. No path endpoint is prescribed. -/
theorem pathGraph_free_after_adding_missing_pair
    {N : ℕ} (hN : 3 ≤ N)
    (G : SimpleGraph (Fin N)) (hfree : (pathGraph N).Free G)
    (u v : Fin N) (huv : u ≠ v) (hmissing : ¬ G.Adj u v)
    (hsum : N - 1 ≤ G.degree u + G.degree v) :
    (pathGraph N).Free (augment G u v) := by
  classical
  intro hcopy
  have hbound : G.degree u + G.degree v ≤ N - 2 :=
    ErdosProblems.PathSpanningNonedgeDeficit.degree_sum_le_of_spanning_path_augmentation
      hN G hfree u v huv hmissing hcopy
  omega

end ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105

noncomputable section

namespace ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105

/-- Literal ORIGINAL degree restricted to all vertices of the actual seed. -/
def originalSeedDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin n)) (w : Fin n) : ℕ := by
  classical
  exact (K.filter (fun v => G.Adj w v)).card

/-- Add exactly the finite distinct W-seed pair family on the same carrier. -/
def fillSeedPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (K W : Finset (Fin n)) : SimpleGraph (Fin n) :=
  G ⊔ fromEdgeSet {e | ∃ w ∈ W, ∃ v ∈ K, w ≠ v ∧ e = s(w,v)}

theorem originalSeedDegree_le_degree {n : ℕ}
    (G : SimpleGraph (Fin n)) (K : Finset (Fin n)) (w : Fin n) :
    originalSeedDegree G K w ≤ G.degree w := by
  classical
  have hsub : K.filter (fun v => G.Adj w v) ⊆ G.neighborFinset w := by
    intro v hv
    exact (G.mem_neighborFinset w v).mpr (Finset.mem_filter.mp hv).2
  simpa only [originalSeedDegree, card_neighborFinset_eq_degree] using
    Finset.card_le_card hsub

/-- The first fill's guard is ORIGINAL kernel/high-pool degree, retained in
every intermediate supergraph; no newly filled degree is counted here. -/
theorem seed_pair_guard {d : ℕ}
    (G J : SimpleGraph (Fin (2*d+2))) (K : Finset (Fin (2*d+2)))
    (w v : Fin (2*d+2)) (hGJ : G ≤ J)
    (hhigh : d+1 ≤ originalSeedDegree G K w)
    (hmin : d ≤ originalSeedDegree G K v) :
    2*d+2-1 ≤ J.degree w + J.degree v := by
  have hw : d+1 ≤ J.degree w :=
    hhigh.trans ((originalSeedDegree_le_degree G K w).trans
      (G.degree_le_of_le (v := w) hGJ))
  have hv : d ≤ J.degree v :=
    hmin.trans ((originalSeedDegree_le_degree G K v).trans
      (G.degree_le_of_le (v := v) hGJ))
  omega

/-- Membership in the explicit fill graph derives complete seed adjacency. -/
theorem filled_seed_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (K W : Finset (Fin n)) (w v : Fin n)
    (hw : w ∈ W) (hv : v ∈ K) (hne : w ≠ v) :
    (fillSeedPairs G K W).Adj w v := by
  apply (SimpleGraph.sup_adj _ _ _ _).mpr
  right
  exact (SimpleGraph.fromEdgeSet_adj _).mpr
    ⟨⟨w, hw, v, hv, hne, rfl⟩, hne⟩

/-- After the explicit first family, the SAME original seed supplies the
whole-carrier degree bound |K|-1 for each W vertex. -/
theorem seed_fill_degree_lower {n : ℕ} (G J : SimpleGraph (Fin n))
    (K W : Finset (Fin n)) (w : Fin n) (hw : w ∈ W) (hwK : w ∈ K)
    (hfill : fillSeedPairs G K W ≤ J) : K.card-1 ≤ J.degree w := by
  classical
  have hsub : K.erase w ⊆ J.neighborFinset w := by
    intro v hv
    obtain ⟨hvw, hvK⟩ := Finset.mem_erase.mp hv
    exact (J.mem_neighborFinset w v).mpr
      (hfill (filled_seed_adj G K W w v hw hvK (Ne.symm hvw)))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hwK, card_neighborFinset_eq_degree] at hcard
  exact hcard

/-- Every second-family missing pair meets the exact N-1 threshold, even
when the peeled vertex is maximally deficient. The seed-first order is real. -/
theorem restoration_pair_guard {d h : ℕ}
    (G J : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (w x : Fin (2*d+2))
    (hh : h ≤ d) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d-h+2 ≤ G.degree x) :
    2*d+2-1 ≤ J.degree w + J.degree x := by
  have hGJ : G ≤ J := le_trans le_sup_left hfill
  have hwdegree := seed_fill_degree_lower G J K W w hw (hWK hw) hfill
  rw [horder] at hwdegree
  have hxdegree : d-h+2 ≤ J.degree x :=
    hpeeled.trans (G.degree_le_of_le (v := x) hGJ)
  omega

/-- One actual second-family step preserves spanning-path freedom using
the guard derived above, not a supplied sum or a path endpoint oracle. -/
theorem path_free_after_missing_restoration_pair {d h : ℕ}
    (hd : 4 ≤ d) (G J : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (w x : Fin (2*d+2))
    (hh : h ≤ d) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hx : x ∉ K)
    (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d-h+2 ≤ G.degree x)
    (hfree : (pathGraph (2*d+2)).Free J) (hmissing : ¬ J.Adj w x) :
    (pathGraph (2*d+2)).Free
      (ErdosProblems.PathSpanningNonedgeDeficit.augment J w x) := by
  have hne : w ≠ x := by
    intro heq
    exact hx (heq ▸ hWK hw)
  exact pathGraph_free_after_adding_missing_pair (by omega) J hfree w x hne
    hmissing (restoration_pair_guard G J K W w x hh horder hWK hw hfill hpeeled)

end ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.SeedFirstPathFill1105

open SimpleGraph
open ErdosProblems.PathSpanningNonedgeDeficit
open ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105
open ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105

/-- A literal finite ordered sequence of augmentations on the SAME carrier.
Already present pairs have no effect, so repeated orientations are harmless. -/
def fillOrdered {N : ℕ} (G : SimpleGraph (Fin N)) :
    List (Fin N × Fin N) → SimpleGraph (Fin N)
  | [] => G
  | p :: ps => fillOrdered (augment G p.1 p.2) ps

/-- The first internally constructed pair family. Diagonal pairs are omitted. -/
def seedPairs {N : ℕ} (K W : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (W ×ˢ K).filter (fun p => p.1 ≠ p.2)

/-- The second internally constructed family uses the literal complement of K. -/
def restoredPairs {N : ℕ} (K W : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (W ×ˢ (Finset.univ \ K)).filter (fun p => p.1 ≠ p.2)

def seedFilled {N : ℕ} (G : SimpleGraph (Fin N)) (K W : Finset (Fin N)) :=
  fillOrdered G (seedPairs K W).toList

def seedFirstFilled {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) :=
  fillOrdered (seedFilled G K W) (restoredPairs K W).toList

theorem augment_le {N : ℕ} (G J : SimpleGraph (Fin N))
    (u v : Fin N) (hGJ : G ≤ J) (huv : J.Adj u v) :
    augment G u v ≤ J := by
  apply sup_le hGJ
  intro x y hxy
  obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have heq : s(x,y) = s(u,v) := Set.mem_singleton_iff.mp hpair
  rcases Sym2.eq_iff.mp heq with h | h
  · simpa only [h.1, h.2] using huv
  · simpa only [h.1, h.2] using J.adj_symm huv

theorem augment_eq_of_adj {N : ℕ} (G : SimpleGraph (Fin N))
    (u v : Fin N) (huv : G.Adj u v) : augment G u v = G :=
  le_antisymm (augment_le G G u v le_rfl huv) le_sup_left

theorem augment_pair_adj {N : ℕ} (G : SimpleGraph (Fin N))
    (u v : Fin N) (hne : u ≠ v) : (augment G u v).Adj u v := by
  apply (SimpleGraph.sup_adj _ _ _ _).mpr
  right
  exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨by simp, hne⟩

theorem le_fillOrdered {N : ℕ} (G : SimpleGraph (Fin N))
    (L : List (Fin N × Fin N)) : G ≤ fillOrdered G L := by
  induction L generalizing G with
  | nil => exact le_rfl
  | cons p ps ih => exact le_trans le_sup_left (ih (augment G p.1 p.2))

theorem fillOrdered_le {N : ℕ} (G J : SimpleGraph (Fin N))
    (L : List (Fin N × Fin N)) (hGJ : G ≤ J)
    (hpairs : ∀ p ∈ L, J.Adj p.1 p.2) : fillOrdered G L ≤ J := by
  have haux : ∀ L : List (Fin N × Fin N), ∀ G : SimpleGraph (Fin N),
      G ≤ J → (∀ p ∈ L, J.Adj p.1 p.2) → fillOrdered G L ≤ J := by
    intro L
    induction L with
    | nil => intro G hGJ _; exact hGJ
    | cons p ps ih =>
        intro G hGJ hpairs
        exact ih (augment G p.1 p.2)
          (augment_le G J p.1 p.2 hGJ (hpairs p (by simp)))
          (fun q hq => hpairs q (by simp only [List.mem_cons]; exact Or.inr hq))
  exact haux L G hGJ hpairs

theorem fillOrdered_pair_adj {N : ℕ} (G : SimpleGraph (Fin N))
    (L : List (Fin N × Fin N)) (p : Fin N × Fin N)
    (hp : p ∈ L) (hne : p.1 ≠ p.2) : (fillOrdered G L).Adj p.1 p.2 := by
  have haux : ∀ L : List (Fin N × Fin N), ∀ G : SimpleGraph (Fin N),
      ∀ p ∈ L, p.1 ≠ p.2 → (fillOrdered G L).Adj p.1 p.2 := by
    intro L
    induction L with
    | nil => intro G p hp; simp at hp
    | cons q qs ih =>
        intro G p hp hne
        rcases List.mem_cons.mp hp with h | h
        · subst p
          exact le_fillOrdered (augment G q.1 q.2) qs
            (augment_pair_adj G q.1 q.2 hne)
        · exact ih (augment G q.1 q.2) p h hne
  exact haux L G p hp hne

/-- A finite sequence preserves P_N-freedom when every actual missing step
has the existing N-1 guard. The final seed caller DERIVES this guard. -/
theorem fillOrdered_free {N : ℕ} (hN : 3 ≤ N)
    (B : SimpleGraph (Fin N)) (L : List (Fin N × Fin N))
    (hne : ∀ p ∈ L, p.1 ≠ p.2)
    (hguard : ∀ J : SimpleGraph (Fin N), B ≤ J →
      ∀ p ∈ L, N-1 ≤ J.degree p.1 + J.degree p.2)
    (J : SimpleGraph (Fin N)) (hBJ : B ≤ J)
    (hfree : (pathGraph N).Free J) : (pathGraph N).Free (fillOrdered J L) := by
  classical
  have haux : ∀ L : List (Fin N × Fin N),
      (∀ p ∈ L, p.1 ≠ p.2) →
      (∀ J : SimpleGraph (Fin N), B ≤ J →
        ∀ p ∈ L, N-1 ≤ J.degree p.1 + J.degree p.2) →
      ∀ J : SimpleGraph (Fin N), B ≤ J → (pathGraph N).Free J →
        (pathGraph N).Free (fillOrdered J L) := by
    intro L
    induction L with
    | nil => intro _ _ J _ hfree; exact hfree
    | cons p ps ih =>
        intro hne hguard J hBJ hfree
        have hstep : (pathGraph N).Free (augment J p.1 p.2) := by
          by_cases hadj : J.Adj p.1 p.2
          · simpa only [augment_eq_of_adj J p.1 p.2 hadj] using hfree
          · exact pathGraph_free_after_adding_missing_pair hN J hfree p.1 p.2
              (hne p (by simp)) hadj (hguard J hBJ p (by simp))
        exact ih
          (fun q hq => hne q (by simp only [List.mem_cons]; exact Or.inr hq))
          (fun H hBH q hq => hguard H hBH q
            (by simp only [List.mem_cons]; exact Or.inr hq))
          (augment J p.1 p.2) (le_trans hBJ le_sup_left) hstep
  exact haux L hne hguard J hBJ hfree

theorem mem_seedPairs {N : ℕ} (K W : Finset (Fin N))
    (p : Fin N × Fin N) : p ∈ seedPairs K W ↔
      p.1 ∈ W ∧ p.2 ∈ K ∧ p.1 ≠ p.2 := by
  classical
  simp only [seedPairs, Finset.mem_filter, Finset.mem_product]
  tauto

theorem mem_restoredPairs {N : ℕ} (K W : Finset (Fin N))
    (p : Fin N × Fin N) : p ∈ restoredPairs K W ↔
      p.1 ∈ W ∧ p.2 ∉ K ∧ p.1 ≠ p.2 := by
  classical
  simp only [restoredPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

/-- The actual completed FIRST ordered family is exactly the existing
explicit seed fill graph. This equality is proved, never a fill oracle. -/
theorem seedFilled_eq {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) : seedFilled G K W = fillSeedPairs G K W := by
  classical
  apply le_antisymm
  · apply fillOrdered_le G (fillSeedPairs G K W) _ le_sup_left
    intro p hp
    obtain ⟨hw, hv, hne⟩ :=
      (mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)
    exact filled_seed_adj G K W p.1 p.2 hw hv hne
  · apply sup_le (le_fillOrdered G _)
    intro u v huv
    obtain ⟨⟨w, hw, x, hx, hne, heq⟩, _⟩ :=
      (SimpleGraph.fromEdgeSet_adj _).mp huv
    have hadj : (seedFilled G K W).Adj w x :=
      fillOrdered_pair_adj G _ (w,x)
        (Finset.mem_toList.mpr ((mem_seedPairs K W (w,x)).mpr ⟨hw,hx,hne⟩)) hne
    rcases Sym2.eq_iff.mp heq with h | h
    · simpa only [seedFilled, h.1, h.2] using hadj
    · simpa only [seedFilled, h.1, h.2] using (seedFilled G K W).adj_symm hadj

/-- Both finite families together add exactly ALL distinct W-incident pairs
on the same carrier, with no added residual edge outside W. -/
theorem seedFirstFilled_eq {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) :
    seedFirstFilled G K W = fillSeedPairs G Finset.univ W := by
  classical
  let H := fillSeedPairs G Finset.univ W
  have hseed : seedFilled G K W ≤ H := by
    apply fillOrdered_le G H _ le_sup_left
    intro p hp
    obtain ⟨hw, _, hne⟩ :=
      (mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)
    exact filled_seed_adj G Finset.univ W p.1 p.2 hw (Finset.mem_univ _) hne
  apply le_antisymm
  · apply fillOrdered_le (seedFilled G K W) H _ hseed
    intro p hp
    obtain ⟨hw, _, hne⟩ :=
      (mem_restoredPairs K W p).mp (Finset.mem_toList.mp hp)
    exact filled_seed_adj G Finset.univ W p.1 p.2 hw (Finset.mem_univ _) hne
  · apply sup_le
      (le_trans (le_fillOrdered G _) (le_fillOrdered (seedFilled G K W) _))
    intro u v huv
    obtain ⟨⟨w, hw, x, _, hne, heq⟩, _⟩ :=
      (SimpleGraph.fromEdgeSet_adj _).mp huv
    have hadj : (seedFirstFilled G K W).Adj w x := by
      by_cases hx : x ∈ K
      · apply le_fillOrdered (seedFilled G K W) _
        rw [seedFilled_eq]
        exact filled_seed_adj G K W w x hw hx hne
      · exact fillOrdered_pair_adj (seedFilled G K W) _ (w,x)
          (Finset.mem_toList.mpr
            ((mem_restoredPairs K W (w,x)).mpr ⟨hw,hx,hne⟩)) hne
    rcases Sym2.eq_iff.mp heq with h | h
    · simpa only [seedFirstFilled, h.1, h.2] using hadj
    · simpa only [seedFirstFilled, h.1, h.2] using (seedFirstFilled G K W).adj_symm hadj

theorem residual_original {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) (u v : Fin N) (hu : u ∉ W) (hv : v ∉ W) :
    (seedFirstFilled G K W).Adj u v ↔ G.Adj u v := by
  rw [seedFirstFilled_eq]
  constructor
  · intro h
    rcases (SimpleGraph.sup_adj _ _ _ _).mp h with h | h
    · exact h
    · obtain ⟨⟨w, hw, x, _, _, heq⟩, _⟩ :=
        (SimpleGraph.fromEdgeSet_adj _).mp h
      rcases Sym2.eq_iff.mp heq with he | he
      · exact False.elim (hu (he.1.symm ▸ hw))
      · exact False.elim (hv (he.2.symm ▸ hw))
  · intro hadj
    exact (show G ≤ fillSeedPairs G Finset.univ W from le_sup_left) hadj

/-- Actual two-phase fixed-carrier path filling. Every degree guard comes
from ORIGINAL G degrees or the PROVED first-family completion. Restored
degree is on this very Fin(2*d+2), not ambient degree on a larger graph.
The caller must derive these retained degrees from its SAME actual trace. -/
theorem seed_first_path_free {d h : ℕ} (hd : 4 ≤ d) (_hlow : 3 ≤ h)
    (hh : h ≤ d) (G : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d+1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d-h+2 ≤ G.degree x)
    (hfree : (pathGraph (2*d+2)).Free G) :
    (pathGraph (2*d+2)).Free (seedFirstFilled G K W) ∧
      G ≤ seedFirstFilled G K W ∧
      (∀ w ∈ W, ∀ v, w ≠ v → (seedFirstFilled G K W).Adj w v) ∧
      (∀ u, u ∉ W → ∀ v, v ∉ W →
        ((seedFirstFilled G K W).Adj u v ↔ G.Adj u v)) := by
  classical
  have hN : 3 ≤ 2*d+2 := by omega
  have hfirst : (pathGraph (2*d+2)).Free (seedFilled G K W) := by
    apply fillOrdered_free hN G (seedPairs K W).toList
      (fun p hp => ((mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)).2.2)
      ?_ G le_rfl hfree
    intro J hGJ p hp
    obtain ⟨hw, hv, _⟩ :=
      (mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)
    exact seed_pair_guard G J K p.1 p.2 hGJ (hhigh p.1 hw) (hmin p.2 hv)
  have hsecond : (pathGraph (2*d+2)).Free (seedFirstFilled G K W) := by
    apply fillOrdered_free hN (seedFilled G K W) (restoredPairs K W).toList
      (fun p hp => ((mem_restoredPairs K W p).mp (Finset.mem_toList.mp hp)).2.2)
      ?_ (seedFilled G K W) le_rfl hfirst
    intro J hseedJ p hp
    obtain ⟨hw, hx, _⟩ :=
      (mem_restoredPairs K W p).mp (Finset.mem_toList.mp hp)
    rw [seedFilled_eq] at hseedJ
    exact restoration_pair_guard G J K W p.1 p.2 hh horder hWK hw hseedJ
      (hrestored p.2 hx)
  refine ⟨hsecond, ?_, ?_, ?_⟩
  · exact le_trans (le_fillOrdered G _) (le_fillOrdered (seedFilled G K W) _)
  · intro w hw v hne
    rw [seedFirstFilled_eq]
    exact filled_seed_adj G Finset.univ W w v hw (Finset.mem_univ _) hne
  · intro u hu v hv
    exact residual_original G K W u v hu hv

/-- The explicit final graph is P_N-free; no filling sequence is supplied
by the caller. This is the direct interface for residual-block arguments. -/
theorem path_free_all_seed_incident_pairs {d h : ℕ} (hd : 4 ≤ d) (hlow : 3 ≤ h)
    (hh : h ≤ d) (G : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d+1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d-h+2 ≤ G.degree x)
    (hfree : (pathGraph (2*d+2)).Free G) :
    (pathGraph (2*d+2)).Free (fillSeedPairs G Finset.univ W) := by
  have hfilled := (seed_first_path_free hd hlow hh G K W horder hWK
    hmin hhigh hrestored hfree).1
  simpa only [seedFirstFilled_eq] using hfilled

end ErdosProblems.PathUpperReduction.SeedFirstPathFill1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.SmallKernelWholeSupport1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.ActualInducedDegree1105
open ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105
open ErdosProblems.PathUpperReduction.SeedFirstPathFill1105
open ErdosProblems.PathUpperReduction.ResidualForestStar1105

local instance (priority := 100) carrierDecidableEq (V : Type*) : DecidableEq V :=
  Classical.decEq V

local instance (priority := 100) carrierDecidableAdj {V : Type*} (G : SimpleGraph V) :
    DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

/-- General weaving lemma: an injective path of length `L ≥ 1` outside a universal
subset `U` of size `k` with `L + 2 * k = N` extends to a spanning `P_N`. -/
theorem spanning_path_of_residual_path {N L k : ℕ}
    (_hL : 1 ≤ L) (hN : L + 2 * k = N)
    (G : SimpleGraph (Fin N)) (U : Finset (Fin N)) (hU : U.card = k)
    (huniv : ∀ u ∈ U, ∀ v, u ≠ v → G.Adj u v)
    (p : Fin L → Fin N) (hpinj : Function.Injective p)
    (hpnotU : ∀ i : Fin L, p i ∉ U)
    (hpadj : ∀ (i j : Fin L), i.val + 1 = j.val → G.Adj (p i) (p j)) :
    (pathGraph N).IsContained G := by
  classical
  let A : Finset (Fin N) := Finset.univ.image p
  have hAcard : A.card = L := by
    rw [Finset.card_image_of_injective _ hpinj, Finset.card_univ, Fintype.card_fin]
  have hpA (i : Fin L) : p i ∈ A :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hUA : Disjoint U A := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvA
    exact hpnotU i hvU
  let T : Finset (Fin N) := Finset.univ \ (U ∪ A)
  have hTcard : T.card = k := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, Finset.card_union_of_disjoint hUA,
      hU, hAcard]
    omega
  let ew : Fin k ≃ U := (Finset.equivFinOfCardEq hU).symm
  let et : Fin k ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  let w : Fin k → Fin N := fun i => (ew i).val
  let t : Fin k → Fin N := fun i => (et i).val
  have hwinj : Function.Injective w := Subtype.val_injective.comp ew.injective
  have htinj : Function.Injective t := Subtype.val_injective.comp et.injective
  have hwU (i : Fin k) : w i ∈ U := (ew i).property
  have htT (i : Fin k) : t i ∈ T := (et i).property
  have htU (i : Fin k) : t i ∉ U := by
    have hn := (Finset.mem_sdiff.mp (htT i)).2
    exact fun hm => hn (Finset.mem_union.mpr (Or.inl hm))
  have htA (i : Fin k) : t i ∉ A := by
    have hn := (Finset.mem_sdiff.mp (htT i)).2
    exact fun hm => hn (Finset.mem_union.mpr (Or.inr hm))
  have hpw (i : Fin L) (j : Fin k) : p i ≠ w j := by
    intro he
    exact hpnotU i (he.symm ▸ hwU j)
  have hpt (i : Fin L) (j : Fin k) : p i ≠ t j := by
    intro he
    exact htA j (he ▸ hpA i)
  have hwt (i j : Fin k) : w i ≠ t j := by
    intro he
    exact htU j (he ▸ hwU i)
  let ix (i : Fin N) (hi : ¬ i.val < L) : Fin k :=
    ⟨(i.val - L) / 2, by have hi := i.isLt; omega⟩
  let q : Fin N → Fin N := fun i =>
    if hi : i.val < L then p ⟨i.val, hi⟩
    else if (i.val - L) % 2 = 0 then w (ix i hi) else t (ix i hi)
  have hqP (i : Fin N) (hi : i.val < L) :
      q i = p ⟨i.val, hi⟩ := by simp only [q, dite_eq_left hi]
  have hqW (i : Fin N) (hi : ¬ i.val < L)
      (hr : (i.val - L) % 2 = 0) : q i = w (ix i hi) := by
    simp only [q, dite_eq_right hi, ite_eq_left hr]
  have hqT (i : Fin N) (hi : ¬ i.val < L)
      (hr : ¬ (i.val - L) % 2 = 0) : q i = t (ix i hi) := by
    simp only [q, dite_eq_right hi, ite_eq_right hr]
  have hqinj : Function.Injective q := by
    intro i j he
    by_cases hi : i.val < L
    · by_cases hj : j.val < L
      · rw [hqP i hi, hqP j hj] at he
        exact Fin.ext (congrArg (fun x : Fin L => x.val) (hpinj he))
      · by_cases hjr : (j.val - L) % 2 = 0
        · rw [hqP i hi, hqW j hj hjr] at he
          exact (hpw _ _ he).elim
        · rw [hqP i hi, hqT j hj hjr] at he
          exact (hpt _ _ he).elim
    · by_cases hj : j.val < L
      · by_cases hir : (i.val - L) % 2 = 0
        · rw [hqW i hi hir, hqP j hj] at he
          exact (hpw _ _ he.symm).elim
        · rw [hqT i hi hir, hqP j hj] at he
          exact (hpt _ _ he.symm).elim
      · by_cases hir : (i.val - L) % 2 = 0
        · by_cases hjr : (j.val - L) % 2 = 0
          · rw [hqW i hi hir, hqW j hj hjr] at he
            have hix := congrArg Fin.val (hwinj he)
            change (i.val - L) / 2 = (j.val - L) / 2 at hix
            apply Fin.ext
            omega
          · rw [hqW i hi hir, hqT j hj hjr] at he
            exact (hwt _ _ he).elim
        · by_cases hjr : (j.val - L) % 2 = 0
          · rw [hqT i hi hir, hqW j hj hjr] at he
            exact (hwt _ _ he.symm).elim
          · rw [hqT i hi hir, hqT j hj hjr] at he
            have hix := congrArg Fin.val (htinj he)
            change (i.val - L) / 2 = (j.val - L) / 2 at hix
            have him := Nat.mod_lt (i.val - L) (by omega : 0 < 2)
            have hjm := Nat.mod_lt (j.val - L) (by omega : 0 < 2)
            apply Fin.ext
            omega
  have hforward (i j : Fin N) (hij : i.val + 1 = j.val) :
      G.Adj (q i) (q j) := by
    have hne : q i ≠ q j := by
      intro he
      have hv := congrArg Fin.val (hqinj he)
      omega
    by_cases hi : i.val < L
    · by_cases hj : j.val < L
      · rw [hqP i hi, hqP j hj]
        exact hpadj ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
      · have hjr : (j.val - L) % 2 = 0 := by omega
        have hadj := huniv (w (ix j hj)) (hwU _) (q i) (by
          rw [← hqW j hj hjr]
          exact Ne.symm hne)
        rw [hqW j hj hjr]
        exact hadj.symm
    · have hj : ¬ j.val < L := by omega
      by_cases hir : (i.val - L) % 2 = 0
      · have hadj := huniv (w (ix i hi)) (hwU _) (q j) (by
          rw [← hqW i hi hir]
          exact hne)
        rw [hqW i hi hir]
        exact hadj
      · have hjr : (j.val - L) % 2 = 0 := by
          have him := Nat.mod_lt (i.val - L) (by omega : 0 < 2)
          omega
        have hadj := huniv (w (ix j hj)) (hwU _) (q i) (by
          rw [← hqW j hj hjr]
          exact Ne.symm hne)
        rw [hqW j hj hjr]
        exact hadj.symm
  let f : (pathGraph N) →g G := ⟨q, by
    intro i j hij
    rcases pathGraph_adj.mp hij with h | h
    · exact hforward i j h
    · exact (hforward j i h).symm⟩
  exact ⟨⟨f, hqinj⟩⟩

/-- An injective `P_3 + P_2` outside `W` (`|W| = d - 1`) in a graph where `W` is
universal yields a spanning `P_{2d+2}`. -/
theorem spanning_path_of_residual_p3_p2 {d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 2))) (W : Finset (Fin (2 * d + 2)))
    (hW : W.card = d - 1)
    (huniv : ∀ w ∈ W, ∀ v, w ≠ v → G.Adj w v)
    (p : Fin 5 → Fin (2 * d + 2)) (hpinj : Function.Injective p)
    (hpnotW : ∀ i : Fin 5, p i ∉ W)
    (h01 : G.Adj (p 0) (p 1)) (h12 : G.Adj (p 1) (p 2)) (h34 : G.Adj (p 3) (p 4)) :
    (pathGraph (2 * d + 2)).IsContained G := by
  classical
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  let U : Finset (Fin (2 * d + 2)) := W.erase w0
  have hUcard : U.card = d - 2 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hw0, hW]
    omega
  have hUuniv : ∀ u ∈ U, ∀ v, u ≠ v → G.Adj u v := by
    intro u hu v hne
    exact huniv u (Finset.mem_erase.mp hu).2 v hne
  have hpw0 (i : Fin 5) : p i ≠ w0 := by
    intro he
    exact hpnotW i (he.symm ▸ hw0)
  let p6 : Fin 6 → Fin (2 * d + 2) := ![p 0, p 1, p 2, w0, p 3, p 4]
  have hp6inj : Function.Injective p6 := by
    intro i j he
    have h01ne : p 0 ≠ p 1 := fun h => by have := hpinj h; revert this; decide
    have h02ne : p 0 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h03ne : p 0 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h04ne : p 0 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h12ne : p 1 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h13ne : p 1 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h14ne : p 1 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h23ne : p 2 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h24ne : p 2 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h34ne : p 3 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have hw00 := hpw0 0; have hw01 := hpw0 1; have hw02 := hpw0 2
    have hw03 := hpw0 3; have hw04 := hpw0 4
    fin_cases i <;> fin_cases j <;>
      simp [p6, h01ne, h01ne.symm, h02ne, h02ne.symm, h03ne, h03ne.symm,
        h04ne, h04ne.symm, h12ne, h12ne.symm, h13ne, h13ne.symm,
        h14ne, h14ne.symm, h23ne, h23ne.symm, h24ne, h24ne.symm,
        h34ne, h34ne.symm, hw00, hw00.symm, hw01, hw01.symm,
        hw02, hw02.symm, hw03, hw03.symm, hw04, hw04.symm] at he ⊢
  have hp6notU : ∀ i : Fin 6, p6 i ∉ U := by
    intro i
    have hn0 := hpnotW 0; have hn1 := hpnotW 1; have hn2 := hpnotW 2
    have hn3 := hpnotW 3; have hn4 := hpnotW 4
    fin_cases i <;> simp [p6, U, hn0, hn1, hn2, hn3, hn4]
  have hp6adj : ∀ (i j : Fin 6), i.val + 1 = j.val → G.Adj (p6 i) (p6 j) := by
    have h2w : G.Adj (p 2) w0 := (huniv w0 hw0 (p 2) (hpw0 2).symm).symm
    have hw3 : G.Adj w0 (p 3) := huniv w0 hw0 (p 3) (hpw0 3).symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p6]
  exact spanning_path_of_residual_path (by omega) (by omega) G U hUcard hUuniv
    p6 hp6inj hp6notU hp6adj

/-- Three vertex-disjoint edges outside `W` (`|W| = d - 1`) in a graph where `W`
is universal yield a spanning `P_{2d+2}`. -/
theorem spanning_path_of_residual_3p2 {d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 2))) (W : Finset (Fin (2 * d + 2)))
    (hW : W.card = d - 1)
    (huniv : ∀ w ∈ W, ∀ v, w ≠ v → G.Adj w v)
    (p : Fin 6 → Fin (2 * d + 2)) (hpinj : Function.Injective p)
    (hpnotW : ∀ i : Fin 6, p i ∉ W)
    (h01 : G.Adj (p 0) (p 1)) (h23 : G.Adj (p 2) (p 3)) (h45 : G.Adj (p 4) (p 5)) :
    (pathGraph (2 * d + 2)).IsContained G := by
  classical
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  let W1 : Finset (Fin (2 * d + 2)) := W.erase w0
  have hW1card : W1.card = d - 2 := by
    dsimp [W1]
    rw [Finset.card_erase_of_mem hw0, hW]
    omega
  obtain ⟨w1, hw1W1⟩ := Finset.card_pos.mp (by omega : 0 < W1.card)
  have hw1ne0 : w1 ≠ w0 := (Finset.mem_erase.mp hw1W1).1
  have hw1 : w1 ∈ W := (Finset.mem_erase.mp hw1W1).2
  let U : Finset (Fin (2 * d + 2)) := W1.erase w1
  have hUcard : U.card = d - 3 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hw1W1, hW1card]
    omega
  have hUuniv : ∀ u ∈ U, ∀ v, u ≠ v → G.Adj u v := by
    intro u hu v hne
    exact huniv u (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2 v hne
  have hpw0 (i : Fin 6) : p i ≠ w0 := fun he => hpnotW i (he.symm ▸ hw0)
  have hpw1 (i : Fin 6) : p i ≠ w1 := fun he => hpnotW i (he.symm ▸ hw1)
  let p8 : Fin 8 → Fin (2 * d + 2) := ![p 0, p 1, w0, p 2, p 3, w1, p 4, p 5]
  have hp8inj : Function.Injective p8 := by
    intro i j he
    have h01ne : p 0 ≠ p 1 := fun h => by have := hpinj h; revert this; decide
    have h02ne : p 0 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h03ne : p 0 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h04ne : p 0 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h05ne : p 0 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h12ne : p 1 ≠ p 2 := fun h => by have := hpinj h; revert this; decide
    have h13ne : p 1 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h14ne : p 1 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h15ne : p 1 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h23ne : p 2 ≠ p 3 := fun h => by have := hpinj h; revert this; decide
    have h24ne : p 2 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h25ne : p 2 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h34ne : p 3 ≠ p 4 := fun h => by have := hpinj h; revert this; decide
    have h35ne : p 3 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have h45ne : p 4 ≠ p 5 := fun h => by have := hpinj h; revert this; decide
    have hw00 := hpw0 0; have hw01 := hpw0 1; have hw02 := hpw0 2
    have hw03 := hpw0 3; have hw04 := hpw0 4; have hw05 := hpw0 5
    have hw10 := hpw1 0; have hw11 := hpw1 1; have hw12 := hpw1 2
    have hw13 := hpw1 3; have hw14 := hpw1 4; have hw15 := hpw1 5
    fin_cases i <;> fin_cases j <;>
      simp [p8, h01ne, h01ne.symm, h02ne, h02ne.symm, h03ne, h03ne.symm,
        h04ne, h04ne.symm, h05ne, h05ne.symm, h12ne, h12ne.symm,
        h13ne, h13ne.symm, h14ne, h14ne.symm, h15ne, h15ne.symm,
        h23ne, h23ne.symm, h24ne, h24ne.symm, h25ne, h25ne.symm,
        h34ne, h34ne.symm, h35ne, h35ne.symm, h45ne, h45ne.symm,
        hw00, hw00.symm, hw01, hw01.symm, hw02, hw02.symm,
        hw03, hw03.symm, hw04, hw04.symm, hw05, hw05.symm,
        hw10, hw10.symm, hw11, hw11.symm, hw12, hw12.symm,
        hw13, hw13.symm, hw14, hw14.symm, hw15, hw15.symm,
        hw1ne0, hw1ne0.symm] at he ⊢
  have hp8notU : ∀ i : Fin 8, p8 i ∉ U := by
    intro i
    have hn0 := hpnotW 0; have hn1 := hpnotW 1; have hn2 := hpnotW 2
    have hn3 := hpnotW 3; have hn4 := hpnotW 4; have hn5 := hpnotW 5
    fin_cases i <;> simp [p8, U, W1, hn0, hn1, hn2, hn3, hn4, hn5]
  have hp8adj : ∀ (i j : Fin 8), i.val + 1 = j.val → G.Adj (p8 i) (p8 j) := by
    have h1w0 : G.Adj (p 1) w0 := (huniv w0 hw0 (p 1) (hpw0 1).symm).symm
    have hw02 : G.Adj w0 (p 2) := huniv w0 hw0 (p 2) (hpw0 2).symm
    have h3w1 : G.Adj (p 3) w1 := (huniv w1 hw1 (p 3) (hpw1 3).symm).symm
    have hw14 : G.Adj w1 (p 4) := huniv w1 hw1 (p 4) (hpw1 4).symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p8]
  exact spanning_path_of_residual_path (by omega) (by omega) G U hUcard hUuniv
    p8 hp8inj hp8notU hp8adj

section StarCenter

local instance (priority := 3000) subtypeNeighborSetFintype {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- Every vertex in `K \ W` has at least one neighbor in `K \ W` because its degree
in `K` is at least `d` and `|W| = d - 1`. -/
theorem residual_min_degree_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (K W : Finset V)
    (hd : 1 ≤ d) (hWcard : W.card = d - 1)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x) :
    ∀ u : (↑(K \ W) : Set V),
      1 ≤ (G.induce (↑(K \ W) : Set V)).degree u := by
  intro u
  have huK : u.val ∈ K := (Finset.mem_sdiff.mp u.property).1
  have hdegK : d ≤ (K.filter (G.Adj u.val)).card := hseed u.val huK
  have hsub : K.filter (G.Adj u.val) ⊆ W ∪ (K \ W).filter (G.Adj u.val) := by
    intro z hz
    obtain ⟨hzK, huz⟩ := Finset.mem_filter.mp hz
    by_cases hzW : z ∈ W
    · exact Finset.mem_union.mpr (Or.inl hzW)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hzK, hzW⟩, huz⟩))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hpos : 0 < ((K \ W).filter (G.Adj u.val)).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  obtain ⟨hzR, huz⟩ := Finset.mem_filter.mp hz
  have hadj : (G.induce (↑(K \ W) : Set V)).Adj u ⟨z, hzR⟩ := huz
  exact hadj.degree_pos_left

end StarCenter

/-- When `b ∈ K \ W` is adjacent in `G` to every vertex of `(K \ W) \ {b}`, adding
`W × K` pairs is identical to adding `(insert b W) × K` pairs. -/
theorem fillSeedPairs_insert_center_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) (K W : Finset (Fin n)) (b : Fin n)
    (hb : b ∈ K \ W) (hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x) :
    fillSeedPairs G K (insert b W) = fillSeedPairs G K W := by
  classical
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  apply le_antisymm
  · apply sup_le le_sup_left
    intro u v huv
    change (fillSeedPairs G K W).Adj u v
    obtain ⟨⟨w, hw, x, hxK, hne, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
    rcases Finset.mem_insert.mp hw with rfl | hwW
    · by_cases hxW : x ∈ W
      · have hadj : (fillSeedPairs G K W).Adj x w :=
          filled_seed_adj G K W x w hxW hbK hne.symm
        rcases Sym2.eq_iff.mp heq with h | h
        · simpa only [h.1, h.2] using (fillSeedPairs G K W).adj_symm hadj
        · simpa only [h.1, h.2] using hadj
      · have hxKW : x ∈ K \ W := Finset.mem_sdiff.mpr ⟨hxK, hxW⟩
        have hadjG : G.Adj w x := hcenter x hxKW hne.symm
        have hadj : (fillSeedPairs G K W).Adj w x :=
          (le_sup_left : G ≤ fillSeedPairs G K W) hadjG
        rcases Sym2.eq_iff.mp heq with h | h
        · simpa only [h.1, h.2] using hadj
        · simpa only [h.1, h.2] using (fillSeedPairs G K W).adj_symm hadj
    · have hadj : (fillSeedPairs G K W).Adj w x :=
        filled_seed_adj G K W w x hwW hxK hne
      rcases Sym2.eq_iff.mp heq with h | h
      · simpa only [h.1, h.2] using hadj
      · simpa only [h.1, h.2] using (fillSeedPairs G K W).adj_symm hadj
  · apply sup_le le_sup_left
    intro u v huv
    change (fillSeedPairs G K (insert b W)).Adj u v
    obtain ⟨⟨w, hwW, x, hxK, hne, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
    have hadj : (fillSeedPairs G K (insert b W)).Adj w x :=
      filled_seed_adj G K (insert b W) w x (Finset.mem_insert_of_mem hwW) hxK hne
    rcases Sym2.eq_iff.mp heq with h | h
    · simpa only [h.1, h.2] using hadj
    · simpa only [h.1, h.2] using (fillSeedPairs G K (insert b W)).adj_symm hadj

/-- Additive-guard version of `restoration_pair_guard`: no upper bound `h ≤ d` is needed. -/
theorem restoration_pair_guard_additive {d h : ℕ}
    (G J : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (w x : Fin (2 * d + 2))
    (hlow : 3 ≤ h) (horder : K.card = d + h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d + 2 ≤ G.degree x + h) :
    2 * d + 2 - 1 ≤ J.degree w + J.degree x := by
  have hGJ : G ≤ J := le_trans le_sup_left hfill
  have hwdegree := seed_fill_degree_lower G J K W w hw (hWK hw) hfill
  rw [horder] at hwdegree
  have hxdegree : G.degree x ≤ J.degree x := G.degree_le_of_le (v := x) hGJ
  omega

/-- An edge outside a size-`d` universal set `H` (`3 ≤ d`) extends to a spanning `P_{2d+2}`. -/
theorem spanning_path_of_residual_edge_ge_three {d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 2))) (H : Finset (Fin (2 * d + 2)))
    (hHcard : H.card = d)
    (huniv : ∀ h ∈ H, ∀ x, h ≠ x → G.Adj h x)
    (u v : Fin (2 * d + 2)) (hu : u ∉ H) (hv : v ∉ H)
    (hEdge : G.Adj u v) : (pathGraph (2 * d + 2)).IsContained G := by
  classical
  have huv : u ≠ v := hEdge.ne
  obtain ⟨h0, hh0⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  let W : Finset (Fin (2 * d + 2)) := H.erase h0
  have hWcard : W.card = d - 1 := by
    dsimp only [W]
    rw [Finset.card_erase_of_mem hh0, hHcard]
  have hWuniv : ∀ w ∈ W, ∀ x, w ≠ x → G.Adj w x := by
    intro w hw x hne
    exact huniv w (Finset.mem_erase.mp hw).2 x hne
  let R : Finset (Fin (2 * d + 2)) := Finset.univ \ H
  have hRcard : R.card = d + 2 := by
    dsimp only [R]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hHcard]
    omega
  have huR : u ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩
  have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
  have hvErase : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvR⟩
  let T : Finset (Fin (2 * d + 2)) := (R.erase u).erase v
  have hTcard : T.card = d := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hvErase, Finset.card_erase_of_mem huR, hRcard]
    omega
  obtain ⟨z, hzT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hzv : z ≠ v := (Finset.mem_erase.mp hzT).1
  have hzEu : z ∈ R.erase u := (Finset.mem_erase.mp hzT).2
  have hzu : z ≠ u := (Finset.mem_erase.mp hzEu).1
  have hzR : z ∈ R := (Finset.mem_erase.mp hzEu).2
  have hzH : z ∉ H := (Finset.mem_sdiff.mp hzR).2
  have huh0 : u ≠ h0 := fun he => hu (he.symm ▸ hh0)
  have hvh0 : v ≠ h0 := fun he => hv (he.symm ▸ hh0)
  have hzh0 : z ≠ h0 := fun he => hzH (he.symm ▸ hh0)
  let p : Fin 4 → Fin (2 * d + 2) := ![u, v, h0, z]
  have hpinj : Function.Injective p := by
    intro i j he
    fin_cases i <;> fin_cases j <;>
      simp [p, huv, huv.symm, huh0, huh0.symm, hzu, hzu.symm,
        hvh0, hvh0.symm, hzv, hzv.symm, hzh0, hzh0.symm] at he ⊢
  have hpnotW : ∀ i : Fin 4, p i ∉ W := by
    intro i
    fin_cases i <;> simp [p, W, hu, hv, hzH]
  have hpadj : ∀ (i j : Fin 4), i.val + 1 = j.val → G.Adj (p i) (p j) := by
    have h12 : G.Adj v h0 := (huniv h0 hh0 v hvh0.symm).symm
    have h23 : G.Adj h0 z := huniv h0 hh0 z hzh0.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  exact spanning_path_of_residual_path (by omega) (by omega) G W hWcard hWuniv
    p hpinj hpnotW hpadj

/-- Additive-guard single restoration step. -/
theorem path_free_after_missing_restoration_pair_additive {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h) (G J : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (w x : Fin (2 * d + 2))
    (horder : K.card = d + h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hx : x ∉ K)
    (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free J) (hmissing : ¬ J.Adj w x) :
    (pathGraph (2 * d + 2)).Free
      (ErdosProblems.PathSpanningNonedgeDeficit.augment J w x) := by
  have hne : w ≠ x := fun heq => hx (heq ▸ hWK hw)
  exact GenericPathMissingPairClosure1105.pathGraph_free_after_adding_missing_pair
    (by omega) J hfree w x hne hmissing
    (restoration_pair_guard_additive G J K W w x hlow horder hWK hw hfill hpeeled)

/-- Additive-guard two-phase seed-first path filling on `Fin (2*d+2)`, valid for all `h ≥ 3`. -/
theorem seed_first_path_free_additive {d h : ℕ} (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (horder : K.card = d + h) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    (pathGraph (2 * d + 2)).Free (seedFirstFilled G K W) ∧
      G ≤ seedFirstFilled G K W ∧
      (∀ w ∈ W, ∀ v, w ≠ v → (seedFirstFilled G K W).Adj w v) ∧
      (∀ u, u ∉ W → ∀ v, v ∉ W →
        ((seedFirstFilled G K W).Adj u v ↔ G.Adj u v)) := by
  classical
  have hfirst : (pathGraph (2 * d + 2)).Free (seedFilled G K W) := by
    have haux : ∀ L : List (Fin (2 * d + 2) × Fin (2 * d + 2)),
        (∀ p ∈ L, p ∈ seedPairs K W) →
        ∀ J : SimpleGraph (Fin (2 * d + 2)), G ≤ J →
          (pathGraph (2 * d + 2)).Free J →
          (pathGraph (2 * d + 2)).Free (fillOrdered J L) := by
      intro L
      induction L with
      | nil => intro _ J _ hfreeJ; exact hfreeJ
      | cons p ps ih =>
          intro hmem J hGJ hfreeJ
          have hp : p ∈ seedPairs K W := hmem p (by simp)
          simp only [seedPairs, Finset.mem_filter, Finset.mem_product] at hp
          obtain ⟨⟨hw, hv⟩, hne⟩ := hp
          have hstep : (pathGraph (2 * d + 2)).Free
              (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2) := by
            by_cases hadj : J.Adj p.1 p.2
            · have heq : ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2 = J := by
                apply le_antisymm _ le_sup_left
                apply sup_le le_rfl
                intro x y hxy
                obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
                rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair) with h | h
                · simpa only [h.1, h.2] using hadj
                · simpa only [h.1, h.2] using J.adj_symm hadj
              simpa only [heq] using hfreeJ
            · exact GenericPathMissingPairClosure1105.pathGraph_free_after_adding_missing_pair
                (by omega) J hfreeJ p.1 p.2 hne hadj
                (seed_pair_guard G J K p.1 p.2 hGJ (hhigh p.1 hw) (hmin p.2 hv))
          exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
            (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2)
            (le_trans hGJ le_sup_left) hstep
    exact haux (seedPairs K W).toList (fun p hp => Finset.mem_toList.mp hp) G le_rfl hfree
  have hsecond : (pathGraph (2 * d + 2)).Free (seedFirstFilled G K W) := by
    have haux : ∀ L : List (Fin (2 * d + 2) × Fin (2 * d + 2)),
        (∀ p ∈ L, p ∈ restoredPairs K W) →
        ∀ J : SimpleGraph (Fin (2 * d + 2)), seedFilled G K W ≤ J →
          (pathGraph (2 * d + 2)).Free J →
          (pathGraph (2 * d + 2)).Free (fillOrdered J L) := by
      intro L
      induction L with
      | nil => intro _ J _ hfreeJ; exact hfreeJ
      | cons p ps ih =>
          intro hmem J hseedJ hfreeJ
          have hp : p ∈ restoredPairs K W := hmem p (by simp)
          simp only [restoredPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
          obtain ⟨⟨hw, hx⟩, _hne⟩ := hp
          have hfill : fillSeedPairs G K W ≤ J := by
            rw [← seedFilled_eq]
            exact hseedJ
          have hstep : (pathGraph (2 * d + 2)).Free
              (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2) := by
            by_cases hadj : J.Adj p.1 p.2
            · have heq : ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2 = J := by
                apply le_antisymm _ le_sup_left
                apply sup_le le_rfl
                intro x y hxy
                obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
                rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair) with h | h
                · simpa only [h.1, h.2] using hadj
                · simpa only [h.1, h.2] using J.adj_symm hadj
              simpa only [heq] using hfreeJ
            · exact path_free_after_missing_restoration_pair_additive hd hlow G J K W p.1 p.2
                horder hWK hw hx hfill (hrestored p.2 hx) hfreeJ hadj
          exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
            (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2)
            (le_trans hseedJ le_sup_left) hstep
    exact haux (restoredPairs K W).toList (fun p hp => Finset.mem_toList.mp hp)
      (seedFilled G K W) le_rfl hfirst
  refine ⟨hsecond, le_trans (le_fillOrdered G _) (le_fillOrdered (seedFilled G K W) _), ?_, ?_⟩
  · intro w hw v hne
    rw [seedFirstFilled_eq]
    exact filled_seed_adj G Finset.univ W w v hw (Finset.mem_univ v) hne
  · intro u hu v hv
    exact residual_original G K W u v hu hv

/-- Additive-guard residual forest exclusions on any finite carrier of size `2*d+2`. -/
theorem original_residual_forest_free_of_finite_carrier_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph V) (hcard : Fintype.card V = 2 * d + 2)
    (K W : Finset V)
    (horder : K.card = d + h) (hW : W.card = d - 1) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ (K.filter (G.Adj v)).card)
    (hhigh : ∀ w ∈ W, d + 1 ≤ (K.filter (G.Adj w)).card)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    (∀ p : Fin 4 → V, Function.Injective p → (∀ i, p i ∈ K ∧ p i ∉ W) →
      G.Adj (p 0) (p 1) → G.Adj (p 1) (p 2) → G.Adj (p 2) (p 3) → False) ∧
    (∀ p : Fin 5 → V, Function.Injective p → (∀ i, p i ∈ K ∧ p i ∉ W) →
      G.Adj (p 0) (p 1) → G.Adj (p 1) (p 2) → G.Adj (p 3) (p 4) → False) ∧
    (∀ p : Fin 6 → V, Function.Injective p → (∀ i, p i ∈ K ∧ p i ∉ W) →
      G.Adj (p 0) (p 1) → G.Adj (p 2) (p 3) → G.Adj (p 4) (p 5) → False) := by
  classical
  let J : SimpleGraph (Fin (2 * d + 2)) := G.overFin hcard
  let e : G ≃g J := G.overFinIso hcard
  let Kf : Finset (Fin (2 * d + 2)) := K.map e.toEquiv.toEmbedding
  let Wf : Finset (Fin (2 * d + 2)) := W.map e.toEquiv.toEmbedding
  have hKcard : Kf.card = d + h := by simpa only [Kf, Finset.card_map] using horder
  have hWcard : Wf.card = d - 1 := by simpa only [Wf, Finset.card_map] using hW
  have hWKf : Wf ⊆ Kf := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨u, hWK hu, rfl⟩
  have hseed (u : V) :
      originalSeedDegree J Kf (e u) = (K.filter (G.Adj u)).card := by
    change ((K.map e.toEquiv.toEmbedding).filter (J.Adj (e u))).card =
      (K.filter (G.Adj u)).card
    rw [Finset.filter_map]
    change ((K.filter (fun v => J.Adj (e u) (e v))).map
      e.toEquiv.toEmbedding).card = (K.filter (G.Adj u)).card
    have hfilters : K.filter (fun v => J.Adj (e u) (e v)) =
        K.filter (G.Adj u) := by
      ext v
      simp only [Finset.mem_filter, e.map_adj_iff]
    rw [hfilters, Finset.card_map]
  have hminf : ∀ z ∈ Kf, d ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hmin u hu
  have hhighf : ∀ z ∈ Wf, d + 1 ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hhigh u hu
  have hrestf : ∀ z, z ∉ Kf → d + 2 ≤ J.degree z + h := by
    intro z hz
    have hnot : e.symm z ∉ K := by
      intro hm
      apply hz
      exact Finset.mem_map.mpr ⟨e.symm z, hm, e.apply_symm_apply z⟩
    have hdeg := e.degree_eq (e.symm z)
    rw [e.apply_symm_apply] at hdeg
    rw [hdeg]
    exact hrestored (e.symm z) hnot
  have hfreef : (pathGraph (2 * d + 2)).Free J :=
    (SimpleGraph.free_congr_right e).mp hfree
  obtain ⟨hFfree, hJF, hWuniv, _houtside⟩ :=
    seed_first_path_free_additive hd hlow J Kf Wf hKcard hWKf hminf hhighf hrestf hfreef
  let F := seedFirstFilled J Kf Wf
  refine ⟨?_, ?_, ?_⟩
  · intro p hpinj hpKW h01 h12 h23
    let pf : Fin 4 → Fin (2 * d + 2) := fun i => e (p i)
    have hpfinj : Function.Injective pf := e.injective.comp hpinj
    have hpfnotW : ∀ i : Fin 4, pf i ∉ Wf := by
      intro i hmem
      obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hmem
      change e u = e (p i) at he
      exact (hpKW i).2 ((e.injective he) ▸ huW)
    have hf01 : F.Adj (pf 0) (pf 1) := hJF (e.map_adj_iff.mpr h01)
    have hf12 : F.Adj (pf 1) (pf 2) := hJF (e.map_adj_iff.mpr h12)
    have hf23 : F.Adj (pf 2) (pf 3) := hJF (e.map_adj_iff.mpr h23)
    have hpadj : ∀ (i j : Fin 4), i.val + 1 = j.val → F.Adj (pf i) (pf j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    exact hFfree (spanning_path_of_residual_path (by omega) (by omega)
      F Wf hWcard hWuniv pf hpfinj hpfnotW hpadj)
  · intro p hpinj hpKW h01 h12 h34
    let pf : Fin 5 → Fin (2 * d + 2) := fun i => e (p i)
    have hpfinj : Function.Injective pf := e.injective.comp hpinj
    have hpfnotW : ∀ i : Fin 5, pf i ∉ Wf := by
      intro i hmem
      obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hmem
      change e u = e (p i) at he
      exact (hpKW i).2 ((e.injective he) ▸ huW)
    have hf01 : F.Adj (pf 0) (pf 1) := hJF (e.map_adj_iff.mpr h01)
    have hf12 : F.Adj (pf 1) (pf 2) := hJF (e.map_adj_iff.mpr h12)
    have hf34 : F.Adj (pf 3) (pf 4) := hJF (e.map_adj_iff.mpr h34)
    exact hFfree (spanning_path_of_residual_p3_p2 hd F Wf hWcard hWuniv
      pf hpfinj hpfnotW hf01 hf12 hf34)
  · intro p hpinj hpKW h01 h23 h45
    let pf : Fin 6 → Fin (2 * d + 2) := fun i => e (p i)
    have hpfinj : Function.Injective pf := e.injective.comp hpinj
    have hpfnotW : ∀ i : Fin 6, pf i ∉ Wf := by
      intro i hmem
      obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hmem
      change e u = e (p i) at he
      exact (hpKW i).2 ((e.injective he) ▸ huW)
    have hf01 : F.Adj (pf 0) (pf 1) := hJF (e.map_adj_iff.mpr h01)
    have hf23 : F.Adj (pf 2) (pf 3) := hJF (e.map_adj_iff.mpr h23)
    have hf45 : F.Adj (pf 4) (pf 5) := hJF (e.map_adj_iff.mpr h45)
    exact hFfree (spanning_path_of_residual_3p2 hd F Wf hWcard hWuniv
      pf hpfinj hpfnotW hf01 hf23 hf45)

/-- Actual-carrier wrapper for all three linear forest exclusions under the additive guard. -/
theorem original_residual_forest_free_of_actual_carrier_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (H : SimpleGraph V) (D K W : Finset V)
    (hDcard : D.card = 2 * d + 2) (hKD : K ⊆ D) (hWK : W ⊆ K)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1)
    (hmin : ∀ v ∈ K, d ≤ withinDegree H K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ withinDegree H K w)
    (hrestored : ∀ x ∈ D, x ∉ K → d + 2 ≤ withinDegree H D x + h)
    (hfree : (pathGraph (2 * d + 2)).Free H) :
    (pathGraph 4).Free (H.induce (↑(K \ W) : Set V)) ∧
      NoP3AndP2 (H.induce (↑(K \ W) : Set V)) ∧
      NoThreeP2 (H.induce (↑(K \ W) : Set V)) := by
  let J : SimpleGraph (↑D : Set V) := H.induce (↑D : Set V)
  let KD : Finset (↑D : Set V) := K.subtype (fun x => x ∈ D)
  let WD : Finset (↑D : Set V) := W.subtype (fun x => x ∈ D)
  have hDtype : Fintype.card (↑D : Set V) = 2 * d + 2 := by
    have hc : Fintype.card (↑D : Set V) = D.card :=
      Fintype.card_of_finset' (p := (↑D : Set V)) D (fun _ => Iff.rfl)
    exact hc.trans hDcard
  have hKDmap : KD.map (Function.Embedding.subtype _) = K :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD hx)
  have hWDmap : WD.map (Function.Embedding.subtype _) = W :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD (hWK hx))
  have hKDcard : KD.card = d + h := by
    have hc := congrArg Finset.card hKDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hKcard
  have hWDcard : WD.card = d - 1 := by
    have hc := congrArg Finset.card hWDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hWcard
  have hWKD : WD ⊆ KD := by
    intro u hu
    exact Finset.mem_subtype.mpr (hWK (Finset.mem_subtype.mp hu))
  have hseed (u : (↑D : Set V)) :
      (KD.filter (J.Adj u)).card = withinDegree H K u.val := by
    change (KD.filter (J.Adj u)).card = (K.filter (H.Adj u.val)).card
    have hf : (KD.filter (J.Adj u)).map (Function.Embedding.subtype _) =
        K.filter (H.Adj u.val) := by
      rw [← hKDmap, Finset.filter_map]
      rfl
    have hc := congrArg Finset.card hf
    simpa only [Finset.card_map] using hc
  have hminD : ∀ u ∈ KD, d ≤ (KD.filter (J.Adj u)).card := by
    intro u hu
    rw [hseed u]
    exact hmin u.val (Finset.mem_subtype.mp hu)
  have hhighD : ∀ u ∈ WD, d + 1 ≤ (KD.filter (J.Adj u)).card := by
    intro u hu
    rw [hseed u]
    exact hhigh u.val (Finset.mem_subtype.mp hu)
  have hrestoredD : ∀ u, u ∉ KD → d + 2 ≤ J.degree u + h := by
    intro u hu
    have hdeg := ActualInducedDegree1105.degree_induce_eq_withinDegree H D u
    change J.degree u = withinDegree H D u.val at hdeg
    rw [hdeg]
    apply hrestored u.val u.property
    intro huK
    exact hu (Finset.mem_subtype.mpr huK)
  have hfreeD : (pathGraph (2 * d + 2)).Free J := by
    intro hp
    obtain ⟨P⟩ := hp
    let E : J.Copy H := (SimpleGraph.Embedding.induce (↑D : Set V)).toCopy
    exact hfree ⟨E.comp P⟩
  obtain ⟨hP4D, hP3P2D, h3P2D⟩ :=
    original_residual_forest_free_of_finite_carrier_additive
      hd hlow J hDtype KD WD hKDcard hWDcard hWKD
      hminD hhighD hrestoredD hfreeD
  let lift : (↑(K \ W) : Set V) → (↑D : Set V) := fun u =>
    ⟨u.val, hKD (Finset.mem_sdiff.mp u.property).1⟩
  have hliftInj : Function.Injective lift := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun z : (↑D : Set V) => z.val) huv
  have hliftKW (u : (↑(K \ W) : Set V)) : lift u ∈ KD ∧ lift u ∉ WD := by
    obtain ⟨huK, huW⟩ := Finset.mem_sdiff.mp u.property
    exact ⟨Finset.mem_subtype.mpr (by change (lift u).val ∈ K; exact huK),
      fun h => huW (Finset.mem_subtype.mp h : (lift u).val ∈ W)⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨P⟩
    have h01 : (pathGraph 4).Adj 0 1 := pathGraph_adj.mpr (Or.inl rfl)
    have h12 : (pathGraph 4).Adj 1 2 := pathGraph_adj.mpr (Or.inl rfl)
    have h23 : (pathGraph 4).Adj 2 3 := pathGraph_adj.mpr (Or.inl rfl)
    exact hP4D (lift ∘ P) (hliftInj.comp P.injective) (fun i => hliftKW (P i))
      (P.toHom.map_rel' h01) (P.toHom.map_rel' h12) (P.toHom.map_rel' h23)
  · intro p hpinj h01 h12 h34
    exact hP3P2D (lift ∘ p) (hliftInj.comp hpinj) (fun i => hliftKW (p i)) h01 h12 h34
  · intro p hpinj h01 h23 h45
    exact h3P2D (lift ∘ p) (hliftInj.comp hpinj) (fun i => hliftKW (p i)) h01 h23 h45

section StarCenterAdditive

local instance (priority := 3000) subtypeNeighborSetFintypeAdditive {A : Type*} [Fintype A]
    (G : SimpleGraph A) [DecidableRel G.Adj] (x : A) : Fintype (G.neighborSet x) :=
  Subtype.fintype (Membership.mem (G.neighborSet x))

/-- For any `h ≥ 4` (including `h = d + 1` and `h = d + 2`), if `K` fits inside a
carrier `D` of size `2*d+2` with the additive restored-degree guard, `G.induce (K \ W)`
is a spanning star with center `b ∈ K \ W`. -/
theorem exists_residual_star_center_of_carrier_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 4 ≤ h)
    (G : SimpleGraph V) (D K W : Finset V)
    (hDcard : D.card = 2 * d + 2) (hKD : K ⊆ D) (hWK : W ⊆ K)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1)
    (hmin : ∀ v ∈ K, d ≤ withinDegree G K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ withinDegree G K w)
    (hrestored : ∀ x ∈ D, x ∉ K → d + 2 ≤ withinDegree G D x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∃ b ∈ K \ W,
      (∀ x ∈ K \ W, x ≠ b → G.Adj b x) ∧
      (∀ x ∈ K \ W, x ≠ b → ∀ y ∈ K \ W, y ≠ b → ¬ G.Adj x y) := by
  let R := G.induce (↑(K \ W) : Set V)
  have hKWcard : (K \ W).card = h + 1 := by
    rw [Finset.card_sdiff_of_subset hWK, hKcard, hWcard]
    omega
  have hRcard : 5 ≤ Fintype.card (↑(K \ W) : Set V) := by
    have hc : Fintype.card (↑(K \ W) : Set V) = (K \ W).card :=
      Fintype.card_of_finset' (p := (↑(K \ W) : Set V)) (K \ W) (fun _ => Iff.rfl)
    omega
  have hRmin := residual_min_degree_one G d K W (by omega) hWcard hmin
  obtain ⟨hP4, hP3P2, h3P2⟩ :=
    original_residual_forest_free_of_actual_carrier_additive
      hd (by omega) G D K W hDcard hKD hWK hKcard hWcard hmin hhigh hrestored hfree
  obtain ⟨b, hcenter, hleaves, _hcover⟩ :=
    exists_center_of_min_degree_and_no_three_edge_linear_forest
      R hRcard hRmin hP4 hP3P2 h3P2
  refine ⟨b.val, b.property, ?_, ?_⟩
  · intro x hx hxb
    have hne : (⟨x, hx⟩ : (↑(K \ W) : Set V)) ≠ b := fun he => hxb (congrArg Subtype.val he)
    exact hcenter ⟨x, hx⟩ hne
  · intro x hx hxb y hy hyb
    have hnex : (⟨x, hx⟩ : (↑(K \ W) : Set V)) ≠ b := fun he => hxb (congrArg Subtype.val he)
    have hney : (⟨y, hy⟩ : (↑(K \ W) : Set V)) ≠ b := fun he => hyb (congrArg Subtype.val he)
    exact hleaves ⟨x, hx⟩ hnex ⟨y, hy⟩ hney

end StarCenterAdditive

/-- Additive-guard version of `finite_carrier_cover_of_star_center`. -/
theorem finite_carrier_cover_of_star_center_additive {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph (Fin (2 * d + 2)))
    (K W : Finset (Fin (2 * d + 2))) (b : Fin (2 * d + 2))
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hb : b ∈ K \ W) (hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d + 1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∀ u v, G.Adj u v → u ∈ insert b W ∨ v ∈ insert b W := by
  classical
  let H : Finset (Fin (2 * d + 2)) := insert b W
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  have hHK : H ⊆ K := Finset.insert_subset_iff.mpr ⟨hbK, hWK⟩
  have hHcard : H.card = d := by
    dsimp [H]
    rw [Finset.card_insert_of_notMem hbW, hWcard]
    omega
  obtain ⟨hFilledFreeW, _hGW, _hWuniv, _hWres⟩ :=
    seed_first_path_free_additive hd hlow G K W hKcard hWK hmin hhigh hrestored hfree
  have hseedEq : seedFilled G K H = seedFilled G K W := by
    rw [seedFilled_eq, seedFilled_eq]
    exact fillSeedPairs_insert_center_eq G K W b hb hcenter
  have hfirstW : (pathGraph (2 * d + 2)).Free (seedFilled G K W) := by
    intro hp
    obtain ⟨P⟩ := hp
    have hle : seedFilled G K W ≤ seedFirstFilled G K W :=
      le_fillOrdered (seedFilled G K W) (restoredPairs K W).toList
    exact hFilledFreeW ⟨(SimpleGraph.Copy.ofLE _ _ hle).comp P⟩
  have hfirstH : (pathGraph (2 * d + 2)).Free (seedFilled G K H) := by
    rw [hseedEq]
    exact hfirstW
  have hsecondH : (pathGraph (2 * d + 2)).Free (seedFirstFilled G K H) := by
    have haux : ∀ L : List (Fin (2 * d + 2) × Fin (2 * d + 2)),
        (∀ p ∈ L, p ∈ restoredPairs K H) →
        ∀ J : SimpleGraph (Fin (2 * d + 2)), seedFilled G K H ≤ J →
          (pathGraph (2 * d + 2)).Free J →
          (pathGraph (2 * d + 2)).Free (fillOrdered J L) := by
      intro L
      induction L with
      | nil => intro _ J _ hfreeJ; exact hfreeJ
      | cons p ps ih =>
          intro hmem J hHJ hfreeJ
          have hp : p ∈ restoredPairs K H := hmem p (by simp)
          simp only [restoredPairs, Finset.mem_filter, Finset.mem_product,
            Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
          obtain ⟨⟨hp1H, hp2notK⟩, _hne⟩ := hp
          have hfill : fillSeedPairs G K H ≤ J := by
            rw [← seedFilled_eq]
            exact hHJ
          have hstep : (pathGraph (2 * d + 2)).Free
              (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2) := by
            by_cases hadj : J.Adj p.1 p.2
            · have heq : ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2 = J := by
                apply le_antisymm _ le_sup_left
                apply sup_le le_rfl
                intro x y hxy
                obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
                rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair) with h | h
                · simpa only [h.1, h.2] using hadj
                · simpa only [h.1, h.2] using J.adj_symm hadj
              simpa only [heq] using hfreeJ
            · exact path_free_after_missing_restoration_pair_additive hd hlow G J K H p.1 p.2
                hKcard hHK hp1H hp2notK hfill (hrestored p.2 hp2notK) hfreeJ hadj
          exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
            (ErdosProblems.PathSpanningNonedgeDeficit.augment J p.1 p.2)
            (le_trans hHJ le_sup_left) hstep
    exact haux (restoredPairs K H).toList (fun p hp => Finset.mem_toList.mp hp)
      (seedFilled G K H) le_rfl hfirstH
  have hHuniv : ∀ w ∈ H, ∀ v, w ≠ v → (seedFirstFilled G K H).Adj w v := by
    intro w hw v hne
    rw [seedFirstFilled_eq]
    exact filled_seed_adj G Finset.univ H w v hw (Finset.mem_univ v) hne
  intro u v huv
  by_cases hu : u ∈ H
  · exact Or.inl hu
  by_cases hv : v ∈ H
  · exact Or.inr hv
  have hFilledEdge : (seedFirstFilled G K H).Adj u v :=
    (residual_original G K H u v hu hv).mpr huv
  exact False.elim (hsecondH (spanning_path_of_residual_edge_ge_three hd
    (seedFirstFilled G K H) H hHcard hHuniv u v hu hv hFilledEdge))

/-- Additive-guard transport over any finite type `V` of size `2*d+2`. -/
theorem finite_carrier_cover_of_star_center_over_fintype_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph V) (hcard : Fintype.card V = 2 * d + 2)
    (K W : Finset V) (b : V)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hb : b ∈ K ∧ b ∉ W) (hcenter : ∀ x ∈ K, x ∉ W → x ≠ b → G.Adj b x)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (hrestored : ∀ x, x ∉ K → d + 2 ≤ G.degree x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∀ x y, G.Adj x y → (x = b ∨ x ∈ W) ∨ (y = b ∨ y ∈ W) := by
  classical
  let J : SimpleGraph (Fin (2 * d + 2)) := G.overFin hcard
  let e : G ≃g J := G.overFinIso hcard
  let Kf : Finset (Fin (2 * d + 2)) := K.map e.toEquiv.toEmbedding
  let Wf : Finset (Fin (2 * d + 2)) := W.map e.toEquiv.toEmbedding
  let bf : Fin (2 * d + 2) := e b
  have hKcardf : Kf.card = d + h := by simpa only [Kf, Finset.card_map] using hKcard
  have hWcardf : Wf.card = d - 1 := by simpa only [Wf, Finset.card_map] using hWcard
  have hWKf : Wf ⊆ Kf := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨u, hWK hu, rfl⟩
  have hbf : bf ∈ Kf \ Wf := by
    obtain ⟨hbK, hbW⟩ := hb
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_map.mpr ⟨b, hbK, rfl⟩, ?_⟩
    intro hm
    obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hm
    change e u = e b at he
    exact hbW ((e.injective he) ▸ huW)
  have hcenterf : ∀ z ∈ Kf \ Wf, z ≠ bf → J.Adj bf z := by
    intro z hz hne
    obtain ⟨hzK, hzW⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨u, huK, rfl⟩ := Finset.mem_map.mp hzK
    have huW : u ∉ W := fun h => hzW (Finset.mem_map.mpr ⟨u, h, rfl⟩)
    have hub : u ≠ b := fun h => hne (congrArg e h)
    exact e.map_adj_iff.mpr (hcenter u huK huW hub)
  have hseed (u : V) :
      originalSeedDegree J Kf (e u) = withinDegree G K u := by
    change ((K.map e.toEquiv.toEmbedding).filter (J.Adj (e u))).card =
      (K.filter (G.Adj u)).card
    rw [Finset.filter_map]
    change ((K.filter (fun v => J.Adj (e u) (e v))).map
      e.toEquiv.toEmbedding).card = (K.filter (G.Adj u)).card
    have hfilters : K.filter (fun v => J.Adj (e u) (e v)) =
        K.filter (G.Adj u) := by
      ext v
      simp only [Finset.mem_filter, e.map_adj_iff]
    rw [hfilters, Finset.card_map]
  have hminf : ∀ z ∈ Kf, d ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hmin u hu
  have hhighf : ∀ z ∈ Wf, d + 1 ≤ originalSeedDegree J Kf z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hz
    change e u = z at he
    rw [← he, hseed u]
    exact hhigh u hu
  have hrestf : ∀ z, z ∉ Kf → d + 2 ≤ J.degree z + h := by
    intro z hz
    have hnot : e.symm z ∉ K := by
      intro hm
      apply hz
      exact Finset.mem_map.mpr ⟨e.symm z, hm, e.apply_symm_apply z⟩
    have hdeg := e.degree_eq (e.symm z)
    rw [e.apply_symm_apply] at hdeg
    rw [hdeg]
    exact hrestored (e.symm z) hnot
  have hfreef : (pathGraph (2 * d + 2)).Free J :=
    (SimpleGraph.free_congr_right e).mp hfree
  have hcover := finite_carrier_cover_of_star_center_additive hd hlow J Kf Wf bf
    hKcardf hWcardf hWKf hbf hcenterf hminf hhighf hrestf hfreef
  intro x y hxy
  have hxyf : J.Adj (e x) (e y) := e.map_adj_iff.mpr hxy
  rcases hcover (e x) (e y) hxyf with hx | hy
  · rcases Finset.mem_insert.mp hx with hxb | hxW
    · exact Or.inl (Or.inl (e.injective hxb))
    · obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hxW
      change e u = e x at he
      exact Or.inl (Or.inr ((e.injective he) ▸ huW))
  · rcases Finset.mem_insert.mp hy with hyb | hyW
    · exact Or.inr (Or.inl (e.injective hyb))
    · obtain ⟨u, huW, he⟩ := Finset.mem_map.mp hyW
      change e u = e y at he
      exact Or.inr (Or.inr ((e.injective he) ▸ huW))

/-- Additive-guard actual-carrier cover: valid for all `h ≥ 3`, including `h = d + 1`
(`|K| = 2*d+1`) and `h = d + 2` (`|K| = 2*d+2`). -/
theorem actual_carrier_cover_of_star_center_additive
    {V : Type*} [Fintype V] {d h : ℕ}
    (hd : 3 ≤ d) (hlow : 3 ≤ h)
    (G : SimpleGraph V) (D K W : Finset V) (b : V)
    (hDcard : D.card = 2 * d + 2) (hKD : K ⊆ D) (hWK : W ⊆ K)
    (hKcard : K.card = d + h) (hWcard : W.card = d - 1)
    (hb : b ∈ K \ W) (hcenter : ∀ x ∈ K \ W, x ≠ b → G.Adj b x)
    (hmin : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hhigh : ∀ x ∈ W, d + 1 ≤ withinDegree G K x)
    (hrestored : ∀ x ∈ D, x ∉ K → d + 2 ≤ withinDegree G D x + h)
    (hfree : (pathGraph (2 * d + 2)).Free G) :
    ∀ x ∈ D, ∀ y ∈ D, G.Adj x y → x ∈ insert b W ∨ y ∈ insert b W := by
  let J : SimpleGraph (↑D : Set V) := G.induce (↑D : Set V)
  let KD : Finset (↑D : Set V) := K.subtype (fun x => x ∈ D)
  let WD : Finset (↑D : Set V) := W.subtype (fun x => x ∈ D)
  have hbK : b ∈ K := (Finset.mem_sdiff.mp hb).1
  have hbW : b ∉ W := (Finset.mem_sdiff.mp hb).2
  let bD : (↑D : Set V) := ⟨b, hKD hbK⟩
  have hDtype : Fintype.card (↑D : Set V) = 2 * d + 2 := by
    have hc : Fintype.card (↑D : Set V) = D.card :=
      Fintype.card_of_finset' (p := (↑D : Set V)) D (fun _ => Iff.rfl)
    exact hc.trans hDcard
  have hKDmap : KD.map (Function.Embedding.subtype _) = K :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD hx)
  have hWDmap : WD.map (Function.Embedding.subtype _) = W :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ D) (fun _ hx => hKD (hWK hx))
  have hKDcard : KD.card = d + h := by
    have hc := congrArg Finset.card hKDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hKcard
  have hWDcard : WD.card = d - 1 := by
    have hc := congrArg Finset.card hWDmap
    simp only [Finset.card_map] at hc
    exact hc.trans hWcard
  have hWKD : WD ⊆ KD := by
    intro u hu
    exact Finset.mem_subtype.mpr (hWK (Finset.mem_subtype.mp hu))
  have hbD : bD ∈ KD ∧ bD ∉ WD :=
    ⟨Finset.mem_subtype.mpr hbK, fun hm => hbW (Finset.mem_subtype.mp hm : bD.val ∈ W)⟩
  have hcenterD : ∀ u ∈ KD, u ∉ WD → u ≠ bD → J.Adj bD u := by
    intro u huK huW hne
    have huK' : u.val ∈ K := Finset.mem_subtype.mp huK
    have huW' : u.val ∉ W := fun h => huW (Finset.mem_subtype.mpr h)
    have hub : u.val ≠ b := fun h => hne (Subtype.ext h)
    exact hcenter u.val (Finset.mem_sdiff.mpr ⟨huK', huW'⟩) hub
  have hseed (u : (↑D : Set V)) :
      withinDegree J KD u = withinDegree G K u.val := by
    change (KD.filter (J.Adj u)).card = (K.filter (G.Adj u.val)).card
    have hf : (KD.filter (J.Adj u)).map (Function.Embedding.subtype _) =
        K.filter (G.Adj u.val) := by
      rw [← hKDmap, Finset.filter_map]
      rfl
    have hc := congrArg Finset.card hf
    simpa only [Finset.card_map] using hc
  have hminD : ∀ u ∈ KD, d ≤ withinDegree J KD u := by
    intro u hu
    rw [hseed u]
    exact hmin u.val (Finset.mem_subtype.mp hu)
  have hhighD : ∀ u ∈ WD, d + 1 ≤ withinDegree J KD u := by
    intro u hu
    rw [hseed u]
    exact hhigh u.val (Finset.mem_subtype.mp hu)
  have hrestoredD : ∀ u, u ∉ KD → d + 2 ≤ J.degree u + h := by
    intro u hu
    have hdeg := ActualInducedDegree1105.degree_induce_eq_withinDegree G D u
    change J.degree u = withinDegree G D u.val at hdeg
    rw [hdeg]
    apply hrestored u.val u.property
    intro huK
    exact hu (Finset.mem_subtype.mpr huK)
  have hfreeD : (pathGraph (2 * d + 2)).Free J := by
    intro hp
    obtain ⟨P⟩ := hp
    let E : J.Copy G := (SimpleGraph.Embedding.induce (↑D : Set V)).toCopy
    exact hfree ⟨E.comp P⟩
  have hcover := finite_carrier_cover_of_star_center_over_fintype_additive hd hlow
    J hDtype KD WD bD hKDcard hWDcard hWKD hbD hcenterD hminD hhighD hrestoredD hfreeD
  intro x hx y hy hxy
  have hxyD : J.Adj (⟨x, hx⟩ : (↑D : Set V)) ⟨y, hy⟩ := hxy
  rcases hcover ⟨x, hx⟩ ⟨y, hy⟩ hxyD with hxH | hyH
  · rcases hxH with hxb | hxW
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hxb)))
    · exact Or.inl (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_subtype.mp hxW : (⟨x, hx⟩ : (↑D : Set V)).val ∈ W)))
  · rcases hyH with hyb | hyW
    · exact Or.inr (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hyb)))
    · exact Or.inr (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_subtype.mp hyW : (⟨y, hy⟩ : (↑D : Set V)).val ∈ W)))

end ErdosProblems.PathUpperReduction.SmallKernelWholeSupport1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenOriginalOneVertexRestoration1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenFiniteCarrierAdapter1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Restore one actual vertex into the SAME ambient original graph. The old
classified carrier is legitimate induction data. The actual new degree,
anchor and ambient cycle freedom derive the enlarged block classification. -/
theorem restore_old_join_one_vertex (G : SimpleGraph V) (d : ℕ)
    (S C T : Finset V) (x a : V) (hd : 2 ≤ d)
    (hST : S ⊆ T) (hScard : S.card = d + 3)
    (hCS : C ⊆ S) (hCcard : C.card = d)
    (houtside : d ≤ (T \ S).card) (hx : x ∉ T)
    (ha : a ∈ C) (hxa : G.Adj x a)
    (hdegree : withinDegree G (insert x T) x = d)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hOldAdj : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C))) :
    ∀ u ∈ insert x T, ∀ v ∈ insert x T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)) := by
  classical
  obtain ⟨L, hLO, hLcard, _hOutsideCapture, hCapture, hWcard, hWdegree⟩ :=
    EvenRestorationSupport1105.exists_actual_restoration_support
      G d S T x a hd hST hScard houtside hx (hCS ha) hxa hdegree
  let W : Finset V := insert x (S ∪ L)
  let H : SimpleGraph (W : Set V) := G.induce (W : Set V)
  let S' := EvenInducedCarrier1105.liftSupport W S
  let C' := EvenInducedCarrier1105.liftSupport W C
  have hLT : L ⊆ T := fun y hy => (Finset.mem_sdiff.mp (hLO hy)).1
  have hSW : S ⊆ W := by
    intro y hy
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl hy))
  have hCW : C ⊆ W := hCS.trans hSW
  have hxW : x ∈ W := Finset.mem_insert_self _ _
  let x' : (W : Set V) := ⟨x, hxW⟩
  have hmemS (u : (W : Set V)) : u ∈ S' ↔ u.val ∈ S := by
    exact EvenInducedCarrier1105.mem_liftSupport W S u
  have hmemC (u : (W : Set V)) : u ∈ C' ↔ u.val ∈ C := by
    exact EvenInducedCarrier1105.mem_liftSupport W C u
  have hN : Fintype.card (W : Set V) = 2 * d + 3 := by
    exact (EvenInducedCarrier1105.induced_carrier_card W).trans hWcard
  have hS'card : S'.card = d + 3 := by
    exact (EvenInducedCarrier1105.liftSupport_card W S hSW).trans hScard
  have hC'card : C'.card = d := by
    exact (EvenInducedCarrier1105.liftSupport_card W C hCW).trans hCcard
  have hOldClique : G.IsClique (S : Set V) := by
    intro u hu v hv huv
    exact (hOldAdj u (hST hu) v (hST hv)).mpr ⟨huv, Or.inl ⟨hu, hv⟩⟩
  have hClique : H.IsClique (S' : Set (W : Set V)) :=
    EvenInducedCarrier1105.clique_lift G W S hOldClique
  have hFree : (cycleGraph (2 * d + 3)).Free H :=
    EvenInducedCarrier1105.cycle_free_induce G W (2 * d + 3) hfree
  have hOutDegree : ∀ u : (W : Set V), u ∉ S' → d ≤ H.degree u := by
    intro u huS'
    have huS : u.val ∉ S := fun hu => huS' ((hmemS u).mpr hu)
    change d ≤ (G.induce (W : Set V)).degree u
    rw [EvenInducedCarrier1105.degree_induce_eq_withinDegree G W u]
    by_cases hux : u.val = x
    · rw [hux]
      exact hWdegree.ge
    · have huL : u.val ∈ L := by
        have huW : u.val ∈ insert x (S ∪ L) := u.property
        rcases Finset.mem_insert.mp huW with hux' | huSL
        · exact False.elim (hux hux')
        · rcases Finset.mem_union.mp huSL with huS' | huL
          · exact False.elim (huS huS')
          · exact huL
      have hCN : C ⊆ W.filter (fun c => G.Adj u.val c) := by
        intro c hc
        have hcS : c ∈ S := hCS hc
        have huc : u.val ≠ c := by
          intro h
          apply huS
          rw [h]
          exact hcS
        exact Finset.mem_filter.mpr ⟨hCW hc,
          (hOldAdj u.val (hLT huL) c (hST hcS)).mpr
            ⟨huc, Or.inr (Or.inl ⟨huS, hc⟩)⟩⟩
      change d ≤ (W.filter (fun c => G.Adj u.val c)).card
      rw [← hCcard]
      exact Finset.card_le_card hCN
  have hActualLedger := EvenRestorationLedger1105.restoration_edge_ledgers
    G d S C T L x hd hST hScard hCS hCcard hOldAdj hx hLO hLcard hWdegree
  have hLedger : d * d ≤ (coreCrossEdges H S' Finset.univ).card +
      (withinEdges H (Finset.univ \ S')).card := by
    have hTransport := EvenInducedCarrier1105.suffix_ledger_induce G W S hSW
    change (coreCrossEdges H S' Finset.univ).card +
      (withinEdges H (Finset.univ \ S')).card =
      (coreCrossEdges G S W).card + (withinEdges G (W \ S)).card at hTransport
    rw [hTransport]
    exact hActualLedger.2.ge
  have hsdiffEq : @SDiff.sdiff (Finset (W : Set V))
      (@Finset.instSDiff (W : Set V) (Classical.decEq _)) Finset.univ S' =
      Finset.univ \ S' := by
    ext z; simp only [Finset.mem_sdiff]
  rw [← hsdiffEq] at hLedger
  obtain ⟨hDcard, _hDS, _hThree, _hOutsideCard, hAdj⟩ :=
    actual_finite_contact_rigidity (by omega : 1 ≤ d) H hN S'
      hS'card hClique hOutDegree hFree hLedger
  have hLpos : 0 < L.card := by rw [hLcard]; omega
  obtain ⟨z, hzL⟩ := Finset.card_pos.mp hLpos
  have hzS : z ∉ S := (Finset.mem_sdiff.mp (hLO hzL)).2
  have hzW : z ∈ W := Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inr hzL))
  have hCD : C' ⊆ actualContacts H S' := by
    intro c hc
    have hcC : c.val ∈ C := (hmemC c).mp hc
    have hcS : c.val ∈ S := hCS hcC
    have hzc : z ≠ c.val := by
      intro h
      apply hzS
      rw [h]
      exact hcS
    apply (EvenInducedCarrier1105.actualContacts_lift_iff G W S c).mpr
    refine ⟨hcS, z, hzW, hzS, ?_⟩
    exact (hOldAdj z (hLT hzL) c.val (hST hcS)).mpr
      ⟨hzc, Or.inr (Or.inl ⟨hzS, hcC⟩)⟩
  have hDEq : actualContacts H S' = C' := by
    apply (Finset.eq_of_subset_of_card_le hCD ?_).symm
    rw [hDcard, hC'card]
  rw [hDEq] at hAdj
  have hxS' : x' ∉ S' := fun h => hx (hST ((hmemS x').mp h))
  have hxC' : x' ∉ C' := fun h => hx (hST (hCS ((hmemC x').mp h)))
  have hNewAdj (v : V) (hvT : v ∈ T) : G.Adj x v ↔ v ∈ C := by
    constructor
    · intro hxv
      have hvW : v ∈ W := hCapture v (Finset.mem_insert_of_mem hvT) hxv
      let v' : (W : Set V) := ⟨v, hvW⟩
      have hSmall : H.Adj x' v' := by change G.Adj x v; exact hxv
      have h := (hAdj x' v').mp hSmall
      rcases h.2 with hSS | hXC | hVC
      · exact False.elim (hxS' hSS.1)
      · exact (hmemC v').mp hXC.2
      · exact False.elim (hxC' hVC.2)
    · intro hvC
      let v' : (W : Set V) := ⟨v, hCW hvC⟩
      have hxv' : x' ≠ v' := by
        intro h
        have hval : x = v := congrArg (fun u : (W : Set V) => u.val) h
        apply hx
        rw [hval]
        exact hvT
      have hSmall : H.Adj x' v' := (hAdj x' v').mpr
        ⟨hxv', Or.inr (Or.inl ⟨hxS', (hmemC v').mpr hvC⟩)⟩
      exact hSmall
  have hxS : x ∉ S := fun h => hx (hST h)
  have hxC : x ∉ C := fun h => hx (hST (hCS h))
  intro u hu v hv
  rcases Finset.mem_insert.mp hu with hux | huT
  · subst u
    rcases Finset.mem_insert.mp hv with hvx | hvT
    · subst v
      simp
    · have hxv : x ≠ v := by rintro rfl; exact hx hvT
      simpa only [ne_eq, hxS, hxC, hxv, not_false_eq_true, false_and, true_and,
        and_false, or_false, false_or] using hNewAdj v hvT
  · rcases Finset.mem_insert.mp hv with hvx | hvT
    · subst v
      have hux : u ≠ x := by rintro rfl; exact hx huT
      have huxAdj : G.Adj u x ↔ u ∈ C := by
        constructor
        · intro h
          exact (hNewAdj u huT).mp h.symm
        · intro h
          exact ((hNewAdj u huT).mpr h).symm
      simpa only [ne_eq, hxS, hxC, hux, not_false_eq_true, and_false, true_and,
        or_false, false_or] using huxAdj
    · exact hOldAdj u huT v hvT

end ErdosProblems.PathUpperReduction.EvenOriginalOneVertexRestoration1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenOriginalBackwardRestoration1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.CoreSizeUpper1105
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenActualSuffixClassification1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- A genuine universal apex belongs to the actual greatest d-core when that
core has more than d vertices. This needs only cone(M) <= G at the caller;
it does not identify the saturated G with its original cone. -/
theorem universal_apex_mem_actual_core (G : SimpleGraph V) (d : ℕ)
    (S : Finset V) (a : V) (hcore : degreeCore G d = S)
    (hlarge : d < S.card) (hall : ∀ z, z ≠ a → G.Adj z a) : a ∈ S := by
  classical
  by_contra ha
  have hgood : GoodCore G d S := by
    rw [← hcore]
    exact degree_core_good G d
  have hneighbors : ∀ z ∈ S, G.Adj a z := by
    intro z hz
    have hza : z ≠ a := by
      intro h
      exact ha (h ▸ hz)
    exact (hall z hza).symm
  have hinsert : GoodCore G d (insert a S) :=
    insert_good_of_all_neighbors G d S hgood hlarge a hneighbors
  have hsubset := good_subset_core G d (insert a S) hinsert
  have hacore : a ∈ degreeCore G d := hsubset (Finset.mem_insert_self a S)
  exact ha (hcore ▸ hacore)

/-- Classify every actual carrier with at least d outsiders by backward
induction on its COMPLETE certificate. Base cardinality, base contacts and
every restored classification are derived, not supplied. The universal
apex remains in the same contact set throughout the induction. -/
theorem classify_complete_deletion_with_apex (G : SimpleGraph V) (d : ℕ)
    (S T : Finset V) (a : V) (hd : 2 ≤ d)
    (hcertificate : ExactCoreDeletion G d S T)
    (hScard : S.card = d + 3) (hclique : G.IsClique (S : Set V))
    (haS : a ∈ S) (hall : ∀ z, z ≠ a → G.Adj z a)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (houtside : d ≤ (T \ S).card) :
    ∃ C : Finset V, C ⊆ S ∧ C.card = d ∧ a ∈ C ∧
      ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)) := by
  classical
  revert houtside
  induction hcertificate with
  | stop =>
      intro houtside
      simp only [Finset.sdiff_self, Finset.card_empty] at houtside
      omega
  | delete T x hx hxS hdegree tail ih =>
      intro houtside
      have hcurrent : ExactCoreDeletion G d S T :=
        ExactCoreDeletion.delete T x hx hxS hdegree tail
      by_cases hlast : (T \ S).card = d
      · obtain ⟨C, hCS, hCcard, hAdj⟩ :=
          actual_suffix_classification G d S T hd hcurrent hScard hclique hlast hfree
        have hpositive : 0 < (T \ S).card := by rw [hlast]; omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hpositive
        obtain ⟨hzT, hzS⟩ := Finset.mem_sdiff.mp hz
        have hza : z ≠ a := by
          intro h
          exact hzS (h.symm ▸ haS)
        have hST : S ⊆ T := certificate_core_subset hcurrent
        have hrel := (hAdj z hzT a (hST haS)).mp (hall z hza)
        have haC : a ∈ C := by
          rcases hrel.2 with hSS | hSC | hCS'
          · exact False.elim (hzS hSS.1)
          · exact hSC.2
          · exact False.elim (hCS'.1 haS)
        exact ⟨C, hCS, hCcard, haC, hAdj⟩
      · have hxOutside : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
        have hcount : ((T.erase x) \ S).card = (T \ S).card - 1 := by
          rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem hxOutside]
        have htailOutside : d ≤ ((T.erase x) \ S).card := by
          rw [hcount]
          omega
        obtain ⟨C, hCS, hCcard, haC, hOld⟩ := ih htailOutside
        have hSTail : S ⊆ T.erase x := certificate_core_subset tail
        have hxTail : x ∉ T.erase x := by
          intro h
          exact (Finset.mem_erase.mp h).1 rfl
        have hxa : G.Adj x a := by
          apply hall x
          intro h
          exact hxS (h.symm ▸ haS)
        have hnewDegree : withinDegree G (insert x (T.erase x)) x = d := by
          rw [Finset.insert_erase hx]
          exact hdegree
        have hRestored :=
          EvenOriginalOneVertexRestoration1105.restore_old_join_one_vertex
            G d S C (T.erase x) x a hd hSTail hScard hCS hCcard
            htailOutside hxTail haC hxa hnewDegree hfree hOld
        rw [Finset.insert_erase hx] at hRestored
        exact ⟨C, hCS, hCcard, haC, hRestored⟩

/-- Actual full-host structural endpoint. The supplied data are the actual
greatest core, its forced size, ORIGINAL tight edge count, ambient cycle
freedom and genuine universal apex. Complete deletion, core clique, last
block, contact set and all restorations are derived internally. -/
theorem classify_tight_actual_core_with_apex (G : SimpleGraph V) (d : ℕ)
    (S : Finset V) (a : V) (hd : 2 ≤ d)
    (hcore : degreeCore G d = S) (hScard : S.card = d + 3)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card))
    (houtside : d ≤ Nat.card V - S.card)
    (hall : ∀ z, z ≠ a → G.Adj z a)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    ∃ C : Finset V, C ⊆ S ∧ C.card = d ∧ a ∈ C ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)) := by
  classical
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  have hcertificate : ExactCoreDeletion G d S Finset.univ :=
    exact_core_deletion_of_tight_nonempty_core G d S hcore hSnonempty htight
  have hOutsideCard : ((Finset.univ : Finset V) \ S).card = Nat.card V - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hEdgesCard : (withinEdges G Finset.univ).card = Nat.card G.edgeSet := by
    have hEdges : withinEdges G Finset.univ = G.edgeFinset := by
      ext e
      simp [withinEdges]
    rw [hEdges, Nat.card_eq_fintype_card, G.card_edgeSet]
  have hLedger := certificate_edge_ledger hcertificate
  rw [hEdgesCard, hOutsideCard] at hLedger
  have hCoreEdges : (withinEdges G S).card = S.card.choose 2 := by
    rw [htight] at hLedger
    omega
  have hInducedCard : (G.induce (S : Set V)).edgeFinset.card =
      (Fintype.card (S : Set V)).choose 2 := by
    have hcardS : Fintype.card (S : Set V) = S.card :=
      Fintype.card_of_finset' (p := (S : Set V)) S (fun _ => Iff.rfl)
    rw [hcardS, ← hCoreEdges]
    have hlift := EvenInducedCarrier1105.withinEdges_lift_card G S S (Finset.Subset.refl S)
    rw [EvenInducedCarrier1105.liftSupport_self] at hlift
    refine Eq.trans ?_ hlift
    unfold withinEdges
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.subset_univ, and_true, mem_edgeFinset]
  have hInducedTop : G.induce (S : Set V) = ⊤ := by
    apply SimpleGraph.edgeFinset_inj.mp
    apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    exact hInducedCard.ge
  have hClique : G.IsClique (S : Set V) := by
    intro u hu v hv huv
    have hSubtypeNe : (⟨u, hu⟩ : (S : Set V)) ≠ ⟨v, hv⟩ := by
      intro h
      exact huv (congrArg (fun z : (S : Set V) => z.val) h)
    have hAdj : (G.induce (S : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [hInducedTop]
      exact hSubtypeNe
    exact hAdj
  have haS : a ∈ S := universal_apex_mem_actual_core G d S a hcore
    (by rw [hScard]; omega) hall
  have hOutsideFinset : d ≤ ((Finset.univ : Finset V) \ S).card := by
    rw [hOutsideCard]
    exact houtside
  obtain ⟨C, hCS, hCcard, haC, hAdj⟩ :=
    classify_complete_deletion_with_apex G d S Finset.univ a hd hcertificate
      hScard hClique haS hall hfree hOutsideFinset
  refine ⟨C, hCS, hCcard, haC, ?_⟩
  intro u v
  exact hAdj u (Finset.mem_univ u) v (Finset.mem_univ v)

end ErdosProblems.PathUpperReduction.EvenOriginalBackwardRestoration1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenOriginalNonemptyCore1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)
open ErdosProblems.PathS1ContainerCountBridge

theorem actual_universal_cone {n : ℕ}
    (H : SimpleGraph (Option (Fin n))) (ha : H.IsUniversal none) :
    H = ConeCoreApplication1105.cone
      (H.comap (some : Fin n → Option (Fin n))) := by
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
          exact ⟨fun _ => True.intro, fun _ => ha (by simp)⟩
  | some u =>
      cases v with
      | none =>
          change H.Adj (some u) none ↔ True
          exact ⟨fun _ => True.intro, fun _ => (ha (by simp)).symm⟩
      | some v => rfl

theorem top_core_impossible {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q)
    (H : SimpleGraph (Option (Fin n)))
    (hCH : cone (selectedGraph χ R) ≤ H)
    (hfree : ∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H)
    (hdelete : ∀ z, (H.induce {w | w ≠ z}).Connected)
    (S : Finset (Option (Fin n)))
    (hclique : H.IsClique (S : Set (Option (Fin n))))
    (hcard : S.card = 2 * d + 1) : False := by
  classical
  let M := selectedGraph χ R
  let J := H.comap (some : Fin n → Option (Fin n))
  have ha : H.IsUniversal none := by
    intro v hne
    exact hCH (UniformConeStructure1105.cone_apex_isUniversal M hne)
  have hSameCone : H = ConeCoreApplication1105.cone J :=
    actual_universal_cone H ha
  have hSelectedSub : M ≤ J := by
    intro u v huv
    exact hCH huv
  have hK : 5 ≤ 2 * d + 3 := by omega
  have hScard : S.card = (2 * d + 3) - 2 := by rw [hcard]; omega
  have hSclique : (ConeCoreApplication1105.cone J).IsClique
      (S : Set (Option (Fin n))) := by
    rw [← hSameCone]
    exact hclique
  have hJfree : ∀ m, 2 * d + 3 ≤ m →
      (cycleGraph m).Free (ConeCoreApplication1105.cone J) := by
    intro m hm
    rw [← hSameCone]
    exact hfree m hm
  have hJdelete : ∀ z : Option (Fin n),
      ((ConeCoreApplication1105.cone J).induce {w | w ≠ z}).Connected := by
    intro z
    rw [← hSameCone]
    exact hdelete z
  have hcompl : 1 < Sᶜ.card := by
    rw [Finset.card_compl, hcard]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcompl
  have houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v :=
    ⟨u, v, Finset.mem_compl.mp hu, Finset.mem_compl.mp hv, huv⟩
  have hContainer := ConeFiniteContainer1105.cone_finite_container
    J S hK hScard hSclique hJfree hJdelete houtside
  dsimp only at hContainer
  let m : ℕ := (2 * d + 3) - 3
  let l : ℕ := n - m
  obtain ⟨_hm2, hl, hsum, _hTcard, _b, e, _hb, _hezero, _heleft,
    _heright, headj⟩ := hContainer
  have hm : 4 ≤ m := by dsimp only [m]; omega
  have hnSum : n = m + l := hsum.symm
  let core : Fin m → Fin n := fun i => e (Sum.inl i)
  let leaf : Fin l → Fin n := fun j => e (Sum.inr j)
  let z : Fin m := ⟨0, by omega⟩
  have hEnum : Sum.elim core leaf = e := by
    funext x
    cases x <;> rfl
  have hinj : Function.Injective (Sum.elim core leaf) := by
    rw [hEnum]
    exact e.injective
  have hcover : Function.Surjective (Sum.elim core leaf) := by
    rw [hEnum]
    exact e.surjective
  have hsub : M ≤ s1Container core leaf z := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    have hc := (headj a b).mp (hSelectedSub hxy)
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            change i ≠ j at hc
            change (s1Container core leaf z).Adj (core i) (core j)
            apply (SimpleGraph.fromEdgeSet_adj _).mpr
            refine ⟨Or.inl ⟨s(i, j), ?_, ?_⟩, hxy.ne⟩
            · exact (SimpleGraph.mem_edgeSet (G := (⊤ : SimpleGraph (Fin m)))).mpr hc
            · simp only [Sym2.map_mk]
        | inr j =>
            change i.val = 0 at hc
            have hi : i = z := by apply Fin.ext; exact hc
            subst i
            change (s1Container core leaf z).Adj (core z) (leaf j)
            exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Or.inr ⟨j, rfl⟩, hxy.ne⟩
    | inr i =>
        cases b with
        | inl j =>
            change j.val = 0 at hc
            have hj : j = z := by apply Fin.ext; exact hc
            subst j
            change (s1Container core leaf z).Adj (leaf i) (core z)
            exact (SimpleGraph.fromEdgeSet_adj _).mpr
              ⟨Or.inr ⟨i, Sym2.eq_swap⟩, hxy.ne⟩
        | inr j => exact hc.elim
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.image (Sym2.map core)
  let B := (Finset.univ : Finset (Fin l)).image (fun j => s(core z, leaf j))
  have hEdgeSubset : M.edgeFinset ⊆ A ∪ B := by
    intro f
    refine Sym2.inductionOn f ?_
    intro x y hf
    have hxy : M.Adj x y := SimpleGraph.mem_edgeFinset.mp hf
    have hs := ((SimpleGraph.fromEdgeSet_adj _).mp (hsub hxy)).1
    rcases hs with ⟨t, ht, hte⟩ | ⟨j, hje⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨t, SimpleGraph.mem_edgeFinset.mpr ht, hte⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, hje⟩)
  have hCount : Nat.card M.edgeSet = q := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      selectedGraph_card_edgeFinset χ R
  have hCapacity : q ≤ m.choose 2 + l := by
    calc
      q = Nat.card M.edgeSet := hCount.symm
      _ = M.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      _ ≤ (A ∪ B).card := Finset.card_le_card hEdgeSubset
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ (⊤ : SimpleGraph (Fin m)).edgeFinset.card +
          (Finset.univ : Finset (Fin l)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = m.choose 2 + l := by
        simp only [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
          Fintype.card_fin, Finset.card_univ]
  have hkm : (2 * d + 2) - 2 = m := by dsimp only [m]; omega
  have hL : n - (2 * d + 2) + 2 = l := by dsimp only [l, m]; omega
  have hhalf : ((2 * d + 2) - 1) / 2 = d := by omega
  have hnotodd : ¬ Odd (2 * d + 2) := by
    simp only [Nat.odd_iff]
    omega
  have hqLiteral : max (((2 * d + 2) - 2).choose 2 + 1)
      ((((2 * d + 2) - 1) / 2 - 1).choose 2 +
        (((2 * d + 2) - 1) / 2 - 1) *
          (n - ((2 * d + 2) - 1) / 2 + 1) +
        (if Odd (2 * d + 2) then 1 else 2)) < q := by
    have hkpred : (2 * d + 2) - 2 = 2 * d := by omega
    simpa only [hkpred, hhalf, ite_eq_right hnotodd] using hq
  have hCapacityLiteral : q ≤ ((2 * d + 2) - 2).choose 2 +
      (n - (2 * d + 2) + 2) := by
    simpa only [hkm, hL] using hCapacity
  obtain ⟨hmargin, hcases⟩ :=
    WindowNumerics1105.original_palette_implies_window_or_full_four
      (2 * d + 2) n q (by omega) hn hqLiteral hCapacityLiteral
  have hmargin' : m.choose 2 + 2 ≤ q := by simpa only [hkm] using hmargin
  have hwindow : 2 * l ≤ m := by
    rcases hcases with hwindow | ⟨hsix, _hfull⟩
    · simpa only [hkm, hL] using hwindow
    · omega
  have hRainbow := rainbow_path_of_representative_s1_container
    hm hl hwindow hnSum χ R core leaf hinj hcover hsub hmargin'
  have hPathOrder : m + 2 = 2 * d + 2 := by dsimp only [m]; omega
  rw [hPathOrder] at hRainbow
  obtain ⟨P, hP⟩ := hRainbow
  exact hno P hP

/-- The actual small-core count is the first forbidden EVEN linear palette
plus the n apex edges; all natural subtractions retain their domain guards. -/
theorem small_core_count_eq_even_linear (d n : ℕ) (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ n) :
    (d + 3).choose 2 + d * (n + 1 - (d + 3)) =
      n + ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 3) := by
  let a := d - 1
  let b := n - d - 2
  have ha : d = a + 1 := by dsimp [a]; omega
  have hb : n + 1 - (d + 3) = b := by dsimp [b]; omega
  have hn' : n = a + b + 3 := by dsimp [a, b]; omega
  have ht : n - d + 1 = b + 3 := by dsimp [b]; omega
  have hstep (u : ℕ) : (u + 1).choose 2 = u + u.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' u 1
  have hchoose : (d + 3).choose 2 = a.choose 2 + 4 * a + 6 := by
    have he : d + 3 = (((a + 1) + 1) + 1) + 1 := by omega
    rw [he, hstep, hstep, hstep, hstep]
    ring
  calc
    (d + 3).choose 2 + d * (n + 1 - (d + 3)) =
        a.choose 2 + 4 * a + 6 + (a + 1) * b := by rw [hchoose, hb, ha]
    _ = (a + b + 3) + (a.choose 2 + a * (b + 3) + 3) := by ring
    _ = n + ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 3) := by
      rw [← hn', ← ht]

theorem small_core_original_classification {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q)
    (H : SimpleGraph (Option (Fin n)))
    (hCH : cone (selectedGraph χ R) ≤ H)
    (hfree : ∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H)
    (hdelete : ∀ z, (H.induce {w | w ≠ z}).Connected)
    (hsat : ∀ u v, u ≠ v → ¬ H.Adj u v →
      ∃ m, 2 * d + 3 ≤ m ∧ Nonempty ((cycleGraph m).Copy
        (H ⊔ fromEdgeSet {s(u, v)})))
    (hlower : n + q ≤ Nat.card H.edgeSet)
    (hsmall : (degreeCore H (d + 1)).card = d + 3) :
    H = cone (selectedGraph χ R) ∧
      ∃ C : Finset (Option (Fin n)), C ⊆ degreeCore H (d + 1) ∧
        C.card = d ∧ none ∈ C ∧
        ∀ u v, (cone (selectedGraph χ R)).Adj u v ↔ u ≠ v ∧
          ((u ∈ degreeCore H (d + 1) ∧ v ∈ degreeCore H (d + 1)) ∨
            (u ∉ degreeCore H (d + 1) ∧ v ∈ C) ∨
            (v ∉ degreeCore H (d + 1) ∧ u ∈ C)) := by
  classical
  let S := degreeCore H (d + 1)
  have hK : 5 ≤ 2 * d + 3 := by omega
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hKN : 2 * d + 3 ≤ Fintype.card (Option (Fin n)) := by rw [hN]; omega
  have hhalf : (2 * d + 3 - 1) / 2 = d + 1 := by omega
  have hnonempty : (degreeCore H ((2 * d + 3 - 1) / 2)).Nonempty := by
    rw [hhalf]
    exact Finset.card_pos.mp (by rw [hsmall]; omega)
  have hsecond := SecondCoreCount1105.saturated_second_core_eq
    H hK hKN hfree hdelete hsat hnonempty
  rw [hhalf] at hsecond
  have hthreshold : 2 * d + 3 - (degreeCore H (d + 1)).card = d := by
    rw [hsmall]
    omega
  rw [hthreshold] at hsecond
  have hcore : degreeCore H d = S := hsecond
  have hupper := SecondCoreCount1105.nonempty_core_edge_bound
    H hK hKN hfree hdelete hsat hnonempty
  rw [hhalf, hsmall, hN] at hupper
  have hsubtraction : 2 * d + 3 - (d + 3) = d := by omega
  rw [hsubtraction, small_core_count_eq_even_linear d n hd hn] at hupper
  have hlinear : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 3 ≤ q := by
    have hlt := lt_of_le_of_lt (le_max_right _ _) hq
    omega
  have htight : Nat.card H.edgeSet =
      S.card.choose 2 + d * (Nat.card (Option (Fin n)) - S.card) := by
    have hnat : Nat.card (Option (Fin n)) = n + 1 := by
      rw [Nat.card_eq_fintype_card, hN]
    change Nat.card H.edgeSet =
      (degreeCore H (d + 1)).card.choose 2 +
        d * (Nat.card (Option (Fin n)) - (degreeCore H (d + 1)).card)
    rw [hsmall, hnat, small_core_count_eq_even_linear d n hd hn]
    omega
  have hMcount : (selectedGraph χ R).edgeFinset.card = q :=
    selectedGraph_card_edgeFinset χ R
  have hConeCount : (cone (selectedGraph χ R)).edgeFinset.card = n + q := by
    rw [UniformConeStructure1105.finite_cone_edgeFinset_card]
    have hEq : @SimpleGraph.edgeFinset _ (selectedGraph χ R) (selectedGraph χ R).fintypeEdgeSet =
        @SimpleGraph.edgeFinset _ (selectedGraph χ R) (selectedGraph_edgeSet_fintype χ R) := by
      congr 1; exact Subsingleton.elim _ _
    rw [hEq, hMcount]
    omega
  have hHnat : Nat.card H.edgeSet = H.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hCardEquality : H.edgeFinset.card = (cone (selectedGraph χ R)).edgeFinset.card := by
    rw [← hHnat, hConeCount]
    omega
  have hOriginalCone : H = cone (selectedGraph χ R) := by
    apply SimpleGraph.edgeFinset_inj.mp
    symm
    exact Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hCH)
      (le_of_eq hCardEquality)
  have hapex : ∀ z : Option (Fin n), z ≠ none → H.Adj z none := by
    intro z hne
    exact (hCH (UniformConeStructure1105.cone_apex_isUniversal
      (selectedGraph χ R) hne.symm)).symm
  have hOutside : d ≤ Nat.card (Option (Fin n)) - S.card := by
    rw [Nat.card_eq_fintype_card, hN]
    change d ≤ n + 1 - (degreeCore H (d + 1)).card
    rw [hsmall]
    omega
  obtain ⟨C, hCS, hCcard, hnone, hclass⟩ :=
    EvenOriginalBackwardRestoration1105.classify_tight_actual_core_with_apex
      H d S none (by omega) hcore hsmall htight hOutside hapex
      (hfree (2 * d + 3) le_rfl)
  refine ⟨hOriginalCone, C, hCS, hCcard, hnone, ?_⟩
  intro u v
  rw [← hOriginalCone]
  exact hclass u v

/-- Original-color nonempty-core reduction, with no supplied structural
premise. The actual saturated cone is constructed from the SAME selected
graph. A nonempty first core has forced size d+3: its large endpoint uses the
SAME coloring's rainbow obstruction, and every middle size violates the
actual count. All original-cone classification data are then derived. -/
theorem original_even_saturated_nonempty_core_reduction {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    ∃ H : SimpleGraph (Option (Fin n)),
      cone (selectedGraph χ R) ≤ H ∧
      (∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, 2 * d + 3 ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      n + q ≤ Nat.card H.edgeSet ∧
      ((degreeCore H (d + 1)).Nonempty →
        (degreeCore H (d + 1)).card = d + 3 ∧
        H = cone (selectedGraph χ R) ∧
        ∃ C : Finset (Option (Fin n)), C ⊆ degreeCore H (d + 1) ∧
          C.card = d ∧ none ∈ C ∧
          ∀ u v, (cone (selectedGraph χ R)).Adj u v ↔ u ≠ v ∧
            ((u ∈ degreeCore H (d + 1) ∧ v ∈ degreeCore H (d + 1)) ∨
              (u ∉ degreeCore H (d + 1) ∧ v ∈ C) ∨
              (v ∉ degreeCore H (d + 1) ∧ u ∈ C))) := by
  classical
  let M := selectedGraph χ R
  have hk : 5 ≤ 2 * d + 2 := by omega
  have hMfree : (pathGraph (2 * d + 2)).Free M :=
    selectedGraph_free (pathGraph (2 * d + 2)) χ R hno
  have hc := UniformConeStructure1105.finite_connected_path_free_cone
    M hk hn hconn hMfree
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hK : 5 ≤ 2 * d + 3 := by omega
  have hKN : 2 * d + 3 ≤ Fintype.card (Option (Fin n)) := by rw [hN]; omega
  have hCfree : ∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free (cone M) := by
    intro m hm
    exact hc.2.2.1 m (by omega)
  have hCdelete : ∀ z, ((cone M).induce {w | w ≠ z}).Connected := by
    intro z
    exact hc.2.1 z
  obtain ⟨H, hCH, hfree, hdelete, hsat, hclique, _hupper⟩ :=
    CoreSizeUpper1105.exists_saturated_small_core
      (cone M) hK hKN hCfree hCdelete
  have hhalf : (2 * d + 3 - 1) / 2 = d + 1 := by omega
  rw [hhalf] at hclique
  have hMcount : Nat.card M.edgeSet = q := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      selectedGraph_card_edgeFinset χ R
  have hConeCount : Nat.card (cone M).edgeSet = Nat.card M.edgeSet + n := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc.2.2.2
  have hEdges : Nat.card (cone M).edgeSet ≤ Nat.card H.edgeSet := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      (Finset.card_le_card (SimpleGraph.edgeFinset_mono hCH))
  have hlower : n + q ≤ Nat.card H.edgeSet := by
    calc
      n + q = Nat.card M.edgeSet + n := by rw [hMcount]; omega
      _ = Nat.card (cone M).edgeSet := hConeCount.symm
      _ ≤ Nat.card H.edgeSet := hEdges
  have hinterval : (degreeCore H (d + 1)).Nonempty →
      d + 3 ≤ (degreeCore H (d + 1)).card ∧
      (degreeCore H (d + 1)).card ≤ 2 * d := by
    intro hnonempty
    have hnonempty' : (degreeCore H ((2 * d + 3 - 1) / 2)).Nonempty := by
      rwa [hhalf]
    have hsize := CoreSizeUpper1105.nonempty_core_size_interval
      H hK hKN hfree hdelete hsat hnonempty'
    rw [hhalf] at hsize
    have htop : (degreeCore H (d + 1)).card ≠ 2 * d + 1 := by
      intro heq
      exact top_core_impossible hd hn χ R hno hq H hCH hfree hdelete
        (degreeCore H (d + 1)) hclique heq
    constructor <;> omega
  refine ⟨H, hCH, hfree, hdelete, hsat, hlower, ?_⟩
  intro hnonempty
  have hrange := hinterval hnonempty
  have hsmall : (degreeCore H (d + 1)).card = d + 3 := by
    by_contra hne
    have hrLower : d + 4 ≤ (degreeCore H (d + 1)).card := by omega
    have hd4 : 4 ≤ d := by omega
    have hnonempty' : (degreeCore H ((2 * d + 3 - 1) / 2)).Nonempty := by
      rwa [hhalf]
    have hcount := SecondCoreCount1105.nonempty_core_edge_bound
      H hK hKN hfree hdelete hsat hnonempty'
    rw [hhalf, hN] at hcount
    have hscalar := EvenIntermediateCoreScalar1105.intermediate_core_count_le_original_even_threshold
      d n (degreeCore H (d + 1)).card hd4 hn hrLower hrange.2
    have hbound : Nat.card H.edgeSet ≤ n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) :=
      le_trans hcount hscalar
    omega
  exact ⟨hsmall, small_core_original_classification hd hn χ R hq H hCH hfree
    hdelete hsat hlower hsmall⟩

/-- The original SAME-color nonempty first-core branch is impossible above
the literal even threshold. The original exceptional-family equivalence and
the two actual independent-side vertices are derived internally; the removed
representative edge remains the actual owner of the inserted original color.
No claim is made here for the empty first-core branch. -/
theorem original_even_saturated_first_core_empty {d n q : ℕ}
    (hd : 3 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    ∃ H : SimpleGraph (Option (Fin n)),
      cone (selectedGraph χ R) ≤ H ∧
      (∀ m, 2 * d + 3 ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      (∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, 2 * d + 3 ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)}))) ∧
      n + q ≤ Nat.card H.edgeSet ∧ degreeCore H (d + 1) = ∅ := by
  classical
  obtain ⟨H, hCH, hfree, hdelete, hsat, hlower, hnonempty⟩ :=
    original_even_saturated_nonempty_core_reduction hd hn χ R hconn hno hq
  refine ⟨H, hCH, hfree, hdelete, hsat, hlower, ?_⟩
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hfirst
  obtain ⟨hScard, _hConeEq, C, hCS, hCcard, hapex, hclass⟩ := hnonempty hfirst
  obtain ⟨phi, hselected⟩ :=
    EvenSelectedFamilyIdentification1105.exists_family_pullback_of_actual_cone_classification
      n d (selectedGraph χ R) (degreeCore H (d + 1)) C (by omega)
      hn hCS hScard hCcard hapex hclass
  let u : Fin (n - d - 2) := ⟨0, by omega⟩
  let v : Fin (n - d - 2) := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 1 at hval
    omega
  have hRainbow := ErdosProblems.EvenExceptionExchange.exists_original_rainbow_path_of_selected_comap_eq_family
    (d - 1) (n - d - 2) (by omega) (by omega) χ R phi hselected u v huv
  have hpath : 2 * (d - 1) + 4 = 2 * d + 2 := by omega
  rw [hpath] at hRainbow
  obtain ⟨P, hP⟩ := hRainbow
  exact hno P hP

end ErdosProblems.PathUpperReduction.EvenOriginalNonemptyCore1105
end

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
end

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
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.PathEightSpanningBase1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathS1ContainerCountBridge
open ErdosProblems.PathSelectedC6FourthLeaf
open ErdosProblems.PathSelectedS3MotifExtractor

/-- Any connected representative `selectedGraph χ r` on `Fin 8` with no rainbow
`P_8` has `q ≤ 16`. -/
theorem palette_le_sixteen_of_connected_no_rainbow_path_eight {q : ℕ}
    (χ : TopEdgeLabeling (Fin 8) (Fin q)) (r : RepresentativeChoice χ)
    (hconn : (selectedGraph χ r).Connected)
    (hno : ∀ f : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin 8)),
      ¬ IsRainbow f.toHom χ) : q ≤ 16 := by
  classical
  by_contra hlarge
  have hq : 17 ≤ q := by omega
  let G : SimpleGraph (Fin 8) := selectedGraph χ r
  have hGfree : (pathGraph 8).Free G := selectedGraph_free (pathGraph 8) χ r hno
  have hGcount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  obtain ⟨H, hGH, hHfree, hclosure⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by decide : 3 ≤ 8) G hGfree
  have hHconn : H.Connected := SimpleGraph.Connected.mono hGH hconn
  have hHedges : 17 ≤ H.edgeFinset.card := by
    calc
      17 ≤ q := hq
      _ = G.edgeFinset.card := hGcount.symm
      _ ≤ H.edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  have hneTop : H ≠ ⊤ := by
    intro htop
    apply hHfree
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph 8) (⊤ : SimpleGraph (Fin 8)) le_top⟩
  have hclosureLocal : ∀ x y : Fin 8, x ≠ y → ¬ H.Adj x y →
      @SimpleGraph.degree (Fin 8) H x (Subtype.fintype (· ∈ H.neighborSet x)) +
      @SimpleGraph.degree (Fin 8) H y (Subtype.fintype (· ∈ H.neighborSet y)) ≤ 8 - 2 := by
    intro x y hxy hnon
    have h := hclosure x y hxy hnon
    have hx : @SimpleGraph.degree (Fin 8) H x (Subtype.fintype (· ∈ H.neighborSet x)) = H.degree x := by
      congr 1; exact Subsingleton.elim _ _
    have hy : @SimpleGraph.degree (Fin 8) H y (Subtype.fintype (· ∈ H.neighborSet y)) = H.degree y := by
      congr 1; exact Subsingleton.elim _ _
    rw [hx, hy]
    exact h
  obtain ⟨a, L, ha, htwice, hLcard, hLdegree, hCap⟩ :=
    spanning_degree_slots_and_edge_count 8 (by decide) H hHconn hneTop hclosureLocal
  have hcases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · -- Branch `a = 1`: `H` is the `S_1` graph (`K_6` with two leaves at hub `w`).
    have hc62 : (8 - 2 : ℕ).choose 2 + 2 ≤ H.edgeFinset.card := by
      have hc : (8 - 2 : ℕ).choose 2 = 15 := by decide
      omega
    obtain ⟨w, hwNotL, _hLdeg1, _hHcard17, _hCoreTop, _hLind, hHadj⟩ :=
      a_one_slots_force_s1 8 (by decide) H hHconn hclosureLocal L hLcard hLdegree hc62
    let C : Finset (Fin 8) := Lᶜ
    have hCcard : C.card = 6 := by
      simpa only [C, Fintype.card_fin, hLcard] using Finset.card_compl L
    have hwC : w ∈ C := Finset.mem_compl.mpr hwNotL
    let eC0 : Fin 6 ≃ C := (Finset.equivFinOfCardEq hCcard).symm
    let eC : Fin 6 ≃ C := (Equiv.swap 0 (eC0.symm ⟨w, hwC⟩)).trans eC0
    let eL : Fin 2 ≃ L := (Finset.equivFinOfCardEq hLcard).symm
    let core : Fin 6 → Fin 8 := fun i => (eC i).val
    let leaf : Fin 2 → Fin 8 := fun j => (eL j).val
    have hcore0 : core 0 = w := by
      dsimp [core, eC]
      rw [Equiv.swap_apply_left, Equiv.apply_symm_apply]
    have hinj : Function.Injective (Sum.elim core leaf) := by
      intro x y hxy
      rcases x with i | j <;> rcases y with i' | j'
      · exact congrArg Sum.inl (eC.injective (Subtype.ext hxy))
      · exfalso
        have hiC : core i ∈ C := (eC i).property
        have hjL : leaf j' ∈ L := (eL j').property
        change core i = leaf j' at hxy
        exact (Finset.mem_compl.mp hiC) (hxy ▸ hjL)
      · exfalso
        have hjL : leaf j ∈ L := (eL j).property
        have hiC : core i' ∈ C := (eC i').property
        change leaf j = core i' at hxy
        exact (Finset.mem_compl.mp hiC) (hxy.symm ▸ hjL)
      · exact congrArg Sum.inr (eL.injective (Subtype.ext hxy))
    have hcover : Function.Surjective (Sum.elim core leaf) :=
      ((Fintype.bijective_iff_injective_and_card (Sum.elim core leaf)).mpr
        ⟨hinj, by decide⟩).2
    have hsub : G ≤ s1Container core leaf 0 := by
      intro u v huv
      have hHuv : H.Adj u v := hGH huv
      obtain ⟨hne, hbranch⟩ := (hHadj u v).mp hHuv
      apply (SimpleGraph.fromEdgeSet_adj _).mpr
      refine ⟨?_, hne⟩
      rcases hbranch with ⟨huNotL, hvNotL⟩ | ⟨huL, rfl⟩ | ⟨hvL, rfl⟩
      · left
        let iu : Fin 6 := eC.symm ⟨u, Finset.mem_compl.mpr huNotL⟩
        let iv : Fin 6 := eC.symm ⟨v, Finset.mem_compl.mpr hvNotL⟩
        have hcoreu : core iu = u := congrArg Subtype.val (eC.apply_symm_apply _)
        have hcorev : core iv = v := congrArg Subtype.val (eC.apply_symm_apply _)
        have hiuv : iu ≠ iv := fun h => hne (hcoreu.symm.trans ((congrArg core h).trans hcorev))
        refine ⟨s(iu, iv), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin 6))).mpr hiuv, ?_⟩
        simp only [Sym2.map_mk, hcoreu, hcorev]
      · right
        let ju : Fin 2 := eL.symm ⟨u, huL⟩
        have hleafu : leaf ju = u := congrArg Subtype.val (eL.apply_symm_apply _)
        refine ⟨ju, ?_⟩
        dsimp only
        rw [hcore0, hleafu, Sym2.eq_swap]
      · right
        let jv : Fin 2 := eL.symm ⟨v, hvL⟩
        have hleafv : leaf jv = v := congrArg Subtype.val (eL.apply_symm_apply _)
        refine ⟨jv, ?_⟩
        dsimp only
        rw [hcore0, hleafv]
    have hq17 : (6 : ℕ).choose 2 + 2 ≤ q := by
      have hc : (6 : ℕ).choose 2 = 15 := by decide
      omega
    obtain ⟨f, hf⟩ :=
      rainbow_path_of_representative_s1_container
        (by decide : 4 ≤ 6) (by decide : 2 ≤ 2) (by decide : 2 * 2 ≤ 6) rfl
        χ r core leaf hinj hcover hsub hq17
    exact hno f hf
  · -- Branch `a = 2`: `H.edgeFinset.card ≤ 16`, contradicting `17 ≤ H.edgeFinset.card`.
    have hc52 : (8 - 1 - 2 : ℕ).choose 2 = 10 := by decide
    omega
  · -- Branch `a = 3`: `H` is `K_3` joined to `I_5`.
    obtain ⟨U, hUcard, _hHcard18, _hUuniv, _hOthree, hHadj⟩ :=
      ActualK8Rigidity1105.actual_three_hub_rigidity H L hLcard hLdegree hclosureLocal hHedges
    have hG17 : 17 ≤ (@SimpleGraph.edgeFinset (Fin 8) G G.fintypeEdgeSet).card := by
      have heq : (@SimpleGraph.edgeFinset (Fin 8) G G.fintypeEdgeSet).card = G.edgeFinset.card := by
        congr 2; exact Subsingleton.elim _ _
      omega
    obtain ⟨u, hu, hmotif⟩ :=
      selected_c6_fourth_leaf_of_seventeen_edges_in_three_hub G H hGH hG17 U hUcard hHadj
    obtain ⟨f, hf⟩ :=
      rainbow_path_eight_of_representative_c6_and_fourth_leaf χ r u hu hmotif
    exact hno f hf

/-- Every surjective coloring of `K_8` avoiding a rainbow `P_8` uses at most 16 colors. -/
theorem palette_le_sixteen_of_no_rainbow_path_eight {q : ℕ}
    (χ : TopEdgeLabeling (Fin 8) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin 8)),
      ¬ IsRainbow f.toHom χ) : q ≤ 16 := by
  classical
  by_contra hlarge
  have hdense : (8 - 2).choose 2 + 2 ≤ q := by
    have hc62 : (8 - 2 : ℕ).choose 2 = 15 := by decide
    omega
  obtain ⟨r, hconn⟩ := exists_connected_representative_of_dense_palette
    χ hχ (by decide : 0 < 8) hdense
  have hle := palette_le_sixteen_of_connected_no_rainbow_path_eight χ r hconn hno
  omega

/-- Upper bound `antiRamseyNum (pathGraph 8) 8 ≤ 16`. -/
theorem antiRamseyNum_path_eight_eight_le_sixteen :
    antiRamseyNum (pathGraph 8) 8 ≤ 16 := by
  unfold antiRamseyNum
  apply csSup_le'
  rintro q ⟨χ, hχ, hno⟩
  exact palette_le_sixteen_of_no_rainbow_path_eight χ hχ hno

/-- Exact value `antiRamseyNum (pathGraph 8) 8 = 16`. -/
theorem antiRamseyNum_path_eight_eight_eq_sixteen :
    antiRamseyNum (pathGraph 8) 8 = 16 := by
  apply Nat.le_antisymm antiRamseyNum_path_eight_eight_le_sixteen
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 8 8 (by decide) (by decide)
  have hnotOdd : ¬ Odd (8 : ℕ) := by decide
  have hc62 : (8 - 2 : ℕ).choose 2 = 15 := by decide
  have hc22 : (((8 - 1 : ℕ) / 2) - 1).choose 2 = 1 := by decide
  simp only [hnotOdd, ite_false] at hlower
  omega

end ErdosProblems.PathUpperReduction.PathEightSpanningBase1105
end

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
end
