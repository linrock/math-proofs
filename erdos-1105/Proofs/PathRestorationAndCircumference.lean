module

/-
Copyright 2025-2026 The Formal Conjectures Authors (cycleLengths, oddCycleLengths in SimpleGraph).
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

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.List.FinRange
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs
public import PathConeAndVineCycles

@[expose] public section

/-!
# PathRestorationAndCircumference

Degree-core elimination, restoration traces, seed-first path filling, `h = 3` residual linear-forest star extraction, high-degree outsider cycle covers, and 2-connected circumference bounds for Erdős Problem 1105.
-/

namespace ErdosProblems.PathUpperReduction.ActualCycleOutside1105

open SimpleGraph

/-- An edge outside an actual cycle in a connected graph yields an actual path
on two more vertices than the cycle.  The attachment and both fresh outside
vertices are derived from the original graph. -/
theorem path_copy_of_outside_edge {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (x y : V) (hx : x ∉ C.support) (hy : y ∉ C.support)
    (hxy : G.Adj x y) : pathGraph (C.length + 2) ⊑ G := by
  classical
  let O : Set V := {z | z ∉ C.support}
  let H := G.induce O
  let xo : O := ⟨x, hx⟩
  let U : Set V := {z | ∃ hz : z ∈ O, H.Reachable xo ⟨z, hz⟩}
  have hxU : x ∈ U := ⟨hx, SimpleGraph.Reachable.rfl⟩
  have haU : a ∉ U := by
    rintro ⟨haO, _⟩
    exact haO C.start_mem_support
  obtain ⟨p⟩ := hconn x a
  obtain ⟨b, _, hbU, hbNotU⟩ := p.exists_boundary_dart U hxU haU
  obtain ⟨hzO, hzReach⟩ := hbU
  have hbCycle : b.snd ∈ C.support := by
    by_contra hbOutside
    have hbH : H.Adj ⟨b.fst, hzO⟩ ⟨b.snd, hbOutside⟩ := b.adj
    exact hbNotU ⟨hbOutside, hzReach.trans hbH.reachable⟩
  have hOutsideNeighbor : ∃ w : V, w ∉ C.support ∧ G.Adj b.fst w := by
    by_cases hzx : b.fst = x
    · refine ⟨y, hy, ?_⟩
      simpa only [hzx] using hxy
    · obtain ⟨q⟩ := hzReach.symm
      have hEndpoints : (⟨b.fst, hzO⟩ : O) ≠ xo := by
        intro h
        exact hzx (congrArg Subtype.val h)
      have hqNotNil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne hEndpoints
      exact ⟨q.snd.val, q.snd.property, q.adj_snd hqNotNil⟩
  obtain ⟨w, hwOutside, hzw⟩ := hOutsideNeighbor
  let rot := C.rotate b.snd hbCycle
  have hrot : rot.IsCycle := hC.rotate hbCycle
  have hzDrop : b.fst ∉ rot.dropLast.support := by
    intro hz
    rw [rot.support_dropLast hrot.not_nil] at hz
    have hzRot := List.mem_of_mem_dropLast hz
    exact hzO ((C.mem_support_rotate_iff b.snd hbCycle).mp hzRot)
  have hwDrop : w ∉ rot.dropLast.support := by
    intro hw
    rw [rot.support_dropLast hrot.not_nil] at hw
    have hwRot := List.mem_of_mem_dropLast hw
    exact hwOutside ((C.mem_support_rotate_iff b.snd hbCycle).mp hwRot)
  let q1 := SimpleGraph.Walk.cons b.adj rot.dropLast
  have hq1 : q1.IsPath := hrot.isPath_dropLast.cons hzDrop
  have hwQ1 : w ∉ q1.support := by
    intro hw
    change w ∈ b.fst :: rot.dropLast.support at hw
    rcases List.mem_cons.mp hw with hwz | hwRot
    · exact hzw.ne' hwz
    · exact hwDrop hwRot
  let q2 := SimpleGraph.Walk.cons hzw.symm q1
  have hq2 : q2.IsPath := hq1.cons hwQ1
  have hdrop : rot.dropLast.length + 1 = C.length := by
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = C.length := SimpleGraph.Walk.length_rotate C b.snd hbCycle
  have hlength : q2.length + 1 = C.length + 2 := by
    change (rot.dropLast.length + 1 + 1) + 1 = C.length + 2
    omega
  have hcopy : SimpleGraph.Copy (pathGraph (q2.length + 1)) G := hq2.pathGraphCopy
  rw [hlength] at hcopy
  exact ⟨hcopy⟩

/-- The vertices outside an actual `2*d`-cycle are independent when the original
connected graph excludes `P_(2*d+2)`.  This does not require a supplied outside
component, favorable attachment, minimum-degree or alternating-half premise. -/
theorem outside_independent_of_actual_cycle {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) (d : ℕ) (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hLength : C.length = 2 * d) :
    ∀ x y : V, x ∉ C.support → y ∉ C.support → ¬G.Adj x y := by
  intro x y hx hy hxy
  have hcopy := path_copy_of_outside_edge G hconn C hC x y hx hy hxy
  rw [hLength] at hcopy
  exact hfree hcopy

end ErdosProblems.PathUpperReduction.ActualCycleOutside1105

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.CountCoreBasis

variable {V : Type*} [Fintype V]

noncomputable def GoodCore (G : SimpleGraph V) (d : ℕ) (S : Finset V) : Prop := by
  classical
  exact ∀ x ∈ S, d < (S.filter (fun z => G.Adj x z)).card

noncomputable def degreeCore (G : SimpleGraph V) (d : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ S : Finset V, x ∈ S ∧ GoodCore G d S)

theorem good_subset_core (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hS : GoodCore G d S) : S ⊆ degreeCore G d := by
  classical
  intro x hx
  simp only [degreeCore, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨S, hx, hS⟩

theorem degree_core_good (G : SimpleGraph V) (d : ℕ) :
    GoodCore G d (degreeCore G d) := by
  classical
  intro x hx
  obtain ⟨S, hxS, hS⟩ := (Finset.mem_filter.mp hx).2
  have hsub : S.filter (fun z => G.Adj x z) ⊆
      (degreeCore G d).filter (fun z => G.Adj x z) := by
    intro z hz
    obtain ⟨hzS, hxz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨good_subset_core G d S hS hzS, hxz⟩
  exact (hS x hxS).trans_le (Finset.card_le_card hsub)

end ErdosProblems.PathUpperReduction.CountCoreBasis

end

section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.CoreElimination

variable {V : Type*} [Fintype V]

noncomputable def withinEdges (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => e.toFinset ⊆ S)

noncomputable def withinDegree (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ := by
  classical
  exact (S.filter (fun z => G.Adj x z)).card

theorem withinEdges_card_le_choose (G : SimpleGraph V) (S : Finset V) :
    (withinEdges G S).card ≤ S.card.choose 2 := by
  classical
  unfold withinEdges
  rw [G.card_filter_edgeFinset_toFinset_subset S]
  have hcard : Fintype.card (↑S : Set V) = S.card := by
    exact Fintype.card_coe S
  simpa only [hcard] using
    (G.induce (↑S : Set V)).card_edgeFinset_le_card_choose_two

section Erase

theorem withinEdges_erase_eq_filter (G : SimpleGraph V) (S : Finset V) (x : V) :
    letI : DecidableEq V := Classical.decEq V
    withinEdges G (S.erase x) = (withinEdges G S).filter (fun e => x ∉ e) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heG, hsub⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heG, ?_⟩, ?_⟩
    · exact hsub.trans (Finset.erase_subset x S)
    · intro hxe
      have hxErase := hsub (Sym2.mem_toFinset.mpr hxe)
      simp at hxErase
  · intro he
    obtain ⟨heS, hnot⟩ := Finset.mem_filter.mp he
    obtain ⟨heG, hsub⟩ := Finset.mem_filter.mp heS
    refine Finset.mem_filter.mpr ⟨heG, ?_⟩
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, hsub hz⟩
    intro hzx
    exact hnot (hzx ▸ Sym2.mem_toFinset.mp hz)

theorem withinEdges_erase_ledger (G : SimpleGraph V) (S : Finset V) (x : V)
    (hx : x ∈ S) :
    letI : DecidableEq V := Classical.decEq V
    (withinEdges G S).card =
      (withinEdges G (S.erase x)).card + withinDegree G S x := by
  classical
  have hIncident :
      ((withinEdges G S).filter (fun e => x ∈ e)).card =
        (S.filter (fun z => G.Adj x z)).card := by
    symm
    apply Finset.card_bij (fun z _hz => s(x, z))
    · intro z hz
      obtain ⟨hzS, hxz⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨?_, Sym2.mem_mk_left _ _⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simpa only [mem_edgeFinset, mem_edgeSet] using hxz
      · rw [Sym2.toFinset_mk_eq]
        exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hzS⟩
    · intro z₁ _hz₁ z₂ _hz₂ hpair
      exact Sym2.congr_right.mp hpair
    · intro e he
      obtain ⟨heS, hxe⟩ := Finset.mem_filter.mp he
      obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxe
      obtain ⟨heG, hsub⟩ := Finset.mem_filter.mp heS
      have hzS : z ∈ S := hsub (by simp [Sym2.toFinset_mk_eq])
      have hxz : G.Adj x z := by simpa only [mem_edgeFinset, mem_edgeSet] using heG
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hxz⟩, rfl⟩
  have hPartition := (withinEdges G S).card_filter_add_card_filter_not
    (fun e => x ∈ e)
  rw [hIncident, ← withinEdges_erase_eq_filter G S x] at hPartition
  simpa only [withinDegree, Nat.add_comm] using hPartition.symm

end Erase

theorem outside_core_low_degree (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hC : degreeCore G d ⊆ S)
    (hlarge : max d (degreeCore G d).card < S.card) :
    ∃ x, x ∈ S ∧ x ∉ degreeCore G d ∧ withinDegree G S x ≤ d := by
  classical
  by_contra hnone
  have hgood : GoodCore G d S := by
    intro x hxS
    change d < withinDegree G S x
    by_cases hxC : x ∈ degreeCore G d
    · have hCore : d < withinDegree G (degreeCore G d) x := by
        simpa only [withinDegree] using degree_core_good G d x hxC
      have hmono : withinDegree G (degreeCore G d) x ≤ withinDegree G S x := by
        unfold withinDegree
        apply Finset.card_le_card
        intro z hz
        obtain ⟨hzC, hxz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hC hzC, hxz⟩
      exact hCore.trans_le hmono
    · have hnot : ¬ withinDegree G S x ≤ d := by
        intro hlow
        exact hnone ⟨x, hxS, hxC, hlow⟩
      omega
  have hSC : S ⊆ degreeCore G d := good_subset_core G d S hgood
  have hcard : S.card ≤ (degreeCore G d).card := Finset.card_le_card hSC
  have hmax : (degreeCore G d).card ≤ max d (degreeCore G d).card :=
    Nat.le_max_right _ _
  omega

theorem core_induced_edge_bound (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hC : degreeCore G d ⊆ S)
    (hM : max d (degreeCore G d).card ≤ S.card) :
    (withinEdges G S).card ≤
      (max d (degreeCore G d).card).choose 2 +
        d * (S.card - max d (degreeCore G d).card) := by
  classical
  let C := degreeCore G d
  let M := max d C.card
  let P : Finset V → Prop := fun T => C ⊆ T → M ≤ T.card →
    (withinEdges G T).card ≤ M.choose 2 + d * (T.card - M)
  have hP : ∀ T, P T := by
    intro T
    refine Finset.strongInductionOn T ?_
    intro T ih
    dsimp only [P]
    intro hCT hMT
    by_cases hbase : T.card = M
    · have hclique := withinEdges_card_le_choose G T
      simpa only [hbase, Nat.sub_self, Nat.mul_zero, Nat.add_zero] using hclique
    · have hlarge : M < T.card := by omega
      obtain ⟨x, hxT, hxC, hlow⟩ := outside_core_low_degree G d T hCT hlarge
      have hCerase : C ⊆ T.erase x := by
        intro z hzC
        apply Finset.mem_erase.mpr
        refine ⟨?_, hCT hzC⟩
        intro hzx
        exact hxC (hzx ▸ hzC)
      have hcardErase : (T.erase x).card = T.card - 1 :=
        Finset.card_erase_of_mem hxT
      have hMerase : M ≤ (T.erase x).card := by omega
      have hIH := ih (T.erase x) (Finset.erase_ssubset hxT) hCerase hMerase
      have hledger := withinEdges_erase_ledger G T x hxT
      have hsteps : ((T.erase x).card - M) + 1 = T.card - M := by omega
      calc
        (withinEdges G T).card =
            (withinEdges G (T.erase x)).card + withinDegree G T x := hledger
        _ ≤ (M.choose 2 + d * ((T.erase x).card - M)) + d :=
          Nat.add_le_add hIH hlow
        _ = M.choose 2 + d * (((T.erase x).card - M) + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        _ = M.choose 2 + d * (T.card - M) := by rw [hsteps]
  exact hP S hC hM

theorem degree_core_edge_bound (G : SimpleGraph V) (d : ℕ)
    (hd : d ≤ Nat.card V) :
    Nat.card G.edgeSet ≤
      (max d (degreeCore G d).card).choose 2 +
        d * (Nat.card V - max d (degreeCore G d).card) := by
  classical
  have hdUniv : d ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hd
  have hCoreUniv : degreeCore G d ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hMUniv : max d (degreeCore G d).card ≤ (Finset.univ : Finset V).card :=
    max_le hdUniv (Finset.card_le_card hCoreUniv)
  have hbound := core_induced_edge_bound G d Finset.univ hCoreUniv hMUniv
  have hEdgesUniv : withinEdges G Finset.univ = G.edgeFinset := by
    ext e
    simp [withinEdges]
  simpa only [hEdgesUniv, Finset.card_univ, Nat.card_eq_fintype_card, G.card_edgeSet]
    using hbound

end ErdosProblems.PathUpperReduction.CoreElimination

end

section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination

noncomputable section

namespace ErdosProblems.PathUpperReduction.RestorationTrace1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Actual reverse restoration on the SAME original G and fixed kernel K.
Each snoc records the exact earlier support and cumulative deficit charge. -/
inductive RestorationTrace (G : SimpleGraph V) (d : ℕ) (K : Finset V) :
    Finset V → ℕ → Prop
  | nil : RestorationTrace G d K K 0
  | snoc {U : Finset V} {c : ℕ} (trace : RestorationTrace G d K U c)
      (x : V) (hfresh : x ∉ U) (hlow : withinDegree G U x < d) :
      RestorationTrace G d K (insert x U) (c + (d - withinDegree G U x))

omit [Fintype V] in
/-- Erasing the endpoint itself preserves its own restricted degree,
because the original graph has no loop at that endpoint. -/
theorem withinDegree_self_erase (G : SimpleGraph V) (U : Finset V) (x : V) :
    withinDegree G (U.erase x) x = withinDegree G U x := by
  classical
  have hfilter : (U.erase x).filter (fun z => G.Adj x z) =
      U.filter (fun z => G.Adj x z) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzErase, hxz⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hzErase).2, hxz⟩
    · intro hz
      obtain ⟨hzU, hxz⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hzU⟩, hxz⟩
      intro hzx
      subst z
      exact G.irrefl hxz
  exact congrArg Finset.card hfilter

/-- An actual edge deficit pays for every strictly low-degree erasure.
The surviving support, lower degree bound and remaining exact deficit are
all constructed internally on the original graph and actual vertex set. -/
theorem exists_actual_kernel_with_restoration_trace_of_empty_core_deficit
    (G : SimpleGraph V) (d : ℕ) (S : Finset V) (D : ℕ)
    (hC : degreeCore G d = ∅)
    (hS : d + 3 ≤ S.card)
    (hD : D ≤ S.card - d - 3)
    (hE : (withinEdges G S).card + D =
      d.choose 2 + d * (S.card - d)) :
    ∃ T : Finset V, T ⊆ S ∧ S.card - D ≤ T.card ∧
      d + 3 ≤ T.card ∧
      (∀ x ∈ T, d ≤ withinDegree G T x) ∧
      ∃ Drem : ℕ, Drem ≤ D ∧ Drem ≤ T.card - d - 3 ∧
        (withinEdges G T).card + Drem =
          d.choose 2 + d * (T.card - d) ∧
        ∃ c : ℕ, RestorationTrace G d T S c ∧ D = Drem + c := by
  classical
  let P : Finset V → Prop := fun U =>
    ∀ E : ℕ, d + 3 ≤ U.card → E ≤ U.card - d - 3 →
      (withinEdges G U).card + E = d.choose 2 + d * (U.card - d) →
      ∃ T : Finset V, T ⊆ U ∧ U.card - E ≤ T.card ∧
        d + 3 ≤ T.card ∧
        (∀ x ∈ T, d ≤ withinDegree G T x) ∧
        ∃ Erem : ℕ, Erem ≤ E ∧ Erem ≤ T.card - d - 3 ∧
          (withinEdges G T).card + Erem =
            d.choose 2 + d * (T.card - d) ∧
          ∃ c : ℕ, RestorationTrace G d T U c ∧ E = Erem + c
  have hP : ∀ U, P U := by
    intro U
    refine Finset.strongInductionOn U ?_
    intro U ih
    dsimp only [P]
    intro E hsize hdeficit hcount
    by_cases hmin : ∀ x ∈ U, d ≤ withinDegree G U x
    · refine ⟨U, ?_, ?_, hsize, hmin, E, le_rfl, hdeficit, hcount,
        0, RestorationTrace.nil, ?_⟩
      · intro x hx
        exact hx
      · omega
      · omega
    · push Not at hmin
      obtain ⟨x, hx, hxlow⟩ := hmin
      have hcard : (U.erase x).card = U.card - 1 :=
        Finset.card_erase_of_mem hx
      have hCerase : degreeCore G d ⊆ U.erase x := by
        rw [hC]
        exact Finset.empty_subset _
      have hdErase : max d (degreeCore G d).card ≤ (U.erase x).card := by
        rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d), hcard]
        omega
      have hbound := core_induced_edge_bound G d (U.erase x) hCerase hdErase
      rw [hC, Finset.card_empty, max_eq_left (Nat.zero_le d)] at hbound
      have hstep : (U.erase x).card - d + 1 = U.card - d := by
        omega
      have htotal : d.choose 2 + d * (U.card - d) =
          (d.choose 2 + d * ((U.erase x).card - d)) + d := by
        rw [← hstep, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      have hledger := withinEdges_erase_ledger G U x hx
      have hbalance := hcount
      rw [hledger, htotal] at hbalance
      have hcharge : d - withinDegree G U x ≤ E := by
        omega
      have hpositive : 0 < d - withinDegree G U x := by
        omega
      let Enext : ℕ := E - (d - withinDegree G U x)
      have hnextCount : (withinEdges G (U.erase x)).card + Enext =
          d.choose 2 + d * ((U.erase x).card - d) := by
        dsimp only [Enext]
        omega
      have hnextSize : d + 3 ≤ (U.erase x).card := by
        omega
      have hnextBound : Enext ≤ (U.erase x).card - d - 3 := by
        dsimp only [Enext]
        omega
      obtain ⟨T, hTU, hTlower, hTsize, hTmin, Erem, hErem, hEremBound,
          hTcount, c, htrace, htraceCharge⟩ :=
        ih (U.erase x) (Finset.erase_ssubset hx)
          Enext hnextSize hnextBound hnextCount
      have htransfer : U.card - E ≤ (U.erase x).card - Enext := by
        dsimp only [Enext]
        omega
      have hnextLe : Enext ≤ E := by
        dsimp only [Enext]
        omega
      have hprefixLow : withinDegree G (U.erase x) x < d := by
        rw [withinDegree_self_erase]
        exact hxlow
      have hfresh : x ∉ U.erase x := by simp
      have hrestored : RestorationTrace G d T U
          (c + (d - withinDegree G U x)) := by
        have hsnoc := RestorationTrace.snoc htrace x hfresh hprefixLow
        rw [Finset.insert_erase hx, withinDegree_self_erase] at hsnoc
        exact hsnoc
      have hchargeExact : E = Erem + (c + (d - withinDegree G U x)) := by
        dsimp only [Enext] at htraceCharge
        omega
      exact ⟨T, hTU.trans (Finset.erase_subset x U),
        htransfer.trans hTlower, hTsize, hTmin,
        Erem, hErem.trans hnextLe, hEremBound, hTcount,
        c + (d - withinDegree G U x), hrestored, hchargeExact⟩
  exact hP S D hS hD hE

/-- Exact old public output, obtained by forgetting the remaining bound and trace.
No new premise, altered graph, altered chosen kernel or oracle is added. -/
theorem exists_actual_kernel_of_empty_core_deficit
    (G : SimpleGraph V) (d : ℕ) (S : Finset V) (D : ℕ)
    (hC : degreeCore G d = ∅)
    (hS : d + 3 ≤ S.card)
    (hD : D ≤ S.card - d - 3)
    (hE : (withinEdges G S).card + D =
      d.choose 2 + d * (S.card - d)) :
    ∃ T : Finset V, T ⊆ S ∧ S.card - D ≤ T.card ∧
      d + 3 ≤ T.card ∧
      (∀ x ∈ T, d ≤ withinDegree G T x) ∧
      ∃ Drem : ℕ, Drem ≤ D ∧
        (withinEdges G T).card + Drem =
          d.choose 2 + d * (T.card - d) := by
  obtain ⟨T, hTS, hTlower, hTsize, hTmin, Drem, hDrem, _hDremBound,
      hTcount, _c, _trace, _charge⟩ :=
    exists_actual_kernel_with_restoration_trace_of_empty_core_deficit
      G d S D hC hS hD hE
  exact ⟨T, hTS, hTlower, hTsize, hTmin, Drem, hDrem, hTcount⟩

end ErdosProblems.PathUpperReduction.RestorationTrace1105
end

end

noncomputable section

namespace ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Exact original cardinality, unordered-edge/charge, and excess ledgers.
All natural cardinality subtractions are guarded by the derived K subset U.
The nonnegative excess is constructed by Prop-valued trace induction. -/
theorem restoration_trace_ledgers
    (G : SimpleGraph V) (d : ℕ) (K U : Finset V) (c : ℕ)
    (htrace : RestorationTrace G d K U c) :
    K ⊆ U ∧
      U.card = K.card + (U.card - K.card) ∧
      (withinEdges G U).card + c =
        (withinEdges G K).card + d * (U.card - K.card) ∧
      ∃ w : ℕ, c = (U.card - K.card) + w := by
  classical
  induction htrace with
  | nil =>
      refine ⟨?_, ?_, ?_, 0, ?_⟩
      · intro x hx
        exact hx
      · simp
      · simp
      · simp
  | @snoc U c trace x hfresh hlow ih =>
      obtain ⟨hKU, hcard, hledger, w, hw⟩ := ih
      have hcardLe : K.card ≤ U.card := Finset.card_le_card hKU
      have hcardStep : (insert x U).card = U.card + 1 :=
        Finset.card_insert_of_notMem hfresh
      have hrStep : (insert x U).card - K.card =
          (U.card - K.card) + 1 := by
        omega
      have hrestoredErase : (insert x U).erase x = U :=
        Finset.erase_insert hfresh
      have hdegree := withinDegree_self_erase G (insert x U) x
      rw [hrestoredErase] at hdegree
      have hedgesStep := withinEdges_erase_ledger G (insert x U) x
        (Finset.mem_insert_self x U)
      rw [hrestoredErase, ← hdegree] at hedgesStep
      have hchargeCancel : withinDegree G U x +
          (d - withinDegree G U x) = d := by
        omega
      have hexcessStep : d - withinDegree G U x =
          1 + ((d - 1) - withinDegree G U x) := by
        omega
      have hnewLedger :
          (withinEdges G (insert x U)).card +
              (c + (d - withinDegree G U x)) =
            (withinEdges G K).card + d * ((U.card - K.card) + 1) := by
        calc
          (withinEdges G (insert x U)).card +
              (c + (d - withinDegree G U x)) =
              ((withinEdges G U).card + c) +
                (withinDegree G U x + (d - withinDegree G U x)) := by
                  rw [hedgesStep]
                  omega
          _ = ((withinEdges G K).card + d * (U.card - K.card)) + d := by
                rw [hledger, hchargeCancel]
          _ = (withinEdges G K).card +
                d * ((U.card - K.card) + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
                omega
      have hnewExcess : c + (d - withinDegree G U x) =
          ((U.card - K.card) + 1) +
            (w + ((d - 1) - withinDegree G U x)) := by
        omega
      refine ⟨hKU.trans (Finset.subset_insert x U), ?_, ?_,
        w + ((d - 1) - withinDegree G U x), ?_⟩
      · omega
      · rw [hrStep]
        exact hnewLedger
      · rw [hrStep]
        exact hnewExcess

/-- Each actual snoc increases the excess above one unit per restoration
by exactly its recorded original earlier-prefix defect. No list is supplied. -/
theorem restoration_trace_snoc_excess
    (G : SimpleGraph V) (d : ℕ) (K U : Finset V) (c : ℕ)
    (htrace : RestorationTrace G d K U c)
    (x : V) (hfresh : x ∉ U) (hlow : withinDegree G U x < d) :
    (c + (d - withinDegree G U x)) - ((insert x U).card - K.card) =
      (c - (U.card - K.card)) + ((d - 1) - withinDegree G U x) := by
  classical
  obtain ⟨hKU, _hcard, _hledger, w, hw⟩ :=
    restoration_trace_ledgers G d K U c htrace
  have hcardLe : K.card ≤ U.card := Finset.card_le_card hKU
  have hcardStep : (insert x U).card = U.card + 1 :=
    Finset.card_insert_of_notMem hfresh
  have hexcessStep : d - withinDegree G U x =
      1 + ((d - 1) - withinDegree G U x) := by
    omega
  omega

end ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
end

noncomputable section

namespace ErdosProblems.PathUpperReduction.ActualTraceCarrierCut1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105
open ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Internally choose an actual trace prefix of exactly m vertices and split
its cumulative charge. The prefix and suffix use the SAME original graph. -/
theorem exists_actual_restoration_trace_cut
    (G : SimpleGraph V) (d : ℕ) (K S : Finset V) (c : ℕ)
    (htrace : RestorationTrace G d K S c)
    (m : ℕ) (hKm : K.card ≤ m) (hmS : m ≤ S.card) :
    ∃ U : Finset V, ∃ a b : ℕ,
      K ⊆ U ∧ U ⊆ S ∧ U.card = m ∧
      RestorationTrace G d K U a ∧ RestorationTrace G d U S b ∧
      c = a + b := by
  classical
  induction htrace generalizing m with
  | nil =>
      have hm : K.card = m := by omega
      refine ⟨K, 0, 0, ?_, ?_, hm, RestorationTrace.nil,
        RestorationTrace.nil, ?_⟩
      · intro x hx
        exact hx
      · intro x hx
        exact hx
      · omega
  | @snoc T q trace x hfresh hlow ih =>
      have hcard : (insert x T).card = T.card + 1 :=
        Finset.card_insert_of_notMem hfresh
      by_cases hmT : m ≤ T.card
      · obtain ⟨U, a, b, hKU, hUT, hUm, hprefix, hsuffix, hq⟩ :=
          ih m hKm hmT
        refine ⟨U, a, b + (d - withinDegree G T x), hKU,
          hUT.trans (Finset.subset_insert x T), hUm, hprefix,
          RestorationTrace.snoc hsuffix x hfresh hlow, ?_⟩
        omega
      · have hm : (insert x T).card = m := by omega
        have hKT : K ⊆ T := (restoration_trace_ledgers G d K T q trace).1
        refine ⟨insert x T, q + (d - withinDegree G T x), 0,
          hKT.trans (Finset.subset_insert x T), ?_, hm,
          RestorationTrace.snoc trace x hfresh hlow, RestorationTrace.nil, ?_⟩
        · intro y hy
          exact hy
        · omega

omit [Fintype V] in
/-- Actual original restricted degrees increase under actual support
inclusion. -/
theorem withinDegree_le_of_subset [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (x : V) (hAB : A ⊆ B) :
    withinDegree G A x ≤ withinDegree G B x := by
  classical
  unfold withinDegree
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzA, hadj⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hAB hzA, hadj⟩

end ErdosProblems.PathUpperReduction.ActualTraceCarrierCut1105
end

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.AllLongSaturation

variable {V : Type*}

/-- A finite graph property admits a same-carrier inclusion-maximal supergraph. -/
theorem exists_saturated_property_supergraph [Finite V]
    (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H, G ≤ H ∧ Q H ∧ ∀ u v, u ≠ v → ¬ H.Adj u v →
      ¬ Q (H ⊔ fromEdgeSet {s(u, v)}) := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ Q H}
  have hfinite : S.Finite := Set.toFinite S
  obtain ⟨H, ⟨hH, hmax⟩⟩ := hfinite.exists_maximal ⟨G, le_refl G, hG⟩
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro u v huv hmissing hnew
  have hJ : H ⊔ fromEdgeSet {s(u, v)} ∈ S :=
    ⟨hH.1.trans le_sup_left, hnew⟩
  have hback : H ⊔ fromEdgeSet {s(u, v)} ≤ H := hmax hJ le_sup_left
  apply hmissing
  apply hback
  exact Or.inr (by simp [fromEdgeSet_adj, huv])

/-- Saturation excludes the entire family of long cycles, not one fixed order. -/
theorem exists_all_long_saturated_supergraph [Finite V]
    (G : SimpleGraph V) (K : ℕ)
    (hG : ∀ m, K ≤ m → (cycleGraph m).Free G) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      ∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)})) := by
  classical
  obtain ⟨H, hGH, hfree, hsat⟩ := exists_saturated_property_supergraph
    (fun H => ∀ m, K ≤ m → (cycleGraph m).Free H) G hG
  refine ⟨H, hGH, hfree, ?_⟩
  intro u v huv hmissing
  have h := hsat u v huv hmissing
  simp only [SimpleGraph.Free, SimpleGraph.IsContained] at h
  push Not at h
  exact h

/-- Deletion connectivity is retained on the same deleted-vertex carrier. -/
theorem deletion_connected_mono (G H : SimpleGraph V) (hGH : G ≤ H)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∀ z, (H.induce {w | w ≠ z}).Connected := by
  intro z
  apply SimpleGraph.Connected.mono _ (hdel z)
  intro a b hab
  exact hGH hab

/-- The saturated extension retains the actual deletion-connectivity hypothesis. -/
theorem exists_connected_all_long_saturated_supergraph [Finite V]
    (G : SimpleGraph V) (K : ℕ)
    (hG : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      ∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)})) := by
  obtain ⟨H, hGH, hfree, hsat⟩ := exists_all_long_saturated_supergraph G K hG
  exact ⟨H, hGH, hfree, deletion_connected_mono G H hGH hdel, hsat⟩

/-- Uniform Copy-freedom implies absence of every actual long cycle walk. -/
theorem no_long_cycle (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G) :
    ∀ q (C : G.Walk q q), C.IsCycle → C.length < K := by
  intro q C hC
  by_contra hsmall
  have hlen : K ≤ C.length := by omega
  apply hfree C.length hlen
  exact (cycleGraph_isContained_iff (by omega)).mpr ⟨q, C, hC, rfl⟩

variable {G : SimpleGraph V} {u v : V}

theorem edge_mem_old_of_ne_added_pair {e : Sym2 V}
    (he : e ∈ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet)
    (hne : e ≠ s(u, v)) : e ∈ G.edgeSet := by
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet] at he
  rcases he with he | he
  · exact he
  · exact (hne (Set.mem_singleton_iff.mp he.1)).elim

theorem cycle_oriented_at_pair {J : SimpleGraph V}
    (huv : u ≠ v) (C : J.Walk u u) (hc : C.IsCycle)
    (he : s(u, v) ∈ C.edges) :
    ∃ D : J.Walk u u, D.IsCycle ∧ D.length = C.length ∧ D.snd = v := by
  have hccons : (SimpleGraph.Walk.cons (C.adj_snd hc.not_nil) C.tail).IsCycle := by
    rw [SimpleGraph.Walk.cons_tail_eq C hc.not_nil]
    exact hc
  have hecons : s(u, v) ∈
      (SimpleGraph.Walk.cons (C.adj_snd hc.not_nil) C.tail).edges := by
    rw [SimpleGraph.Walk.cons_tail_eq C hc.not_nil]
    exact he
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hecons
  rcases hecons with hfirst | htail
  · have hsnd : C.snd = v := by
      rcases Sym2.eq_iff.mp hfirst with hsame | hswap
      · exact hsame.2.symm
      · exact (huv hswap.2.symm).elim
    exact ⟨C, hc, rfl, hsnd⟩
  · have hprev : v = C.tail.penultimate :=
      hc.isPath_tail.eq_penultimate_of_mem_edges htail
    have htailnil : ¬ C.tail.Nil :=
      SimpleGraph.Walk.not_nil_of_isCycle_cons hccons
    have hCprev : C.penultimate = C.tail.penultimate := by
      calc
        C.penultimate =
            (SimpleGraph.Walk.cons (C.adj_snd hc.not_nil) C.tail).penultimate := by
          rw [SimpleGraph.Walk.cons_tail_eq C hc.not_nil]
        _ = C.tail.penultimate :=
          SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ htailnil
    refine ⟨C.reverse, hc.reverse, by simp, ?_⟩
    rw [SimpleGraph.Walk.snd_reverse]
    exact hCprev.trans hprev.symm

theorem added_pair_path {m : ℕ}
    (hm : 2 < m) (hfree : (SimpleGraph.cycleGraph m).Free G)
    (huv : u ≠ v) (_hmissing : ¬ G.Adj u v)
    (f : (SimpleGraph.cycleGraph m).Copy
      (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)})) :
    ∃ P : G.Walk u v, P.IsPath ∧ P.length = m - 1 := by
  classical
  let J : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  obtain ⟨w, C, hc, hcm⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff hm).mp f.isContained
  have he : s(u, v) ∈ C.edges := by
    by_contra hnot
    have hEdges : ∀ e, e ∈ C.edges → e ∈ G.edgeSet := by
      intro e heC
      apply edge_mem_old_of_ne_added_pair (C.edges_subset_edgeSet heC)
      intro heq
      exact hnot (heq ▸ heC)
    have hcG : (C.transfer G hEdges).IsCycle := hc.transfer hEdges
    have hlenG : (C.transfer G hEdges).length = m := by
      simpa only [SimpleGraph.Walk.length_transfer] using hcm
    exact hfree ((SimpleGraph.cycleGraph_isContained_iff hm).mpr
      ⟨w, C.transfer G hEdges, hcG, hlenG⟩)
  have hu : u ∈ C.support := C.fst_mem_support_of_mem_edges he
  let D : J.Walk u u := C.rotate u hu
  have hcD : D.IsCycle := by
    simpa only [D] using hc.rotate hu
  have hlenD : D.length = m := by
    simpa only [D] using (C.length_rotate u hu).trans hcm
  have heD : s(u, v) ∈ D.edges := by
    exact ((C.rotate_edges u hu).perm.mem_iff).mpr he
  obtain ⟨E, hcE, hlenE, hsnd⟩ := cycle_oriented_at_pair huv D hcD heD
  have hcEcons : (SimpleGraph.Walk.cons (E.adj_snd hcE.not_nil) E.tail).IsCycle := by
    rw [SimpleGraph.Walk.cons_tail_eq E hcE.not_nil]
    exact hcE
  have havoid : s(u, v) ∉ E.tail.edges := by
    have h := (SimpleGraph.Walk.cons_isCycle_iff E.tail
      (E.adj_snd hcE.not_nil)).mp hcEcons
    simpa only [hsnd] using h.2
  let T : J.Walk v u := E.tail.copy hsnd rfl
  have hpT : T.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy E.tail hsnd rfl).mpr hcE.isPath_tail
  have hTold : ∀ e, e ∈ T.edges → e ∈ G.edgeSet := by
    intro e heT
    have heTail : e ∈ E.tail.edges := by simpa only [T, SimpleGraph.Walk.edges_copy] using heT
    apply edge_mem_old_of_ne_added_pair (E.tail.edges_subset_edgeSet heTail)
    intro heq
    exact havoid (heq ▸ heTail)
  refine ⟨(T.transfer G hTold).reverse, (hpT.transfer hTold).reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_transfer,
    T, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_tail]
  rw [hlenE, hlenD]

end ErdosProblems.PathUpperReduction.AllLongSaturation

end

section

namespace SimpleGraph

def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m | ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

end SimpleGraph

namespace Erdos1105.GraphHelpers

/-- The properties of a finite normal DFS forest needed by the coloring proof.
They require actual simple graph paths, not merely numerical depth labels. -/
structure NormalDepth {V : Type*} (G : SimpleGraph V) where
  depth : V → ℕ
  edge_ne : ∀ {u v}, G.Adj u v → depth u ≠ depth v
  earlier_injective : ∀ {v u w}, G.Adj u v → G.Adj w v →
    depth u < depth v → depth w < depth v → depth u = depth w → u = w
  back_path : ∀ {u v}, G.Adj u v → depth u < depth v →
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = depth v - depth u

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Closing a simple path of length at least two by an edge gives a cycle. -/
theorem cycle_of_path_and_edge {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (h : G.Adj v u) (hlen : 2 ≤ p.length) :
    (Walk.cons h p).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simpa using hp
  · simp only [Walk.length_cons]
    omega

/-- An edge between vertices of equal depth parity closes an actual odd cycle. -/
theorem same_parity_back_edge (D : NormalDepth G) {u v : V}
    (h : G.Adj u v) (hlt : D.depth u < D.depth v)
    (hpar : D.depth u % 2 = D.depth v % 2) :
    D.depth v - D.depth u + 1 ∈ G.oddCycleLengths := by
  obtain ⟨p, hp, hlen⟩ := D.back_path h hlt
  have htwo : 2 ≤ p.length := by omega
  refine ⟨⟨v, Walk.cons h.symm p,
    cycle_of_path_and_edge p hp h.symm htwo, ?_⟩, ?_⟩
  · simp [hlen]
  · rw [Nat.odd_iff]
    omega

def earlierParityNeighbors (D : NormalDepth G) (v : V) : Set V :=
  {u | G.Adj u v ∧ D.depth u < D.depth v ∧ D.depth u % 2 = D.depth v % 2}

/-- Earlier same-parity neighbors inject into the set of odd cycle lengths. -/
theorem earlier_parity_neighbors_bound [Finite V] (D : NormalDepth G)
    (hfin : G.oddCycleLengths.Finite) (v : V) :
    (earlierParityNeighbors D v).ncard ≤ G.oddCycleLengths.ncard := by
  classical
  let f : V → ℕ := fun u ↦ D.depth v - D.depth u + 1
  have hmaps : Set.MapsTo f (earlierParityNeighbors D v) G.oddCycleLengths := by
    intro u hu
    exact same_parity_back_edge D hu.1 hu.2.1 hu.2.2
  have hinj : Set.InjOn f (earlierParityNeighbors D v) := by
    intro u hu w hw heq
    apply D.earlier_injective hu.1 hw.1 hu.2.1 hw.2.1
    dsimp [f] at heq
    have hu_lt : D.depth u < D.depth v := hu.2.1
    have hw_lt : D.depth w < D.depth v := hw.2.1
    omega
  exact Set.ncard_le_ncard_of_injOn f hmaps hinj hfin

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b x : V}

def cycleWithoutRoot (c : G.Walk x x) (_hc : c.IsCycle) :
    G.Walk c.snd c.tail.penultimate := c.tail.dropLast

theorem cycleWithoutRoot_isPath (c : G.Walk x x) (hc : c.IsCycle) :
    (cycleWithoutRoot c hc).IsPath := hc.isPath_tail.dropLast

theorem cycleWithoutRoot_tail_notNil (c : G.Walk x x) (hc : c.IsCycle) :
    ¬c.tail.Nil := by
  rw [Walk.not_nil_iff_lt_length, Walk.length_tail]
  have := hc.three_le_length
  omega

theorem cycleWithoutRoot_root_notMem (c : G.Walk x x) (hc : c.IsCycle) :
    x ∉ (cycleWithoutRoot c hc).support := by
  have ht := cycleWithoutRoot_tail_notNil c hc
  have hNodup : ((cycleWithoutRoot c hc).support ++ [x]).Nodup := by
    rw [cycleWithoutRoot, Walk.support_dropLast_concat ht]
    exact hc.isPath_tail.support_nodup
  intro hx
  exact (List.nodup_append.mp hNodup).2.2 x hx x (by simp) rfl

theorem cycleWithoutRoot_length (c : G.Walk x x) (hc : c.IsCycle) :
    (cycleWithoutRoot c hc).length = c.length - 2 := by
  simp [cycleWithoutRoot, Walk.length_dropLast, Walk.length_tail, Nat.sub_sub]

theorem cycleWithoutRoot_first_edge (c : G.Walk x x) (hc : c.IsCycle) :
    G.Adj x c.snd := c.adj_snd hc.not_nil

theorem cycleWithoutRoot_last_edge (c : G.Walk x x) (hc : c.IsCycle) :
    G.Adj x c.tail.penultimate :=
  (c.tail.adj_penultimate (cycleWithoutRoot_tail_notNil c hc)).symm

theorem cycleWithoutRoot_mem_of_ne (c : G.Walk x x) (hc : c.IsCycle)
    {u : V} (hux : u ≠ x) (hu : u ∈ c.support) :
    u ∈ (cycleWithoutRoot c hc).support := by
  rw [← Walk.cons_support_tail hc.not_nil] at hu
  rcases List.mem_cons.mp hu with hEq | hu
  · exact (hux hEq).elim
  · rw [← Walk.support_dropLast_concat (cycleWithoutRoot_tail_notNil c hc)] at hu
    simpa [cycleWithoutRoot, hux] using hu

theorem cycleWithoutRoot_covers_neighbors (c : G.Walk x x) (hc : c.IsCycle)
    (hcover : ∀ u, G.Adj x u → u ∈ c.support) :
    ∀ u, G.Adj x u → u ∈ (cycleWithoutRoot c hc).support := by
  intro u hu
  exact cycleWithoutRoot_mem_of_ne c hc hu.ne.symm (hcover u hu)

/-- All path positions adjacent to an external vertex. -/
noncomputable def pathNeighborPositions (p : G.Walk a b) (x : V) : Finset ℕ := by
  classical
  exact (Finset.range (p.length + 1)).filter (fun i ↦ G.Adj x (p.getVert i))

@[simp] theorem mem_pathNeighborPositions (p : G.Walk a b) (x : V) (i : ℕ) :
    i ∈ pathNeighborPositions p x ↔ i ≤ p.length ∧ G.Adj x (p.getVert i) := by
  classical
  simp [pathNeighborPositions]

/-- Covering the entire neighborhood by a simple path preserves its exact
cardinality when vertices are replaced by their unique path positions. -/
theorem pathNeighborPositions_card (p : G.Walk a b) (hp : p.IsPath)
    (hcover : ∀ u, G.Adj x u → u ∈ p.support) :
    (pathNeighborPositions p x).card = (G.neighborSet x).ncard := by
  have hBij : Set.BijOn p.getVert (pathNeighborPositions p x : Set ℕ)
      (G.neighborSet x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact (mem_pathNeighborPositions p x i).mp hi |>.2
    · intro i hi j hj hEq
      exact hp.getVert_injOn
        ((mem_pathNeighborPositions p x i).mp hi).1
        ((mem_pathNeighborPositions p x j).mp hj).1 hEq
    · intro u hu
      obtain ⟨i, hGet, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover u hu)
      refine ⟨i, (mem_pathNeighborPositions p x i).mpr ⟨hi, ?_⟩, hGet⟩
      simpa [hGet] using hu
  simpa using hBij.ncard_eq

/-- The interval from position i to position j, with the original endpoint
vertices rather than endpoints of an intermediate take/drop operation. -/
def pathInterval (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.take j).drop i).copy
    (by simp [Walk.take_getVert, Nat.min_eq_right hij]) rfl

theorem pathInterval_isPath (p : G.Walk a b) (hp : p.IsPath)
    (i j : ℕ) (hij : i ≤ j) : (pathInterval p i j hij).IsPath := by
  exact (Walk.isPath_copy _ _ _).mpr ((hp.take j).drop i)

theorem pathInterval_length (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ p.length) : (pathInterval p i j hij).length = j - i := by
  simp [pathInterval, Walk.drop_length, Walk.take_length, Nat.min_eq_left hj]

theorem pathInterval_support_subset (p : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    (pathInterval p i j hij).support ⊆ p.support := by
  intro y hy
  simp only [pathInterval, Walk.support_copy, Walk.drop_support_eq_support_drop_min,
    Walk.support_take] at hy
  exact List.mem_of_mem_take (List.mem_of_mem_drop hy)

/-- Two neighbors of an outside vertex, at distinct path positions,
give an actual simple cycle of length j-i+2. -/
theorem fan_cycle_witness (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j)) :
    ∃ q : G.Walk (p.getVert j) (p.getVert j),
      q.IsCycle ∧ q.length = j - i + 2 := by
  let r := pathInterval p i j hij.le
  have hr : r.IsPath := pathInterval_isPath p hp i j hij.le
  have hxr : x ∉ r.support := fun h ↦ hx (pathInterval_support_subset p i j hij.le h)
  have hPath : (Walk.cons hxi r).IsPath := hr.cons hxr
  have hrlen : r.length = j - i := pathInterval_length p i j hij.le hj
  refine ⟨Walk.cons hxj.symm (Walk.cons hxi r), ?_, ?_⟩
  · apply cycle_of_path_and_edge (Walk.cons hxi r) hPath hxj.symm
    simp only [Walk.length_cons]
    omega
  · simp only [Walk.length_cons, hrlen]

/-- Opposite-parity neighbor positions yield the corresponding original
odd simple-cycle length. -/
theorem fan_odd_cycle_length (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j))
    (hParity : i % 2 ≠ j % 2) : j - i + 2 ∈ G.oddCycleLengths := by
  obtain ⟨q, hq, hlen⟩ := fan_cycle_witness p hp hx hij hj hxi hxj
  refine ⟨⟨p.getVert j, q, hq, hlen⟩, ?_⟩
  rw [Nat.odd_iff]
  omega

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b c : V}

theorem path_start_notMem_tail (p : G.Walk a b) (hp : p.IsPath) :
    a ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

theorem path_append_of_meet_only (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z, z ∈ p.support → z ∈ q.support → z = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  apply hp.support_nodup.append hq.support_nodup.tail
  intro z hz₁ hz₂
  have hzb := hmeet z hz₁ (List.mem_of_mem_tail hz₂)
  exact path_start_notMem_tail q hq (hzb ▸ hz₂)

theorem cycle_of_two_paths (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hlen : 3 ≤ p.length + q.length) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · intro z hz₁ hz₂
    have hzp := List.mem_of_mem_tail hz₁
    have hzq : z ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hz₂
    rcases hmeet z hzp hzq with hza | hzb
    · exact path_start_notMem_tail p hp (hza ▸ hz₁)
    · exact path_start_notMem_tail q.reverse hq.reverse (hzb ▸ hz₂)
  · rw [Walk.length_reverse]
    omega

theorem two_paths_cycle_length (p q : G.Walk a b) :
    (p.append q.reverse).length = p.length + q.length := by simp

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace TwoConnector

/-- Stop a walk at its first visit to a set containing its end vertex. -/
theorem first_hit {a b : V} (p : G.Walk a b) (s : Set V) (hb : b ∈ s) :
    ∃ u ∈ s, ∃ q : G.Walk a u, ∃ r : G.Walk u b,
      p = q.append r ∧ ∀ z, z ∈ q.support → z ∈ s → z = u := by
  classical
  induction p with
  | nil =>
      exact ⟨_, hb, .nil, .nil, rfl, by simp⟩
  | @cons a c b hac p ih =>
      by_cases ha : a ∈ s
      · exact ⟨a, ha, .nil, .cons hac p, rfl, by simp⟩
      · obtain ⟨u, hu, q, r, hqr, hfirst⟩ := ih hb
        refine ⟨u, hu, .cons hac q, r, ?_, ?_⟩
        · simp only [Walk.cons_append, ← hqr]
        · intro z hz hzs
          rcases List.mem_cons.mp hz with hza | hzq
          · exact (ha (hza ▸ hzs)).elim
          · exact hfirst z hzq hzs

/-- The two halves of a simple path meet only at the splitting vertex. -/
theorem split_meet [DecidableEq V] {a b u : V} {p : G.Walk a b} (hp : p.IsPath)
    (hu : u ∈ p.support) {z : V}
    (hz₁ : z ∈ (p.takeUntil u hu).support)
    (hz₂ : z ∈ (p.dropUntil u hu).support) : z = u := by
  classical
  by_contra hzu
  have hpath : ((p.takeUntil u hu).append (p.dropUntil u hu)).IsPath := by
    simpa only [Walk.take_spec] using hp
  exact hpath.ne_of_mem_support_of_append hzu hz₁ hz₂ rfl

/-- A tripod consists of a stem and two branches, meeting only at the center. -/
structure Tripod (G : SimpleGraph V) (x b₁ b₂ v : V) where
  stem : G.Walk x v
  leg₁ : G.Walk v b₁
  leg₂ : G.Walk v b₂
  stem_path : stem.IsPath
  leg₁_path : leg₁.IsPath
  leg₂_path : leg₂.IsPath
  stem_leg₁ : ∀ z, z ∈ stem.support → z ∈ leg₁.support → z = v
  stem_leg₂ : ∀ z, z ∈ stem.support → z ∈ leg₂.support → z = v
  legs : ∀ z, z ∈ leg₁.support → z ∈ leg₂.support → z = v

theorem tripod_exists (hG : G.Connected) (x b₁ b₂ : V) :
    ∃ v, Nonempty (Tripod G x b₁ b₂ v) := by
  classical
  obtain ⟨p, hp⟩ := (hG b₁ b₂).exists_isPath
  obtain ⟨r, hr⟩ := (hG x b₁).exists_isPath
  obtain ⟨v, hv, q, t, hqt, hfirst⟩ :=
    first_hit r {z | z ∈ p.support} p.start_mem_support
  have hq : q.IsPath := by
    rw [hqt] at hr
    exact hr.of_append_left
  refine ⟨v, ⟨{
    stem := q
    leg₁ := (p.takeUntil v hv).reverse
    leg₂ := p.dropUntil v hv
    stem_path := hq
    leg₁_path := (hp.takeUntil hv).reverse
    leg₂_path := hp.dropUntil hv
    stem_leg₁ := ?_
    stem_leg₂ := ?_
    legs := ?_ }⟩⟩
  · intro z hzq hzp
    simp only [Walk.support_reverse, List.mem_reverse] at hzp
    exact hfirst z hzq (p.support_takeUntil_subset_support hv hzp)
  · intro z hzq hzp
    exact hfirst z hzq (p.support_dropUntil_subset_support hv hzp)
  · intro z hz₁ hz₂
    simp only [Walk.support_reverse, List.mem_reverse] at hz₁
    exact split_meet hp hv hz₁ hz₂

theorem path_avoiding_deleted
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b v : V} (hav : a ≠ v) (hbv : b ≠ v) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ z, z ∈ p.support → z ≠ v := by
  classical
  obtain ⟨p⟩ := hdel v ⟨a, hav⟩ ⟨b, hbv⟩
  let q : G.Walk a b := p.map (Embedding.induce {w | w ≠ v}).toHom
  refine ⟨q.bypass, q.bypass_isPath, ?_⟩
  intro z hz
  have hzq := q.support_bypass_subset_support hz
  change z ∈ (p.map (Embedding.induce {w | w ≠ v}).toHom).support at hzq
  rw [Walk.support_map] at hzq
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hzq
  exact u.property

def Tripod.swap {x b₁ b₂ v : V} (T : Tripod G x b₁ b₂ v) : Tripod G x b₂ b₁ v where
  stem := T.stem
  leg₁ := T.leg₂
  leg₂ := T.leg₁
  stem_path := T.stem_path
  leg₁_path := T.leg₂_path
  leg₂_path := T.leg₁_path
  stem_leg₁ := T.stem_leg₂
  stem_leg₂ := T.stem_leg₁
  legs := fun z hz₂ hz₁ => T.legs z hz₁ hz₂

/-- Repeated vertices in the spliced walks are bypassed. -/
theorem tripod_shift {x b₁ b₂ v w u : V} (T : Tripod G x b₁ b₂ v)
    (hw : w ∈ T.stem.support) (hu : u ∈ T.leg₁.support)
    (hwv : w ≠ v) (huv : u ≠ v) (s : G.Walk w u)
    (hsstem : ∀ z, z ∈ s.support → z ∈ T.stem.support → z = w)
    (hslegs : ∀ z, z ∈ s.support →
      (z ∈ T.leg₁.support ∨ z ∈ T.leg₂.support) → z = u) :
    ∃ U : Tripod G x b₁ b₂ w, U.stem.length < T.stem.length := by
  classical
  have hvpre : v ∉ (T.stem.takeUntil w hw).support :=
    Walk.endpoint_notMem_support_takeUntil T.stem_path hw hwv.symm
  have hvsuffix : v ∉ (T.leg₁.dropUntil u hu).support := by
    intro hv
    have heq := split_meet T.leg₁_path hu (T.leg₁.takeUntil u hu).start_mem_support hv
    exact huv heq.symm
  have hunot₂ : u ∉ T.leg₂.support := by
    intro hu₂
    exact huv (T.legs u hu hu₂)
  let p := T.stem.takeUntil w hw
  let q₁ := (s.append (T.leg₁.dropUntil u hu)).bypass
  let q₂ := ((T.stem.dropUntil w hw).append T.leg₂).bypass
  have hp : p.IsPath := T.stem_path.takeUntil hw
  have hpq₁ : ∀ z, z ∈ p.support → z ∈ q₁.support → z = w := by
    intro z hzp hzq
    have hzstem := T.stem.support_takeUntil_subset_support hw hzp
    rcases (Walk.mem_support_append_iff _ _).mp
        ((s.append (T.leg₁.dropUntil u hu)).support_bypass_subset_support hzq) with hzs | hzleg
    · exact hsstem z hzs hzstem
    · have hz₁ := T.leg₁.support_dropUntil_subset_support hu hzleg
      have hzv := T.stem_leg₁ z hzstem hz₁
      exact (hvsuffix (hzv ▸ hzleg)).elim
  have hpq₂ : ∀ z, z ∈ p.support → z ∈ q₂.support → z = w := by
    intro z hzp hzq
    change z ∈ (T.stem.takeUntil w hw).support at hzp
    rcases (Walk.mem_support_append_iff _ _).mp
        (((T.stem.dropUntil w hw).append T.leg₂).support_bypass_subset_support hzq)
        with hzstem | hzleg
    · exact split_meet T.stem_path hw hzp hzstem
    · have hzv := T.stem_leg₂ z (T.stem.support_takeUntil_subset_support hw hzp) hzleg
      exact (hvpre (hzv ▸ hzp)).elim
  have hq₁q₂ : ∀ z, z ∈ q₁.support → z ∈ q₂.support → z = w := by
    intro z hz₁ hz₂
    rcases (Walk.mem_support_append_iff _ _).mp
        ((s.append (T.leg₁.dropUntil u hu)).support_bypass_subset_support hz₁)
        with hzs | hzleg₁
    · rcases (Walk.mem_support_append_iff _ _).mp
          (((T.stem.dropUntil w hw).append T.leg₂).support_bypass_subset_support hz₂)
          with hzstem | hzleg₂
      · exact hsstem z hzs (T.stem.support_dropUntil_subset_support hw hzstem)
      · have hzu := hslegs z hzs (Or.inr hzleg₂)
        exact (hunot₂ (hzu ▸ hzleg₂)).elim
    · have hzleg := T.leg₁.support_dropUntil_subset_support hu hzleg₁
      rcases (Walk.mem_support_append_iff _ _).mp
          (((T.stem.dropUntil w hw).append T.leg₂).support_bypass_subset_support hz₂)
          with hzstem | hzleg₂
      · have hzv := T.stem_leg₁ z (T.stem.support_dropUntil_subset_support hw hzstem) hzleg
        exact (hvsuffix (hzv ▸ hzleg₁)).elim
      · have hzv := T.legs z hzleg hzleg₂
        exact (hvsuffix (hzv ▸ hzleg₁)).elim
  refine ⟨{
    stem := p
    leg₁ := q₁
    leg₂ := q₂
    stem_path := hp
    leg₁_path := (s.append (T.leg₁.dropUntil u hu)).bypass_isPath
    leg₂_path := ((T.stem.dropUntil w hw).append T.leg₂).bypass_isPath
    stem_leg₁ := hpq₁
    stem_leg₂ := hpq₂
    legs := hq₁q₂ }, ?_⟩
  exact Walk.length_takeUntil_lt_length hw hwv

theorem tripod_shortens_to_leg₁
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x b₁ b₂ v : V} (T : Tripod G x b₁ b₂ v)
    (hvx : v ≠ x) (hbv : b₁ ≠ v) :
    ∃ w, ∃ U : Tripod G x b₁ b₂ w, U.stem.length < T.stem.length := by
  classical
  obtain ⟨r, hr, havoid⟩ := path_avoiding_deleted hdel hvx.symm hbv
  obtain ⟨u, hu, q, l, hq, hfirst⟩ :=
    first_hit r {z | z ∈ T.leg₁.support ∨ z ∈ T.leg₂.support}
      (Or.inl T.leg₁.end_mem_support)
  have hqsub : ∀ z, z ∈ q.support → z ∈ r.support := by
    intro z hz
    rw [hq]
    exact Walk.support_subset_support_append_left _ _ hz
  have huv : u ≠ v := havoid u (hqsub u q.end_mem_support)
  obtain ⟨w, hw, t, k, ht, hstem⟩ :=
    first_hit q.reverse {z | z ∈ T.stem.support} T.stem.start_mem_support
  let s := t.reverse
  have hssub : ∀ z, z ∈ s.support → z ∈ q.support := by
    intro z hz
    have hzt : z ∈ t.support := by
      simpa only [s, Walk.support_reverse, List.mem_reverse] using hz
    have hzq : z ∈ q.reverse.support := by
      rw [ht]
      exact Walk.support_subset_support_append_left _ _ hzt
    simpa only [Walk.support_reverse, List.mem_reverse] using hzq
  have hwv : w ≠ v := havoid w (hqsub w (hssub w s.start_mem_support))
  have hsstem : ∀ z, z ∈ s.support → z ∈ T.stem.support → z = w := by
    intro z hz hs
    apply hstem z _ hs
    simpa only [s, Walk.support_reverse, List.mem_reverse] using hz
  have hslegs : ∀ z, z ∈ s.support →
      (z ∈ T.leg₁.support ∨ z ∈ T.leg₂.support) → z = u := by
    intro z hz hlegs
    exact hfirst z (hssub z hz) hlegs
  rcases hu with hu₁ | hu₂
  · obtain ⟨U, hU⟩ := tripod_shift T hw hu₁ hwv huv s hsstem hslegs
    exact ⟨w, U, hU⟩
  · obtain ⟨U, hU⟩ := tripod_shift T.swap hw hu₂ hwv huv s hsstem
      (fun z hz hlegs => hslegs z hz hlegs.symm)
    exact ⟨w, U.swap, hU⟩

theorem tripod_shortens
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x b₁ b₂ v : V} (T : Tripod G x b₁ b₂ v)
    (hvx : v ≠ x) (hb : b₁ ≠ b₂) :
    ∃ w, ∃ U : Tripod G x b₁ b₂ w, U.stem.length < T.stem.length := by
  by_cases hbv : b₁ = v
  · obtain ⟨w, U, hU⟩ := tripod_shortens_to_leg₁ hdel T.swap hvx (by
      intro hb₂v
      exact hb (hbv.trans hb₂v.symm))
    exact ⟨w, U.swap, hU⟩
  · exact tripod_shortens_to_leg₁ hdel T hvx hbv

end TwoConnector

/-- Two simple paths from a vertex to two distinct targets meet only at their
common starting vertex. The proof uses only connectivity after each deletion. -/
theorem twoFan (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (x b₁ b₂ : V) (hb : b₁ ≠ b₂) :
    ∃ p₁ : G.Walk x b₁, ∃ p₂ : G.Walk x b₂,
      p₁.IsPath ∧ p₂.IsPath ∧
      ∀ z, z ∈ p₁.support → z ∈ p₂.support → z = x := by
  classical
  obtain ⟨v, ⟨T⟩⟩ := TwoConnector.tripod_exists hG x b₁ b₂
  have hex : ∃ m : ℕ, ∃ v, ∃ T : TwoConnector.Tripod G x b₁ b₂ v,
      T.stem.length = m := ⟨T.stem.length, v, T, rfl⟩
  obtain ⟨v, T, hT⟩ := Nat.find_spec hex
  have hv : v = x := by
    by_contra hvx
    obtain ⟨w, U, hU⟩ := TwoConnector.tripod_shortens hdel T hvx hb
    have hmin := Nat.find_min' hex (show
      ∃ v, ∃ T : TwoConnector.Tripod G x b₁ b₂ v, T.stem.length = U.stem.length
      from ⟨w, U, rfl⟩)
    omega
  subst v
  exact ⟨T.leg₁, T.leg₂, T.leg₁_path, T.leg₂_path, T.legs⟩

namespace TwoConnector

/-- Trim a simple walk so that it visits either endpoint set only at its
corresponding endpoint. The trimmed support is contained in the original one. -/
theorem trim_between_sets {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (A B : Set V) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ a' ∈ A, ∃ b' ∈ B, ∃ q : G.Walk a' b', q.IsPath ∧
      (∀ z, z ∈ q.support → z ∈ p.support) ∧
      (∀ z, z ∈ q.support → z ∈ A → z = a') ∧
      (∀ z, z ∈ q.support → z ∈ B → z = b') := by
  classical
  obtain ⟨b', hb', q, r, hqr, hB⟩ := first_hit p B hb
  have hq : q.IsPath := by
    rw [hqr] at hp
    exact hp.of_append_left
  obtain ⟨a', ha', t, k, htk, hA⟩ := first_hit q.reverse A ha
  have ht : t.IsPath := by
    have hrev := hq.reverse
    rw [htk] at hrev
    exact hrev.of_append_left
  have hsub : ∀ z, z ∈ t.reverse.support → z ∈ q.support := by
    intro z hz
    have hzt : z ∈ t.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hz
    have hzq : z ∈ q.reverse.support := by
      rw [htk]
      exact Walk.support_subset_support_append_left _ _ hzt
    simpa only [Walk.support_reverse, List.mem_reverse] using hzq
  refine ⟨a', ha', b', hb', t.reverse, ht.reverse, ?_, ?_, ?_⟩
  · intro z hz
    rw [hqr]
    exact Walk.support_subset_support_append_left _ _ (hsub z hz)
  · intro z hz hza
    apply hA z _ hza
    simpa only [Walk.support_reverse, List.mem_reverse] using hz
  · intro z hz hzb
    exact hB z (hsub z hz) hzb

/-- Attach a path reaching one branch of a fan to that branch. -/
theorem attach_fan_leg {x c b₁ b₂ u : V}
    (p₁ : G.Walk x b₁) (p₂ : G.Walk x b₂) (hp₁ : p₁.IsPath)
    (hmeet : ∀ z, z ∈ p₁.support → z ∈ p₂.support → z = x)
    (hu : u ∈ p₁.support) (hux : u ≠ x) (q : G.Walk c u)
    (hfirst : ∀ z, z ∈ q.support →
      (z ∈ p₁.support ∨ z ∈ p₂.support) → z = u) :
    ∃ r : G.Walk c b₁, r.IsPath ∧
      ∀ z, z ∈ p₂.support → z ∈ r.support → False := by
  classical
  have hunot : u ∉ p₂.support := fun hu₂ => hux (hmeet u hu hu₂)
  have hxdrop : x ∉ (p₁.dropUntil u hu).support := by
    intro hx
    have heq := split_meet hp₁ hu (p₁.takeUntil u hu).start_mem_support hx
    exact hux heq.symm
  let r := (q.append (p₁.dropUntil u hu)).bypass
  refine ⟨r, (q.append (p₁.dropUntil u hu)).bypass_isPath, ?_⟩
  intro z hz₂ hzr
  rcases (Walk.mem_support_append_iff _ _).mp
      ((q.append (p₁.dropUntil u hu)).support_bypass_subset_support hzr)
      with hzq | hzdrop
  · have hzu := hfirst z hzq (Or.inr hz₂)
    exact hunot (hzu ▸ hz₂)
  · have hz₁ := p₁.support_dropUntil_subset_support hu hzdrop
    have hzx := hmeet z hz₁ hz₂
    exact hxdrop (hzx ▸ hzdrop)

end TwoConnector

/-- Two disjoint sets containing distinct pairs admit two vertex-disjoint
simple connectors. Each connector meets the endpoint sets only at its ends. -/
theorem twoConnectors (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (A B : Set V) (hAB : Disjoint A B)
    (hA : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂)
    (hB : ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      ∃ p₁ : G.Walk a₁ b₁, ∃ p₂ : G.Walk a₂ b₂,
        p₁.IsPath ∧ p₂.IsPath ∧
        (∀ z, z ∈ p₁.support → z ∈ p₂.support → False) ∧
        (∀ z, z ∈ p₁.support → z ∈ A → z = a₁) ∧
        (∀ z, z ∈ p₁.support → z ∈ B → z = b₁) ∧
        (∀ z, z ∈ p₂.support → z ∈ A → z = a₂) ∧
        (∀ z, z ∈ p₂.support → z ∈ B → z = b₂) := by
  classical
  obtain ⟨a₁, ha₁, a₂, ha₂, haa⟩ := hA
  obtain ⟨b₁, hb₁, b₂, hb₂, hbb⟩ := hB
  obtain ⟨p₁, p₂, hp₁, hp₂, hmeet⟩ := twoFan hG hdel a₁ b₁ b₂ hbb
  have hb₁a₁ : b₁ ≠ a₁ := by
    intro h
    subst b₁
    exact Set.disjoint_left.mp hAB ha₁ hb₁
  obtain ⟨r, hr, havoid⟩ := TwoConnector.path_avoiding_deleted hdel haa.symm hb₁a₁
  obtain ⟨u, hu, q, l, hq, hfirst⟩ :=
    TwoConnector.first_hit r {z | z ∈ p₁.support ∨ z ∈ p₂.support}
      (Or.inl p₁.end_mem_support)
  have hqsub : ∀ z, z ∈ q.support → z ∈ r.support := by
    intro z hz
    rw [hq]
    exact Walk.support_subset_support_append_left _ _ hz
  have hux : u ≠ a₁ := havoid u (hqsub u q.end_mem_support)
  have hpair : ∃ y₁ ∈ B, ∃ y₂ ∈ B,
      ∃ t₁ : G.Walk a₁ y₁, ∃ t₂ : G.Walk a₂ y₂,
        t₁.IsPath ∧ t₂.IsPath ∧
        ∀ z, z ∈ t₁.support → z ∈ t₂.support → False := by
    rcases hu with hu₁ | hu₂
    · obtain ⟨t, ht, hdisj⟩ :=
        TwoConnector.attach_fan_leg p₁ p₂ hp₁ hmeet hu₁ hux q hfirst
      exact ⟨b₂, hb₂, b₁, hb₁, p₂, t, hp₂, ht, hdisj⟩
    · obtain ⟨t, ht, hdisj⟩ :=
        TwoConnector.attach_fan_leg p₂ p₁ hp₂
          (fun z hz₂ hz₁ => hmeet z hz₁ hz₂) hu₂ hux q
          (fun z hz hlegs => hfirst z hz hlegs.symm)
      exact ⟨b₁, hb₁, b₂, hb₂, p₁, t, hp₁, ht, hdisj⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, t₁, t₂, ht₁, ht₂, hdisj⟩ := hpair
  obtain ⟨a₁', ha₁', b₁', hb₁', q₁, hq₁, hsub₁, hA₁, hB₁⟩ :=
    TwoConnector.trim_between_sets t₁ ht₁ A B ha₁ hy₁
  obtain ⟨a₂', ha₂', b₂', hb₂', q₂, hq₂, hsub₂, hA₂, hB₂⟩ :=
    TwoConnector.trim_between_sets t₂ ht₂ A B ha₂ hy₂
  have hd : ∀ z, z ∈ q₁.support → z ∈ q₂.support → False := by
    intro z hz₁ hz₂
    exact hdisj z (hsub₁ z hz₁) (hsub₂ z hz₂)
  have ha' : a₁' ≠ a₂' := by
    intro h
    exact hd a₁' q₁.start_mem_support (h.symm ▸ q₂.start_mem_support)
  have hb' : b₁' ≠ b₂' := by
    intro h
    exact hd b₁' q₁.end_mem_support (h.symm ▸ q₂.end_mem_support)
  exact ⟨a₁', ha₁', a₂', ha₂', b₁', hb₁', b₂', hb₂', ha', hb',
    q₁, q₂, hq₁, hq₂, hd, hA₁, hB₁, hA₂, hB₂⟩

end Erdos1105.GraphHelpers

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Deletion connectivity at one internal position of an injective ordering
gives a simple detour across that position. The detour contacts the entire
ordered vertex range only at its two attachments. No adjacency of successive
ordered vertices, ambient finiteness, or connectivity after other deletions is
assumed. -/
theorem exists_internal_cut_detour
    {V : Type*} {G : SimpleGraph V} {s : ℕ}
    (p : Fin (s + 1) → V) (hp : Function.Injective p)
    (i : Fin (s + 1)) (hi0 : (0 : Fin (s + 1)) < i)
    (hilast : i < Fin.last s)
    (hdel : (G.induce {w | w ≠ p i}).Connected) :
    ∃ a b : Fin (s + 1), a < i ∧ i < b ∧
      ∃ q : G.Walk (p a) (p b), q.IsPath ∧
        (∀ z, z ∈ q.support → z ≠ p i) ∧
        (∀ j, p j ∈ q.support → j = a ∨ j = b) ∧
        (∀ z, z ∈ q.support → z ∈ Set.range p → z = p a ∨ z = p b) := by
  classical
  have h0 : p (0 : Fin (s + 1)) ≠ p i := by
    intro h
    exact (ne_of_lt hi0) (hp h)
  have hlast : p (Fin.last s) ≠ p i := by
    intro h
    exact (ne_of_gt hilast) (hp h)
  obtain ⟨deleted⟩ := hdel ⟨p 0, h0⟩ ⟨p (Fin.last s), hlast⟩
  let initial : G.Walk (p 0) (p (Fin.last s)) :=
    deleted.map (Embedding.induce {w | w ≠ p i}).toHom
  have initial_avoids : ∀ z, z ∈ initial.bypass.support → z ≠ p i := by
    intro z hz
    have hzinitial := initial.support_bypass_subset_support hz
    change z ∈ (deleted.map (Embedding.induce {w | w ≠ p i}).toHom).support at hzinitial
    rw [Walk.support_map] at hzinitial
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hzinitial
    exact u.property
  let A : Set V := p '' {j | j < i}
  let B : Set V := p '' {j | i < j}
  have hA0 : p (0 : Fin (s + 1)) ∈ A := ⟨0, hi0, rfl⟩
  have hBlast : p (Fin.last s) ∈ B := ⟨Fin.last s, hilast, rfl⟩
  obtain ⟨u, hu, v, hv, q, hq, hsub, hA, hB⟩ :=
    Erdos1105.GraphHelpers.TwoConnector.trim_between_sets initial.bypass initial.bypass_isPath
      A B hA0 hBlast
  change u ∈ p '' {j | j < i} at hu
  change v ∈ p '' {j | i < j} at hv
  rcases hu with ⟨a, ha, rfl⟩
  rcases hv with ⟨b, hb, rfl⟩
  have hcontacts : ∀ j, p j ∈ q.support → j = a ∨ j = b := by
    intro j hj
    rcases lt_trichotomy j i with hji | hji | hij
    · exact Or.inl (hp (hA (p j) hj ⟨j, hji, rfl⟩))
    · subst j
      exact (initial_avoids (p i) (hsub (p i) hj) rfl).elim
    · exact Or.inr (hp (hB (p j) hj ⟨j, hij, rfl⟩))
  refine ⟨a, b, ha, hb, q, hq, ?_, hcontacts, ?_⟩
  · intro z hz
    exact initial_avoids z (hsub z hz)
  · intro z hz hzp
    rcases hzp with ⟨j, rfl⟩
    rcases hcontacts j hz with hja | hjb
    · exact Or.inl (congrArg p hja)
    · exact Or.inr (congrArg p hjb)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.ComponentDetour
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Ambient support of an actual component of the graph outside S. -/
def componentSupport (C : (G.induce Sᶜ).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

def Attaches (C : (G.induce Sᶜ).ConnectedComponent) (x : V) : Prop :=
  ∃ v : ↥(Sᶜ), v ∈ C.supp ∧ G.Adj x v

theorem componentSupport_subset_compl (C : (G.induce Sᶜ).ConnectedComponent) :
    componentSupport C ⊆ Sᶜ := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

theorem componentSupport_disjoint {C D : (G.induce Sᶜ).ConnectedComponent}
    (hCD : C ≠ D) : Disjoint (componentSupport C) (componentSupport D) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, heq⟩
  have hwv : w = v := Subtype.ext heq
  subst w
  exact Set.disjoint_left.mp (pairwise_disjoint_supp_connectedComponent (G.induce Sᶜ) hCD) hv hw

/-- Two actual attachments to one outside component give a simple ambient detour.
The two attachment vertices inside the component may coincide. -/
theorem exists_component_detour (C : (G.induce Sᶜ).ConnectedComponent)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hCx : Attaches C x) (hCy : Attaches C y) :
    ∃ q : G.Walk x y, q.IsPath ∧ 2 ≤ q.length ∧
      (∀ z, z ∈ q.support → z ≠ x → z ≠ y → z ∈ componentSupport C) ∧
      (∀ z, z ∈ q.support → z ∈ S → z = x ∨ z = y) ∧
      (∃ z, z ∈ q.support ∧ z ∈ componentSupport C) := by
  classical
  obtain ⟨v, hvC, hxv⟩ := hCx
  obtain ⟨w, hwC, hyw⟩ := hCy
  obtain ⟨inside, hinside⟩ := C.connected_toSimpleGraph.exists_isPath ⟨v, hvC⟩ ⟨w, hwC⟩
  let middle : G.Walk v.val w.val :=
    (inside.map C.toSimpleGraph_hom).map (Embedding.induce Sᶜ).toHom
  have hmiddle : middle.IsPath :=
    Walk.IsPath.map (f := (Embedding.induce Sᶜ).toHom) Subtype.val_injective
      (Walk.IsPath.map (f := C.toSimpleGraph_hom) Subtype.val_injective hinside)
  have hcomponent : ∀ z, z ∈ middle.support → z ∈ componentSupport C := by
    intro z hz
    change z ∈ ((inside.map C.toSimpleGraph_hom).map (Embedding.induce Sᶜ).toHom).support at hz
    rw [Walk.support_map, Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hu
    exact ⟨t.val, t.property, rfl⟩
  have havoids : ∀ z, z ∈ middle.support → z ∉ S := by
    intro z hz
    exact componentSupport_subset_compl C (hcomponent z hz)
  have hynot : y ∉ middle.reverse.support := by
    intro hz
    exact havoids y (by simpa only [Walk.support_reverse, List.mem_reverse] using hz) hy
  let right : G.Walk y v.val := Walk.cons hyw middle.reverse
  have hright : right.IsPath := hmiddle.reverse.cons hynot
  have hxnot : x ∉ right.reverse.support := by
    intro hz
    have hz' : x = y ∨ x ∈ middle.support := by
      simpa only [right, Walk.support_reverse, List.mem_reverse, Walk.support_cons,
        List.mem_cons] using hz
    rcases hz' with h | h
    · exact hxy h
    · exact havoids x h hx
  let q : G.Walk x y := Walk.cons hxv right.reverse
  have hq : q.IsPath := hright.reverse.cons hxnot
  have hsupport : ∀ z, z ∈ q.support ↔ z = x ∨ z = y ∨ z ∈ middle.support := by
    intro z
    simp only [q, right, Walk.support_cons, Walk.support_reverse, List.mem_reverse,
      List.mem_cons]
  refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
  · simp only [q, right, Walk.length_cons, Walk.length_reverse]
    omega
  · intro z hz hzx hzy
    rcases (hsupport z).mp hz with h | h | h
    · exact (hzx h).elim
    · exact (hzy h).elim
    · exact hcomponent z h
  · intro z hz hzS
    rcases (hsupport z).mp hz with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (havoids z h hzS).elim
  · exact ⟨v.val, (hsupport v.val).mpr (Or.inr (Or.inr middle.start_mem_support)),
      hcomponent v.val middle.start_mem_support⟩

/-- Following an outside walk until its sole allowed S-contact gives an actual
attachment to the initial outside component. No simple-walk premise is needed. -/
theorem outside_walk_attaches_end {v y : V} (q : G.Walk v y)
    (hv : v ∉ S) (hy : y ∈ S)
    (hcontact : ∀ z, z ∈ q.support → z ∈ S → z = y) :
    Attaches ((G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩) y := by
  induction q with
  | nil => exact (hv hy).elim
  | @cons v w y hvw q ih =>
    by_cases hw : w ∈ S
    · have hwy : w = y := hcontact w
        (Walk.support_subset_support_cons q hvw q.start_mem_support) hw
      subst w
      exact ⟨⟨v, hv⟩, rfl, hvw.symm⟩
    · have htail : ∀ z, z ∈ q.support → z ∈ S → z = y := by
        intro z hz hzS
        exact hcontact z (Walk.support_subset_support_cons q hvw hz) hzS
      have hcomp : (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ =
          (G.induce Sᶜ).connectedComponentMk ⟨w, hw⟩ :=
        ConnectedComponent.connectedComponentMk_eq_of_adj (G := G.induce Sᶜ) hvw
      rw [hcomp]
      exact ih hw hy htail

/-- An actual simple detour contacting S only at its ends is either a chord,
or has both actual attachments in one actual outside connected component. -/
theorem path_is_chord_or_component {x y : V} (q : G.Walk x y)
    (_hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hq : q.IsPath)
    (hcontact : ∀ z, z ∈ q.support → z ∈ S → z = x ∨ z = y) :
    G.Adj x y ∨ ∃ C : (G.induce Sᶜ).ConnectedComponent,
      Attaches C x ∧ Attaches C y := by
  cases q with
  | nil => exact (hxy rfl).elim
  | @cons x v y hxv q =>
    by_cases hv : v ∈ S
    · have hvin : v ∈ (Walk.cons hxv q).support := by
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr q.start_mem_support
      rcases hcontact v hvin hv with h | h
      · exact (hxv.ne h.symm).elim
      · exact Or.inl (h ▸ hxv)
    · have hxnot : x ∉ q.support := (Walk.cons_isPath_iff hxv q).mp hq |>.2
      have htail : ∀ z, z ∈ q.support → z ∈ S → z = y := by
        intro z hz hzS
        rcases hcontact z (Walk.support_subset_support_cons q hxv hz) hzS with h | h
        · exact (hxnot (h ▸ hz)).elim
        · exact h
      exact Or.inr ⟨(G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩,
        ⟨⟨v, hv⟩, rfl, hxv⟩, outside_walk_attaches_end q hv hy htail⟩

/-- Actual component extremes come from all actual path attachment indices,
and have a simple, nonempty, component-supported ambient detour. -/
theorem exists_extreme_component_detour {s : ℕ}
    (p : Fin (s + 1) → V) (hp : Function.Injective p)
    (C : (G.induce (Set.range p)ᶜ).ConnectedComponent)
    (hwide : ∃ i j : Fin (s + 1), i < j ∧ Attaches C (p i) ∧ Attaches C (p j)) :
    ∃ a b : Fin (s + 1), a < b ∧ Attaches C (p a) ∧ Attaches C (p b) ∧
      (∀ j, Attaches C (p j) → a ≤ j ∧ j ≤ b) ∧
      ∃ q : G.Walk (p a) (p b), q.IsPath ∧ 2 ≤ q.length ∧
        (∀ z, z ∈ q.support → z ≠ p a → z ≠ p b → z ∈ componentSupport C) ∧
        (∀ j, p j ∈ q.support → j = a ∨ j = b) ∧
        (∃ z, z ∈ q.support ∧ z ∈ componentSupport C) := by
  classical
  let I : Finset (Fin (s + 1)) := Finset.univ.filter (fun i => Attaches C (p i))
  have hmem : ∀ i, i ∈ I ↔ Attaches C (p i) := by intro i; simp [I]
  obtain ⟨i, j, hij, hi, hj⟩ := hwide
  have hI : I.Nonempty := ⟨i, (hmem i).mpr hi⟩
  let a := I.min' hI
  let b := I.max' hI
  have hab : a < b := lt_of_le_of_lt (I.min'_le i ((hmem i).mpr hi))
    (lt_of_lt_of_le hij (I.le_max' j ((hmem j).mpr hj)))
  have ha : Attaches C (p a) := (hmem a).mp (I.min'_mem hI)
  have hb : Attaches C (p b) := (hmem b).mp (I.max'_mem hI)
  have hpa : p a ∈ Set.range p := ⟨a, rfl⟩
  have hpb : p b ∈ Set.range p := ⟨b, rfl⟩
  have hpab : p a ≠ p b := fun h => (ne_of_lt hab) (hp h)
  obtain ⟨q, hq, hlength, hinside, hcontacts, hnonempty⟩ :=
    exists_component_detour C hpa hpb hpab ha hb
  refine ⟨a, b, hab, ha, hb, ?_, q, hq, hlength, hinside, ?_, hnonempty⟩
  · intro k hk
    exact ⟨I.min'_le k ((hmem k).mpr hk), I.le_max' k ((hmem k).mpr hk)⟩
  · intro k hk
    rcases hcontacts (p k) hk ⟨k, rfl⟩ with h | h
    · exact Or.inl (hp h)
    · exact Or.inr (hp h)

/-- Distinct actual component labels force disjoint ordinary internal supports
once the constructed component-support conclusions have been applied. -/
theorem internal_supports_disjoint {C D : (G.induce Sᶜ).ConnectedComponent}
    (hCD : C ≠ D) {x y u v : V} (q : G.Walk x y) (r : G.Walk u v)
    (hq : ∀ z, z ∈ q.support → z ≠ x → z ≠ y → z ∈ componentSupport C)
    (hr : ∀ z, z ∈ r.support → z ≠ u → z ≠ v → z ∈ componentSupport D) :
    Disjoint {z | z ∈ q.support ∧ z ≠ x ∧ z ≠ y}
      {z | z ∈ r.support ∧ z ≠ u ∧ z ≠ v} := by
  apply Set.disjoint_left.mpr
  rintro z ⟨hzq, hzx, hzy⟩ ⟨hzr, hzu, hzv⟩
  exact Set.disjoint_left.mp (componentSupport_disjoint hCD)
    (hq z hzq hzx hzy) (hr z hzr hzu hzv)

end ErdosProblems.PathUpperReduction.ComponentDetour

namespace ErdosProblems.PathUpperReduction.IntervalVine

abbrev Interval := ℕ × ℕ

def Valid (F : Finset Interval) (s : ℕ) : Prop :=
  ∀ p ∈ F, p.1 < p.2 ∧ p.2 ≤ s

def Cuts (F : Finset Interval) (s : ℕ) : Prop :=
  ∀ c, 0 < c → c < s → ∃ p ∈ F, p.1 < c ∧ c < p.2

def RightBound (F : Finset Interval) (previous reach : ℕ) : Prop :=
  ∀ p ∈ F, p.1 < previous → p.2 ≤ reach

/-- Maximum right end, with minimum left end among its ties. -/
theorem exists_right_max_left_min (S : Finset Interval) (hS : S.Nonempty) :
    ∃ p ∈ S, (∀ q ∈ S, q.2 ≤ p.2) ∧
      (∀ q ∈ S, q.2 = p.2 → p.1 ≤ q.1) := by
  classical
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun q => q.2) hS
  let T := S.filter (fun q => q.2 = p.2)
  have hT : T.Nonempty := ⟨p, by simp [T, hp]⟩
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image T (fun q => q.1) hT
  have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
  have hqp : q.2 = p.2 := (Finset.mem_filter.mp hq).2
  refine ⟨q, hqS, ?_, ?_⟩
  · intro v hv
    rw [hqp]
    exact hmax v hv
  · intro v hv hvq
    apply hmin v
    exact Finset.mem_filter.mpr ⟨hv, hvq.trans hqp⟩

/-- One exact greedy extension. Its previous bound is propagated, and its
selected left end cannot lie below the preceding reach. -/
theorem exists_greedy_step (F : Finset Interval) (s previous reach : ℕ)
    (hvalid : Valid F s) (hcuts : Cuts F s)
    (hpositive : 0 < reach) (hless : reach < s)
    (hinvariant : RightBound F previous reach) :
    ∃ p ∈ F, previous ≤ p.1 ∧ p.1 < reach ∧ reach < p.2 ∧ p.2 ≤ s ∧
      RightBound F reach p.2 ∧
      (∀ q ∈ F, q.1 < reach → q.2 = p.2 → p.1 ≤ q.1) := by
  classical
  obtain ⟨cross, hcrossF, hcrossL, hcrossR⟩ := hcuts reach hpositive hless
  let S := F.filter (fun q => q.1 < reach)
  have hS : S.Nonempty := ⟨cross, Finset.mem_filter.mpr ⟨hcrossF, hcrossL⟩⟩
  obtain ⟨p, hpS, hmax, hmin⟩ := exists_right_max_left_min S hS
  have hpF : p ∈ F := (Finset.mem_filter.mp hpS).1
  have hpL : p.1 < reach := (Finset.mem_filter.mp hpS).2
  have hpR : reach < p.2 :=
    lt_of_lt_of_le hcrossR (hmax cross (Finset.mem_filter.mpr ⟨hcrossF, hcrossL⟩))
  have hprevious : previous ≤ p.1 := by
    by_contra hnot
    have hsmall : p.1 < previous := by omega
    have hbound := hinvariant p hpF hsmall
    omega
  refine ⟨p, hpF, hprevious, hpL, hpR, (hvalid p hpF).2, ?_, ?_⟩
  · intro q hq hqL
    exact hmax q (Finset.mem_filter.mpr ⟨hq, hqL⟩)
  · intro q hq hqL hqR
    exact hmin q (Finset.mem_filter.mpr ⟨hq, hqL⟩) hqR

/-- A literal list certificate. After an interval with right end `reach`,
the next interval starts before `reach` and at or above `previous`; recursively
the pair of reaches becomes `(reach,newRight)`. Thus its third selected left
end is at least the first selected right end, and so on. -/
inductive GreedyTail (F : Finset Interval) (s : ℕ) :
    ℕ → ℕ → List Interval → Prop
  | done (previous : ℕ) : GreedyTail F s previous s []
  | step (previous reach : ℕ) (p : Interval) (rest : List Interval)
      (hp : p ∈ F) (hprevious : previous ≤ p.1) (hleft : p.1 < reach)
      (hadvance : reach < p.2) (hbound : p.2 ≤ s)
      (hmaximum : RightBound F reach p.2)
      (htie : ∀ q ∈ F, q.1 < reach → q.2 = p.2 → p.1 ≤ q.1)
      (tail : GreedyTail F s reach p.2 rest) :
      GreedyTail F s previous reach (p :: rest)

/-- Integer progress, not a supplied finite cutoff, yields a terminating tail. -/
theorem exists_greedy_tail (F : Finset Interval) (s previous reach : ℕ)
    (hvalid : Valid F s) (hcuts : Cuts F s)
    (hpositive : 0 < reach) (hbound : reach ≤ s)
    (hinvariant : RightBound F previous reach) :
    ∃ rest, GreedyTail F s previous reach rest := by
  classical
  have haux : ∀ n previous reach, s - reach = n → 0 < reach → reach ≤ s →
      RightBound F previous reach → ∃ rest, GreedyTail F s previous reach rest := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro previous reach hmeasure hpositive hbound hinvariant
      by_cases hend : reach = s
      · subst reach
        exact ⟨[], GreedyTail.done previous⟩
      have hless : reach < s := by omega
      obtain ⟨p, hp, hprevious, hleft, hadvance, hboundp, hmax, htie⟩ :=
        exists_greedy_step F s previous reach hvalid hcuts hpositive hless hinvariant
      have hdecrease : s - p.2 < n := by omega
      obtain ⟨rest, hrest⟩ := ih (s - p.2) hdecrease reach p.2 rfl
        (by omega) hboundp hmax
      exact ⟨p :: rest, GreedyTail.step previous reach p rest hp hprevious hleft
        hadvance hboundp hmax htie hrest⟩
  exact haux (s - reach) previous reach rfl hpositive hbound hinvariant

def endRight : ℕ → List Interval → ℕ
  | reach, [] => reach
  | _, p :: rest => endRight p.2 rest

theorem GreedyTail.end_eq {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    endRight reach rest = s := by
  induction h with
  | done previous => rfl
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    exact ih

theorem GreedyTail.mem {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    ∀ p ∈ rest, p ∈ F := by
  induction h with
  | done previous => simp
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ih q hq

theorem GreedyTail.length_le {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    rest.length ≤ s - reach := by
  induction h with
  | done previous => simp
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    simp only [List.length_cons]
    omega

theorem GreedyTail.strict_right {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    rest.Pairwise (fun p q => p.2 < q.2) ∧ ∀ q ∈ rest, reach < q.2 := by
  induction h with
  | done previous => exact ⟨List.Pairwise.nil, by simp⟩
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    rcases ih with ⟨ihpairwise, ihgreater⟩
    refine ⟨List.Pairwise.cons ihgreater ihpairwise, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hadvance
    · exact lt_trans hadvance (ihgreater q hq)

/-- The min-left tie is what bounds the final left end by the last boundary
interval; an arbitrary maximum-right choice would not justify this result. -/
theorem GreedyTail.terminal_left_le {F : Finset Interval} {s previous reach b : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest)
    (hboundary : (b, s) ∈ F) :
    ∀ q ∈ rest, q.2 = s → q.1 ≤ b := by
  induction h with
  | done previous => simp
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    intro q hq hqend
    rcases List.mem_cons.mp hq with rfl | hq
    · by_cases hb : b < reach
      · exact htie (b, s) hboundary hb hqend.symm
      · have hreach : reach ≤ b := by omega
        exact le_trans (Nat.le_of_lt hleft) hreach
    · exact ih q hq hqend

/-- Actual finite interval-family theorem with both boundary intervals.
The nonempty output list ends at s, has at most s members, and its returned
recursive certificate gives the stated greedy interleaving and membership.
Its first right end is at least a; every selected interval ending at s starts
at or before b. `2 ≤ s` excludes the vacuous empty-family s=1 counterexample. -/
theorem exists_interval_vine (F : Finset Interval) (s a b : ℕ)
    (hs : 2 ≤ s) (hvalid : Valid F s) (hcuts : Cuts F s)
    (hfirst : (0, a) ∈ F) (hlast : (b, s) ∈ F) :
    ∃ first rest, first ∈ F ∧ first.1 = 0 ∧ a ≤ first.2 ∧
      (∀ q ∈ F, q.1 = 0 → q.2 ≤ first.2) ∧
      GreedyTail F s 1 first.2 rest ∧
      (first :: rest).Pairwise (fun p q => p.2 < q.2) ∧
      endRight 0 (first :: rest) = s ∧ (first :: rest).length ≤ s ∧
      (∀ q ∈ first :: rest, q ∈ F) ∧
      (∀ q ∈ first :: rest, q.2 = s → q.1 ≤ b) := by
  classical
  let S := F.filter (fun p => p.1 = 0)
  have hS : S.Nonempty := ⟨(0, a), Finset.mem_filter.mpr ⟨hfirst, rfl⟩⟩
  obtain ⟨first, hfirstS, hmax, hmin⟩ := exists_right_max_left_min S hS
  have hfirstF : first ∈ F := (Finset.mem_filter.mp hfirstS).1
  have hzero : first.1 = 0 := (Finset.mem_filter.mp hfirstS).2
  have hfirstmax : ∀ q ∈ F, q.1 = 0 → q.2 ≤ first.2 := by
    intro q hq hqzero
    exact hmax q (Finset.mem_filter.mpr ⟨hq, hqzero⟩)
  have ha : a ≤ first.2 := hfirstmax (0, a) hfirst rfl
  obtain ⟨cross, hcross, hcrossL, hcrossR⟩ := hcuts 1 (by omega) (by omega)
  have hcrosszero : cross.1 = 0 := by omega
  have hreach : 1 < first.2 := lt_of_lt_of_le hcrossR (hfirstmax cross hcross hcrosszero)
  have hinvariant : RightBound F 1 first.2 := by
    intro q hq hqL
    exact hfirstmax q hq (by omega)
  obtain ⟨rest, hrest⟩ := exists_greedy_tail F s 1 first.2 hvalid hcuts
    (by omega) (hvalid first hfirstF).2 hinvariant
  refine ⟨first, rest, hfirstF, hzero, ha, hfirstmax, hrest,
    List.Pairwise.cons hrest.strict_right.2 hrest.strict_right.1, hrest.end_eq, ?_, ?_, ?_⟩
  · have hlength := hrest.length_le
    have hbound := (hvalid first hfirstF).2
    simp only [List.length_cons]
    omega
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hfirstF
    · exact hrest.mem q hq
  · intro q hq hqend
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hzero]
      exact Nat.zero_le b
    · exact hrest.terminal_left_le hlast q hq hqend

end ErdosProblems.PathUpperReduction.IntervalVine

namespace ErdosProblems.PathUpperReduction.ActualBridgeFamily
open SimpleGraph ComponentDetour
variable {V : Type*} {G : SimpleGraph V} {s : ℕ}

def Chord (p : Fin (s + 1) → V) :=
  {ij : Fin (s + 1) × Fin (s + 1) // ij.1 < ij.2 ∧ G.Adj (p ij.1) (p ij.2)}

def Wide (p : Fin (s + 1) → V) :=
  {C : (G.induce (Set.range p)ᶜ).ConnectedComponent //
    ∃ i j : Fin (s + 1), i < j ∧ Attaches C (p i) ∧ Attaches C (p j)}

def Label (p : Fin (s + 1) → V) := Chord (G := G) p ⊕ Wide (G := G) p

def Data (p : Fin (s + 1) → V)
    (L R : Label (G := G) p → Fin (s + 1))
    (Q : ∀ l, G.Walk (p (L l)) (p (R l))) : Prop :=
      (∀ l, L l < R l) ∧
      (∀ l, (Q l).IsPath ∧ ∀ j, p j ∈ (Q l).support → j = L l ∨ j = R l) ∧
      (∀ c : Chord (G := G) p, L (.inl c) = c.val.1 ∧ R (.inl c) = c.val.2 ∧
        (Q (.inl c)).length = 1) ∧
      (∀ C : Wide (G := G) p, ∀ j, Attaches C.val (p j) →
        L (.inr C) ≤ j ∧ j ≤ R (.inr C)) ∧
      (∀ C : Wide (G := G) p, Attaches C.val (p (L (.inr C))) ∧
        Attaches C.val (p (R (.inr C))) ∧ 2 ≤ (Q (.inr C)).length ∧
        (∀ z, z ∈ (Q (.inr C)).support → z ≠ p (L (.inr C)) →
          z ≠ p (R (.inr C)) → z ∈ ComponentDetour.componentSupport C.val) ∧
        (∃ z, z ∈ (Q (.inr C)).support ∧ z ∈ ComponentDetour.componentSupport C.val)) ∧
      (∀ l r, R l < R r →
        Disjoint {z | z ∈ (Q l).support ∧ z ≠ p (L l) ∧ z ≠ p (R l)}
          {z | z ∈ (Q r).support ∧ z ≠ p (L r) ∧ z ≠ p (R r)})

/-- One fixed pair and actual walk for every actual chord/component label.
Strictly different right endpoints force disjoint ordinary internal supports. -/
theorem exists_bridge_data (p : Fin (s + 1) → V) (hp : Function.Injective p) :
    ∃ L R : Label (G := G) p → Fin (s + 1),
    ∃ Q : ∀ l, G.Walk (p (L l)) (p (R l)), Data p L R Q := by
  classical
  have hex := fun C : Wide (G := G) p =>
    exists_extreme_component_detour p hp C.val C.property
  choose LC RC hlt hAL hAR hbound QC hpath hlen hinside hcontact hnonempty using hex
  let L : Label (G := G) p → Fin (s + 1) := Sum.elim (fun c => c.val.1) LC
  let R : Label (G := G) p → Fin (s + 1) := Sum.elim (fun c => c.val.2) RC
  let Q : ∀ l : Label (G := G) p, G.Walk (p (L l)) (p (R l)) := fun l =>
    match l with
    | .inl c => Walk.cons c.property.2 Walk.nil
    | .inr C => QC C
  have hchord : ∀ c : Chord (G := G) p, ∀ z,
      z ∈ (Q (.inl c)).support → z = p c.val.1 ∨ z = p c.val.2 := by
    intro c z hz
    change z ∈ [p c.val.1, p c.val.2] at hz
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hz
  have hempty : ∀ c : Chord (G := G) p,
      {z | z ∈ (Q (.inl c)).support ∧ z ≠ p (L (.inl c)) ∧
        z ≠ p (R (.inl c))} = ∅ := by
    intro c
    ext z
    constructor
    · rintro ⟨hz, hx, hy⟩
      rcases hchord c z hz with h | h
      · exact (hx h).elim
      · exact (hy h).elim
    · intro hz
      exact hz.elim
  refine ⟨L, R, Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    cases l with
    | inl c => exact c.property.1
    | inr C => exact hlt C
  · intro l
    cases l with
    | inl c =>
      change (Walk.cons c.property.2 Walk.nil).IsPath ∧ _
      refine ⟨Walk.IsPath.nil.cons ?_, ?_⟩
      · simp only [Walk.support_nil, List.mem_singleton]
        exact fun h => (ne_of_lt c.property.1) (hp h)
      · intro j hj
        rcases hchord c (p j) hj with h | h
        · exact Or.inl (hp h)
        · exact Or.inr (hp h)
    | inr C => exact ⟨hpath C, hcontact C⟩
  · intro c
    exact ⟨rfl, rfl, rfl⟩
  · intro C j hj
    exact hbound C j hj
  · intro C
    exact ⟨hAL C, hAR C, hlen C, hinside C, hnonempty C⟩
  · intro l r hprogress
    cases l with
    | inl c => rw [hempty c]; exact Set.empty_disjoint _
    | inr C =>
      cases r with
      | inl c => rw [hempty c]; exact Set.disjoint_empty _
      | inr D =>
        have hCD : C.val ≠ D.val := by
          intro h
          have heq : C = D := Subtype.ext h
          subst D
          exact (lt_irrefl _ hprogress)
        exact internal_supports_disjoint hCD (QC C) (QC D) (hinside C) (hinside D)

/-- Every internal deletion cut is covered by the actual finite image family.
No boundary chord or consecutive-order adjacency is assumed in this theorem. -/
theorem exists_cut_covered_family [Finite V] (p : Fin (s + 1) → V)
    (hp : Function.Injective p)
    (hdel : ∀ i : Fin (s + 1), 0 < i → i < Fin.last s →
      (G.induce {w | w ≠ p i}).Connected) :
    ∃ L R : Label (G := G) p → Fin (s + 1),
    ∃ Q : ∀ l, G.Walk (p (L l)) (p (R l)), Data p L R Q ∧
    ∃ F : Finset IntervalVine.Interval,
      (∀ I, I ∈ F ↔ ∃ l, ((L l).val, (R l).val) = I) ∧
      IntervalVine.Valid F s ∧ IntervalVine.Cuts F s := by
  classical
  obtain ⟨L, R, Q, hd⟩ := exists_bridge_data (G := G) p hp
  rcases hd with ⟨hlt, hpath, hchord, hextreme, hinside, hdisjoint⟩
  have : Finite (Label (G := G) p) := by
    dsimp [Label, Chord, Wide]
    infer_instance
  let : Fintype (Label (G := G) p) := Fintype.ofFinite _
  let F : Finset IntervalVine.Interval :=
    Finset.univ.image (fun l => ((L l).val, (R l).val))
  have hmem : ∀ I, I ∈ F ↔ ∃ l, ((L l).val, (R l).val) = I := by
    intro I
    simp only [F, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨L, R, Q, ⟨hlt, hpath, hchord, hextreme, hinside, hdisjoint⟩,
    F, hmem, ?_, ?_⟩
  · intro I hI
    obtain ⟨l, rfl⟩ := (hmem I).mp hI
    exact ⟨hlt l, Nat.le_of_lt_succ (R l).isLt⟩
  · intro c hc0 hcs
    let i : Fin (s + 1) := ⟨c, by omega⟩
    have hi0 : (0 : Fin (s + 1)) < i := hc0
    have his : i < Fin.last s := hcs
    obtain ⟨a, b, hai, hib, q, hq, _havoid, _hcontacts, hcontact⟩ :=
      exists_internal_cut_detour p hp i hi0 his (hdel i hi0 his)
    have hab : a < b := lt_trans hai hib
    have hpa : p a ∈ Set.range p := ⟨a, rfl⟩
    have hpb : p b ∈ Set.range p := ⟨b, rfl⟩
    have hpab : p a ≠ p b := fun h => (ne_of_lt hab) (hp h)
    rcases path_is_chord_or_component q hpa hpb hpab hq hcontact with hadj | hcomponent
    · let l : Label (G := G) p := .inl ⟨(a, b), hab, hadj⟩
      have hleft : L l = a := (hchord ⟨(a, b), hab, hadj⟩).1
      have hright : R l = b := (hchord ⟨(a, b), hab, hadj⟩).2.1
      refine ⟨((L l).val, (R l).val), (hmem _).mpr ⟨l, rfl⟩, ?_, ?_⟩
      · rw [hleft]
        exact hai
      · rw [hright]
        exact hib
    · obtain ⟨C, hCa, hCb⟩ := hcomponent
      let D : Wide (G := G) p := ⟨C, a, b, hab, hCa, hCb⟩
      let l : Label (G := G) p := .inr D
      have hLa : L l ≤ a := (hextreme D a hCa).1
      have hbR : b ≤ R l := (hextreme D b hCb).2
      refine ⟨((L l).val, (R l).val), (hmem _).mpr ⟨l, rfl⟩, ?_, ?_⟩
      · exact lt_of_le_of_lt hLa hai
      · exact lt_of_lt_of_le hib hbR

/-- Construct the actual labelled vine from deletion connectivity and two actual
boundary edges. Image duplicates do not require interval-map injectivity. -/
theorem exists_actual_interval_vine [Finite V] (p : Fin (s + 1) → V)
    (hp : Function.Injective p) (hs : 2 ≤ s)
    (hdel : ∀ i : Fin (s + 1), 0 < i → i < Fin.last s →
      (G.induce {w | w ≠ p i}).Connected)
    (a b : Fin (s + 1)) (ha : 0 < a) (hb : b < Fin.last s)
    (hfirstEdge : G.Adj (p 0) (p a)) (hlastEdge : G.Adj (p b) (p (Fin.last s))) :
    ∃ L R : Label (G := G) p → Fin (s + 1),
    ∃ Q : ∀ l, G.Walk (p (L l)) (p (R l)), Data p L R Q ∧
    ∃ F : Finset IntervalVine.Interval, ∃ first rest, ∃ labels : List (Label (G := G) p),
      (∀ I, I ∈ F ↔ ∃ l, ((L l).val, (R l).val) = I) ∧
      IntervalVine.Valid F s ∧ IntervalVine.Cuts F s ∧
      first ∈ F ∧ first.1 = 0 ∧ a.val ≤ first.2 ∧
      (∀ I ∈ F, I.1 = 0 → I.2 ≤ first.2) ∧
      IntervalVine.GreedyTail F s 1 first.2 rest ∧
      labels.map (fun l => ((L l).val, (R l).val)) = first :: rest ∧
      labels ≠ [] ∧ labels.Pairwise (fun l r => R l < R r) ∧
      labels.Pairwise (fun l r =>
        Disjoint {z | z ∈ (Q l).support ∧ z ≠ p (L l) ∧ z ≠ p (R l)}
          {z | z ∈ (Q r).support ∧ z ≠ p (L r) ∧ z ≠ p (R r)}) ∧
      IntervalVine.endRight 0 (labels.map (fun l => ((L l).val, (R l).val))) = s ∧
      labels.length ≤ s ∧ (∀ l ∈ labels, (R l).val = s → (L l).val ≤ b.val) := by
  classical
  obtain ⟨L, R, Q, hd, F, hmem, hvalid, hcuts⟩ :=
    exists_cut_covered_family (G := G) p hp hdel
  have hchord := hd.2.2.1
  have hfirst : (0, a.val) ∈ F := by
    let c : Chord (G := G) p := ⟨(0, a), ha, hfirstEdge⟩
    apply (hmem _).mpr
    refine ⟨.inl c, ?_⟩
    rw [(hchord c).1, (hchord c).2.1]
    rfl
  have hlast : (b.val, s) ∈ F := by
    let c : Chord (G := G) p := ⟨(b, Fin.last s), hb, hlastEdge⟩
    apply (hmem _).mpr
    refine ⟨.inl c, ?_⟩
    rw [(hchord c).1, (hchord c).2.1]
    rfl
  obtain ⟨first, rest, hfirstF, hzero, hreach, hmax, htail, hstrict,
    hend, hlength, hselected, hterminal⟩ :=
    IntervalVine.exists_interval_vine F s a.val b.val hs hvalid hcuts hfirst hlast
  have hpre : ∀ I : {I : IntervalVine.Interval // I ∈ F},
      ∃ l : Label (G := G) p, ((L l).val, (R l).val) = I.val := by
    intro I
    exact (hmem I.val).mp I.property
  choose select hselect using hpre
  let seq := first :: rest
  let lift : {I : IntervalVine.Interval // I ∈ seq} → Label (G := G) p :=
    fun I => select ⟨I.val, hselected I.val I.property⟩
  let labels := seq.attach.map lift
  have hmap : labels.map (fun l => ((L l).val, (R l).val)) = seq := by
    change (seq.attach.map lift).map _ = seq
    rw [List.map_map]
    calc
      _ = seq.attach.map Subtype.val := by
        apply List.map_congr_left
        intro I _hI
        exact hselect ⟨I.val, hselected I.val I.property⟩
      _ = seq := List.attach_map_subtype_val seq
  have hlabelstrict : labels.Pairwise (fun l r => R l < R r) := by
    have h := hstrict
    change seq.Pairwise (fun p q => p.2 < q.2) at h
    rw [← hmap, List.pairwise_map] at h
    exact h
  have hnonempty : labels ≠ [] := by
    intro hnil
    simp [hnil, seq] at hmap
  refine ⟨L, R, Q, hd, F, first, rest, labels, hmem, hvalid, hcuts,
    hfirstF, hzero, hreach, hmax, htail, hmap, hnonempty, hlabelstrict,
    hlabelstrict.imp (fun {l r} h => hd.2.2.2.2.2 l r h), ?_, ?_, ?_⟩
  · rw [hmap]
    exact hend
  · have hlen : (labels.map (fun l => ((L l).val, (R l).val))).length = labels.length :=
      List.length_map _
    rw [hmap] at hlen
    rw [← hlen]
    exact hlength
  · intro l hl hRl
    have hin : ((L l).val, (R l).val) ∈ seq := by
      rw [← hmap]
      exact List.mem_map.mpr ⟨l, hl, rfl⟩
    exact hterminal _ hin hRl

end ErdosProblems.PathUpperReduction.ActualBridgeFamily

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.VineCycle
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem interval_getVert (P : G.Walk u v) (i j n : ℕ) (hij : i ≤ j)
    (hn : i + n ≤ j) :
    (Erdos1105.GraphHelpers.pathInterval P i j hij).getVert n = P.getVert (i + n) := by
  simp only [Erdos1105.GraphHelpers.pathInterval, Walk.getVert_copy, Walk.drop_getVert,
    Walk.take_getVert, Nat.min_eq_right hn]

theorem interval_support (P : G.Walk u v) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ P.length) (z : V) :
    z ∈ (Erdos1105.GraphHelpers.pathInterval P i j hij).support ↔
      ∃ k, i ≤ k ∧ k ≤ j ∧ P.getVert k = z := by
  constructor
  · intro hz
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    rw [Erdos1105.GraphHelpers.pathInterval_length P i j hij hj] at hnl
    have hsum : i + n ≤ j := by omega
    exact ⟨i + n, by omega, hsum, (interval_getVert P i j n hij hsum).symm.trans hn⟩
  · rintro ⟨k, hik, hkj, hk⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨k - i, ?_, ?_⟩
    · rw [interval_getVert P i j (k - i) hij (by omega)]
      simpa [Nat.add_sub_of_le hik] using hk
    · rw [Erdos1105.GraphHelpers.pathInterval_length P i j hij hj]
      omega

def Interior (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l))) (l : α) : Set V :=
  {z | z ∈ (Q l).support ∧ z ≠ P.getVert (L l) ∧ z ≠ P.getVert (R l)}

theorem interval_contacts (P : G.Walk u v) (hp : P.IsPath) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ P.length) (k : ℕ) (hk : k ≤ P.length)
    (hmem : P.getVert k ∈ (Erdos1105.GraphHelpers.pathInterval P i j hij).support) : i ≤ k ∧ k ≤ j := by
  obtain ⟨m, him, hmj, hmk⟩ := (interval_support P i j hij hj (P.getVert k)).mp hmem
  have : m = k := hp.getVert_injOn (show m ≤ P.length from le_trans hmj hj) hk hmk
  omega

def Rails (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (previous reach : ℕ)
    (U : G.Walk (P.getVert 0) (P.getVert previous))
    (W : G.Walk (P.getVert 0) (P.getVert reach)) : Prop :=
  U.IsPath ∧ W.IsPath ∧
  (∀ k, k ≤ P.length → P.getVert k ∈ U.support → k ≤ previous) ∧
  (∀ k, k ≤ P.length → P.getVert k ∈ W.support → k = 0 ∨ k < previous ∨ k = reach) ∧
  (∀ z, z ∈ U.support → z ∈ W.support → z = P.getVert 0) ∧
  (∀ z, z ∈ U.support ∨ z ∈ W.support → z ∉ P.support →
    ∃ l, R l ≤ reach ∧ z ∈ Interior P L R Q l)

theorem fresh_meet (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    {previous reach : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert reach)}
    (h : Rails P L R Q previous reach U W) (n : α) (hr : reach < R n)
    (z : V) (hz : z ∈ U.support ∨ z ∈ W.support) (hzn : z ∈ (Q n).support) :
    z = P.getVert (L n) ∨ z = P.getVert (R n) := by
  by_cases hpz : z ∈ P.support
  · obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hpz
    have hc := contact n k hkl (hk.symm ▸ hzn)
    rcases hc with hc | hc <;> subst k <;> simp_all
  · by_contra he
    push Not at he
    obtain ⟨l, hl, hzl⟩ := h.2.2.2.2.2 z hz hpz
    exact Set.disjoint_left.mp (separate l n (by omega)) hzl ⟨hzn, he.1, he.2⟩

theorem rails_close (P : G.Walk u v) (hp : P.IsPath) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    {previous : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert P.length)}
    (h : Rails P L R Q previous P.length U W)
    (hprev : previous < P.length) (hs : 2 ≤ P.length) :
    let S := Erdos1105.GraphHelpers.pathInterval P previous P.length hprev.le
    ((U.append S).append W.reverse).IsCycle ∧
    (∀ z, z ∈ ((U.append S).append W.reverse).support ↔
      z ∈ U.support ∨ z ∈ S.support ∨ z ∈ W.support) := by
  dsimp only
  let S := Erdos1105.GraphHelpers.pathInterval P previous P.length hprev.le
  have hS : S.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp previous P.length hprev.le
  have hUS : (U.append S).IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only U S h.1 hS
    intro z hz hzS
    obtain ⟨k, hkprev, hks, hk⟩ := (interval_support P previous P.length hprev.le (by omega) z).mp hzS
    have hkU := h.2.2.1 k hks (hk.symm ▸ hz)
    have : k = previous := by omega
    simpa [this] using hk.symm
  have hmeet : ∀ z, z ∈ (U.append S).support → z ∈ W.support →
      z = P.getVert 0 ∨ z = P.getVert P.length := by
    intro z hz hzW
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzU | hzS
    · exact Or.inl (h.2.2.2.2.1 z hzU hzW)
    · obtain ⟨k, hkprev, hks, hk⟩ := (interval_support P previous P.length hprev.le (by omega) z).mp hzS
      rcases h.2.2.2.1 k hks (hk.symm ▸ hzW) with hk0 | hkp | hkl
      · exact Or.inl (by simpa [hk0] using hk.symm)
      · omega
      · exact Or.inr (by simpa [hkl] using hk.symm)
  have hWpos : 1 ≤ W.length := by
    by_contra hn
    have he := Walk.eq_of_length_eq_zero (p := W) (by omega)
    have hi := hp.getVert_injOn (by simp) (by simp) he
    omega
  have hUpos : previous ≠ 0 → 1 ≤ U.length := by
    intro hne
    by_contra hn
    have he := Walk.eq_of_length_eq_zero (p := U) (by omega)
    have hi := hp.getVert_injOn (show 0 ≤ P.length from Nat.zero_le _) (show previous ≤ P.length from hprev.le) he
    omega
  have hlenS : S.length = P.length - previous :=
    Erdos1105.GraphHelpers.pathInterval_length P previous P.length hprev.le (by omega)
  have hlen : 3 ≤ (U.append S).length + W.length := by
    rw [Walk.length_append, hlenS]
    by_cases he : previous = 0
    · omega
    · have := hUpos he
      omega
  refine ⟨Erdos1105.GraphHelpers.cycle_of_two_paths (U.append S) W hUS h.2.1 hmeet hlen, ?_⟩
  intro z
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
  tauto

theorem rails_step (P : G.Walk u v) (hp : P.IsPath) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    {previous reach : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert reach)}
    (h : Rails P L R Q previous reach U W) (n : α)
    (ha : previous ≤ L n) (har : L n < reach) (hrb : reach < R n)
    (hb : R n ≤ P.length) :
    let S := Erdos1105.GraphHelpers.pathInterval P previous (L n) ha
    Rails P L R Q reach (R n) W ((U.append S).append (Q n)) := by
  dsimp only
  let S := Erdos1105.GraphHelpers.pathInterval P previous (L n) ha
  have hS : S.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp previous (L n) ha
  have haP : L n ≤ P.length := by omega
  have hUS : (U.append S).IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only U S h.1 hS
    intro z hz hzS
    obtain ⟨k, hpk, hka, hkz⟩ := (interval_support P previous (L n) ha haP z).mp hzS
    have hku := h.2.2.1 k (by omega) (hkz.symm ▸ hz)
    have : k = previous := by omega
    simpa [this] using hkz.symm
  have hUScontact : ∀ k, k ≤ P.length → P.getVert k ∈ (U.append S).support → k ≤ L n := by
    intro k hk hmem
    rcases (Walk.mem_support_append_iff _ _).mp hmem with hu | hs
    · have := h.2.2.1 k hk hu
      omega
    · exact (interval_contacts P hp previous (L n) ha haP k hk hs).2
  have hUSQ : ∀ z, z ∈ (U.append S).support → z ∈ (Q n).support → z = P.getVert (L n) := by
    intro z hz hzn
    have he : z = P.getVert (L n) ∨ z = P.getVert (R n) := by
      rcases (Walk.mem_support_append_iff _ _).mp hz with hu | hs
      · exact fresh_meet P L R Q contact separate h n hrb z (Or.inl hu) hzn
      · obtain ⟨k, hpk, hka, hkz⟩ := (interval_support P previous (L n) ha haP z).mp hs
        rcases contact n k (by omega) (hkz.symm ▸ hzn) with he | he
        · exact Or.inl (by simpa [he] using hkz.symm)
        · omega
    rcases he with he | he
    · exact he
    · have := hUScontact (R n) hb (he ▸ hz)
      omega
  have hnew : ((U.append S).append (Q n)).IsPath :=
    Erdos1105.GraphHelpers.path_append_of_meet_only (U.append S) (Q n) hUS (paths n) hUSQ
  refine ⟨h.2.1, hnew, ?_, ?_, ?_, ?_⟩
  · intro k hk hmem
    rcases h.2.2.2.1 k hk hmem with he | he | he <;> omega
  · intro k hk hmem
    rcases (Walk.mem_support_append_iff _ _).mp hmem with hmem | hmem
    · have := hUScontact k hk hmem
      exact Or.inr (Or.inl (by omega))
    · rcases contact n k hk hmem with he | he
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr he)
  · intro z hzW hznew
    rcases (Walk.mem_support_append_iff _ _).mp hznew with hzUS | hzQ
    · rcases (Walk.mem_support_append_iff _ _).mp hzUS with hzU | hzS
      · exact h.2.2.2.2.1 z hzU hzW
      · obtain ⟨k, hpk, hka, hkz⟩ := (interval_support P previous (L n) ha haP z).mp hzS
        rcases h.2.2.2.1 k (by omega) (hkz.symm ▸ hzW) with he | he | he
        · simpa [he] using hkz.symm
        · omega
        · omega
    · rcases fresh_meet P L R Q contact separate h n hrb z (Or.inr hzW) hzQ with he | he
      · rcases h.2.2.2.1 (L n) haP (he ▸ hzW) with he0 | hep | her
        · simpa [he0] using he
        · omega
        · omega
      · rcases h.2.2.2.1 (R n) hb (he ▸ hzW) with he0 | hep | her <;> omega
  · intro z hz hzP
    rcases hz with hzW | hznew
    · obtain ⟨l, hl, hzl⟩ := h.2.2.2.2.2 z (Or.inr hzW) hzP
      exact ⟨l, by omega, hzl⟩
    · rcases (Walk.mem_support_append_iff _ _).mp hznew with hzUS | hzQ
      · rcases (Walk.mem_support_append_iff _ _).mp hzUS with hzU | hzS
        · obtain ⟨l, hl, hzl⟩ := h.2.2.2.2.2 z (Or.inl hzU) hzP
          exact ⟨l, by omega, hzl⟩
        · exact (hzP (Erdos1105.GraphHelpers.pathInterval_support_subset P previous (L n) ha hzS)).elim
      · refine ⟨n, le_rfl, hzQ, ?_, ?_⟩
        · intro he
          exact hzP (he ▸ Walk.getVert_mem_support P (L n))
        · intro he
          exact hzP (he ▸ Walk.getVert_mem_support P (R n))

def Chain (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (previous reach : ℕ) : List α → Prop
  | [] => reach = P.length ∧ previous < reach
  | n :: ns => previous ≤ L n ∧ L n < reach ∧ reach < R n ∧ R n ≤ P.length ∧
      Chain P L R reach (R n) ns

def Covered (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (previous reach : ℕ) : List α → V → Prop
  | [], z => ∃ k, previous ≤ k ∧ k ≤ P.length ∧ P.getVert k = z
  | n :: ns, z => (∃ k, previous ≤ k ∧ k ≤ L n ∧ P.getVert k = z) ∨
      z ∈ (Q n).support ∨ Covered P L R Q reach (R n) ns z

theorem rails_finish (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (labels : List α) (previous reach : ℕ)
    (hc : Chain P L R previous reach labels)
    (U : G.Walk (P.getVert 0) (P.getVert previous))
    (W : G.Walk (P.getVert 0) (P.getVert reach))
    (h : Rails P L R Q previous reach U W) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      ∀ z, z ∈ C.support ↔ z ∈ U.support ∨ z ∈ W.support ∨
        Covered P L R Q previous reach labels z := by
  induction labels generalizing previous reach with
  | nil =>
    obtain ⟨he, hprev⟩ := hc
    subst reach
    obtain ⟨hcycle, heq⟩ := rails_close P hp L R Q h hprev hs
    refine ⟨(U.append (Erdos1105.GraphHelpers.pathInterval P previous P.length hprev.le)).append W.reverse,
      hcycle, ?_⟩
    intro z
    rw [heq]
    rw [interval_support P previous P.length hprev.le le_rfl z]
    simp only [Covered]
    simp only [or_comm]
  | cons n ns ih =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    have hn := rails_step P hp L R Q paths contact separate h n ha har hrb hb
    obtain ⟨C, hC, heq⟩ := ih reach (R n) ht W
      ((U.append (Erdos1105.GraphHelpers.pathInterval P previous (L n) ha)).append (Q n)) hn
    refine ⟨C, hC, ?_⟩
    intro z
    rw [heq]
    simp only [Walk.mem_support_append_iff, Covered]
    rw [interval_support P previous (L n) ha (by omega) z]
    simp only [or_assoc, or_left_comm, or_comm]

theorem rails_initial (P : G.Walk u v) (hp : P.IsPath) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (n : α) (hL : L n = 0) :
    Rails P L R Q 0 (R n) Walk.nil ((Q n).copy (by rw [hL]) rfl) := by
  refine ⟨Walk.IsPath.nil, (by simpa only [Walk.isPath_copy] using paths n), ?_, ?_, ?_, ?_⟩
  · intro k hk hmem
    simp only [Walk.support_nil, List.mem_singleton] at hmem
    have := hp.getVert_injOn hk (show 0 ≤ P.length from Nat.zero_le _) hmem
    omega
  · intro k hk hmem
    simp only [Walk.support_copy] at hmem
    rcases contact n k hk hmem with he | he
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr he)
  · intro z hz _
    simpa only [Walk.support_nil, List.mem_singleton] using hz
  · intro z hz hzP
    rcases hz with hz | hz
    · simp only [Walk.support_nil, List.mem_singleton] at hz
      exact (hzP (hz ▸ Walk.getVert_mem_support P 0)).elim
    · simp only [Walk.support_copy] at hz
      refine ⟨n, le_rfl, hz, ?_, ?_⟩
      · intro he
        exact hzP (he ▸ Walk.getVert_mem_support P (L n))
      · intro he
        exact hzP (he ▸ Walk.getVert_mem_support P (R n))

theorem exists_spliced_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (first : α) (hL : L first = 0) (rest : List α)
    (hc : Chain P L R 0 (R first) rest) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      ∀ z, z ∈ C.support ↔ z ∈ (Q first).support ∨ Covered P L R Q 0 (R first) rest z := by
  have hi := rails_initial P hp L R Q paths contact first hL
  obtain ⟨C, hC, heq⟩ := rails_finish P hp hs L R Q paths contact separate rest 0 (R first)
    hc Walk.nil ((Q first).copy (by rw [hL]) rfl) hi
  refine ⟨C, hC, ?_⟩
  intro z
  rw [heq]
  simp only [Walk.support_nil, List.mem_singleton, Walk.support_copy]
  have hroot : P.getVert 0 ∈ (Q first).support := by
    simpa [hL] using (Q first).start_mem_support
  constructor
  · rintro (he | hz | hz)
    · exact Or.inl (he.symm ▸ hroot)
    · exact Or.inl hz
    · exact Or.inr hz
  · intro hz
    exact Or.inr hz

theorem chain_of_greedy (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (F : Finset IntervalVine.Interval) (labels : List α) (previous certificatePrevious reach : ℕ)
    (ht : IntervalVine.GreedyTail F P.length certificatePrevious reach
      (labels.map (fun l => (L l, R l))))
    (hle : previous ≤ certificatePrevious) (hpr : previous < reach) :
    Chain P L R previous reach labels := by
  induction labels generalizing previous certificatePrevious reach with
  | nil =>
    cases ht
    exact ⟨rfl, hpr⟩
  | cons n ns ih =>
    cases ht with
    | step cp reach I rest hmem hleft hcross hadv hbound hmax htie tail =>
      refine ⟨le_trans hle hleft, hcross, hadv, hbound, ?_⟩
      exact ih reach reach (R n) tail le_rfl hadv

theorem actual_family_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    (L R : ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val) →
      Fin (P.length + 1))
    (Q : ∀ l, G.Walk (P.getVert (L l).val) (P.getVert (R l).val))
    (hd : ActualBridgeFamily.Data (fun j : Fin (P.length + 1) => P.getVert j.val) L R Q)
    (first : ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val))
    (hL : (L first).val = 0)
    (rest : List (ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val)))
    (F : Finset IntervalVine.Interval)
    (ht : IntervalVine.GreedyTail F P.length 1 (R first).val
      (rest.map (fun l => ((L l).val, (R l).val)))) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      ∀ z, z ∈ C.support ↔ z ∈ (Q first).support ∨
        Covered P (fun l => (L l).val) (fun l => (R l).val) Q 0 (R first).val rest z := by
  have hpositive : 0 < (R first).val := by
    have := (hd.1 first)
    change (L first).val < (R first).val at this
    omega
  apply exists_spliced_cycle P hp hs (fun l => (L l).val) (fun l => (R l).val) Q
    (fun l => (hd.2.1 l).1) ?_ ?_ first hL rest
    (chain_of_greedy P (fun l => (L l).val) (fun l => (R l).val) F rest 0 1
      (R first).val ht (by omega) hpositive)
  · intro l k hk hmem
    have he := (hd.2.1 l).2 (⟨k, by omega⟩ : Fin (P.length + 1)) hmem
    rcases he with he | he
    · exact Or.inl (congrArg Fin.val he)
    · exact Or.inr (congrArg Fin.val he)
  · intro l r hlr
    simpa only [Interior] using hd.2.2.2.2.2 l r hlr

theorem exists_actual_vine_cycle [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hs : 2 ≤ P.length)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (a b : Fin (P.length + 1)) (ha : 0 < a) (hb : b < Fin.last P.length)
    (hfirstEdge : G.Adj (P.getVert 0) (P.getVert a.val))
    (hlastEdge : G.Adj (P.getVert b.val) (P.getVert P.length)) :
    ∃ L R : ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val) →
      Fin (P.length + 1),
    ∃ Q : ∀ l, G.Walk (P.getVert (L l).val) (P.getVert (R l).val),
    ∃ first, ∃ rest : List (ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val)),
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0),
      ActualBridgeFamily.Data (fun j : Fin (P.length + 1) => P.getVert j.val) L R Q ∧
      (L first).val = 0 ∧ C.IsCycle ∧
      (∀ z, z ∈ C.support ↔ z ∈ (Q first).support ∨
        Covered P (fun l => (L l).val) (fun l => (R l).val) Q 0 (R first).val rest z) := by
  have hinj : Function.Injective (fun j : Fin (P.length + 1) => P.getVert j.val) := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) he
  obtain ⟨L, R, Q, hd, F, fi, intervals, labels, _, _, _, _, hzero, _, _, ht, hmap, _⟩ :=
    ActualBridgeFamily.exists_actual_interval_vine (G := G)
      (fun j : Fin (P.length + 1) => P.getVert j.val) hinj hs hdel a b ha hb
      hfirstEdge hlastEdge
  cases labels with
  | nil => simp at hmap
  | cons first rest =>
    simp only [List.map_cons] at hmap
    obtain ⟨hfi, hrest⟩ := List.cons.inj hmap
    have hL : (L first).val = 0 := (congrArg Prod.fst hfi).trans hzero
    have htail : IntervalVine.GreedyTail F P.length 1 (R first).val
        (rest.map (fun l => ((L l).val, (R l).val))) := by
      have hR : (R first).val = fi.2 := congrArg Prod.snd hfi
      rw [hrest, hR]
      exact ht
    obtain ⟨C, hC, hsupport⟩ := actual_family_cycle P hp hs L R Q hd first hL rest F htail
    exact ⟨L, R, Q, first, rest, C, hd, hL, hC, hsupport⟩

end ErdosProblems.PathUpperReduction.VineCycle

end

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.CrossingEndpoint
open VineCycle
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem crossing_cycle (P : G.Walk u v) (hp : P.IsPath) (i j : ℕ)
    (hj : 0 < j) (hji : j < i) (hi : i < P.length)
    (ha : G.Adj (P.getVert 0) (P.getVert i))
    (hb : G.Adj (P.getVert j) (P.getVert P.length)) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      C.length = P.length + 2 - (i - j) ∧
      ∀ z, z ∈ C.support ↔
        (∃ k, k ≤ j ∧ P.getVert k = z) ∨
        (∃ k, i ≤ k ∧ k ≤ P.length ∧ P.getVert k = z) := by
  let S := Erdos1105.GraphHelpers.pathInterval P 0 j (Nat.zero_le j)
  let T := Erdos1105.GraphHelpers.pathInterval P i P.length hi.le
  let A := S.append hb.toWalk
  let B := ha.toWalk.append T
  have hS : S.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp 0 j (Nat.zero_le j)
  have hT : T.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp i P.length hi.le
  have hA : A.IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only S hb.toWalk hS hb.isPath_toWalk
    intro z hz hzE
    simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
    rcases hzE with he | he
    · exact he
    · have hcontact := interval_contacts P hp 0 j (Nat.zero_le j) (by omega)
        P.length le_rfl (he ▸ hz)
      omega
  have hB : B.IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only ha.toWalk T ha.isPath_toWalk hT
    intro z hzE hz
    simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
    rcases hzE with he | he
    · have hcontact := interval_contacts P hp i P.length hi.le le_rfl 0
        (Nat.zero_le _) (he ▸ hz)
      omega
    · exact he
  have hmeet : ∀ z, z ∈ A.support → z ∈ B.support →
      z = P.getVert 0 ∨ z = P.getVert P.length := by
    intro z hzA hzB
    rcases (Walk.mem_support_append_iff _ _).mp hzA with hzS | hzE
    · rcases (Walk.mem_support_append_iff _ _).mp hzB with hzE | hzT
      · simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
        rcases hzE with he | he
        · exact Or.inl he
        · have := interval_contacts P hp 0 j (Nat.zero_le j) (by omega) i hi.le (he ▸ hzS)
          omega
      · obtain ⟨a, _, haj, haz⟩ := (interval_support P 0 j (Nat.zero_le j) (by omega) z).mp hzS
        obtain ⟨b, hib, hbl, hbz⟩ := (interval_support P i P.length hi.le le_rfl z).mp hzT
        have he := hp.getVert_injOn (show a ≤ P.length from by omega) hbl (haz.trans hbz.symm)
        omega
    · simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
      rcases hzE with he | he
      · have := interval_contacts P hp i P.length hi.le le_rfl j (by omega)
          (he ▸ ((Walk.mem_support_append_iff _ _).mp hzB).resolve_left (by
            intro hmem
            simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h0 | hi0
            · have := hp.getVert_injOn (show j ≤ P.length from by omega) (Nat.zero_le _)
                (he.symm.trans h0)
              omega
            · have := hp.getVert_injOn (show j ≤ P.length from by omega) hi.le
                (he.symm.trans hi0)
              omega))
        omega
      · exact Or.inr he
  have hAlen : A.length = j + 1 := by
    simp [A, S, Erdos1105.GraphHelpers.pathInterval_length P 0 j (Nat.zero_le j) (by omega)]
  have hBlen : B.length = 1 + (P.length - i) := by
    simp [B, T, Erdos1105.GraphHelpers.pathInterval_length P i P.length hi.le le_rfl, Nat.add_comm]
  refine ⟨A.append B.reverse, Erdos1105.GraphHelpers.cycle_of_two_paths A B hA hB hmeet (by omega), ?_, ?_⟩
  · rw [Erdos1105.GraphHelpers.two_paths_cycle_length, hAlen, hBlen]
    omega
  · intro z
    simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse,
      A, B, S, T, SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false]
    rw [interval_support P 0 j (Nat.zero_le j) (by omega) z,
      interval_support P i P.length hi.le le_rfl z]
    have h0 : ∃ k, k ≤ j ∧ P.getVert k = P.getVert 0 := ⟨0, Nat.zero_le _, rfl⟩
    have hjj : ∃ k, k ≤ j ∧ P.getVert k = P.getVert j := ⟨j, le_rfl, rfl⟩
    have his : ∃ k, i ≤ k ∧ k ≤ P.length ∧ P.getVert k = P.getVert P.length :=
      ⟨P.length, hi.le, le_rfl, rfl⟩
    have hii : ∃ k, i ≤ k ∧ k ≤ P.length ∧ P.getVert k = P.getVert i :=
      ⟨i, le_rfl, hi.le, rfl⟩
    aesop

theorem minimal_gap_count (A B : Finset ℕ) (s i j : ℕ)
    (hA : ∀ a ∈ A, 0 < a ∧ a < s) (hB : ∀ b ∈ B, 0 < b ∧ b < s)
    (hi : i ∈ A) (hj : j ∈ B) (hg : 2 ≤ i - j)
    (hmin : ∀ a ∈ A, ∀ b ∈ B, b < a → i - j ≤ a - b) :
    A.card + B.card ≤ s + 2 - (i - j) := by
  classical
  let M := A.image (fun a => a - 1)
  have hM : M.card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have := (hA a ha).1
    have := (hA b hb).1
    change a - 1 = b - 1 at he
    omega
  have hdisj : Disjoint M B := by
    apply Finset.disjoint_left.mpr
    intro x hxM hxB
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxM
    have hpos := (hA a ha).1
    have := hmin a ha x hxB (by omega)
    omega
  have hsnot : s ∉ M ∪ B := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hm | hb
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
      have := (hA a ha).2
      omega
    · have := (hB s hb).2
      omega
  let T := (M ∪ B) ∪ {s}
  have hT : T.card = A.card + B.card + 1 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hsnot),
      Finset.card_union_of_disjoint hdisj, hM, Finset.card_singleton]
  have hiM : i - 1 ∈ T := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hErase : (T.erase (i - 1)).card = A.card + B.card := by
    rw [Finset.card_erase_of_mem hiM, hT]
    omega
  have hsub : T.erase (i - 1) ⊆ Finset.Icc 0 j ∪ Finset.Icc i s := by
    intro x hx
    obtain ⟨hne, hxT⟩ := Finset.mem_erase.mp hx
    rcases Finset.mem_union.mp hxT with hxMB | hxS
    · rcases Finset.mem_union.mp hxMB with hxM | hxB
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxM
        have hap := hA a ha
        by_cases haj : a ≤ j
        · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
        · have hno : i ≤ a := by
            by_contra hn
            have := hmin a ha j hj (by omega)
            omega
          exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · have hxp := hB x hxB
        by_cases hxj : x ≤ j
        · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hxj⟩)
        · have hno : i ≤ x := by
            by_contra hn
            have := hmin i hi x hxB (by omega)
            omega
          exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨hno, by omega⟩)
    · have he : x = s := Finset.mem_singleton.mp hxS
      exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by have := (hA i hi).2; omega, by omega⟩)
  have hd : Disjoint (Finset.Icc 0 j) (Finset.Icc i s) := by
    apply Finset.disjoint_left.mpr
    intro x hxj hxi
    have := (Finset.mem_Icc.mp hxj).2
    have := (Finset.mem_Icc.mp hxi).1
    omega
  have hc := Finset.card_le_card hsub
  rw [hErase, Finset.card_union_of_disjoint hd, Nat.card_Icc, Nat.card_Icc] at hc
  have := hA i hi
  have := hB j hj
  omega

noncomputable def LeftNeighbors (P : G.Walk u v) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 P.length).filter (fun k => G.Adj (P.getVert 0) (P.getVert k))

noncomputable def RightNeighbors (P : G.Walk u v) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 P.length).filter (fun k => G.Adj (P.getVert P.length) (P.getVert k))

theorem mem_left (P : G.Walk u v) (k : ℕ) :
    k ∈ LeftNeighbors P ↔ k ≤ P.length ∧ G.Adj (P.getVert 0) (P.getVert k) := by
  classical
  simp [LeftNeighbors, Finset.mem_Icc]

theorem mem_right (P : G.Walk u v) (k : ℕ) :
    k ∈ RightNeighbors P ↔ k ≤ P.length ∧ G.Adj (P.getVert P.length) (P.getVert k) := by
  classical
  simp [RightNeighbors, Finset.mem_Icc]

theorem neighbors_internal (P : G.Walk u v)
    (hne : ¬ G.Adj (P.getVert 0) (P.getVert P.length)) :
    (∀ a ∈ LeftNeighbors P, 0 < a ∧ a < P.length) ∧
    (∀ b ∈ RightNeighbors P, 0 < b ∧ b < P.length) := by
  constructor
  · intro a ha
    obtain ⟨hab, hadj⟩ := (mem_left P a).mp ha
    have ha0 : a ≠ 0 := by
      intro he
      subst a
      exact G.irrefl hadj
    have hal : a ≠ P.length := by
      intro he
      exact hne (he ▸ hadj)
    omega
  · intro b hb
    obtain ⟨hbb, hadj⟩ := (mem_right P b).mp hb
    have hb0 : b ≠ 0 := by
      intro he
      subst b
      exact hne hadj.symm
    have hbl : b ≠ P.length := by
      intro he
      exact G.irrefl (he ▸ hadj)
    omega

theorem exists_min_crossing (A B : Finset ℕ)
    (hex : ∃ i ∈ A, ∃ j ∈ B, j < i) :
    ∃ i ∈ A, ∃ j ∈ B, j < i ∧
      ∀ a ∈ A, ∀ b ∈ B, b < a → i - j ≤ a - b := by
  classical
  let F := (A.product B).filter (fun p => p.2 < p.1)
  have hF : F.Nonempty := by
    obtain ⟨i, hi, j, hj, hji⟩ := hex
    exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hji⟩⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image F (fun p => p.1 - p.2) hF
  obtain ⟨hpAB, hcross⟩ := Finset.mem_filter.mp hp
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hpAB
  refine ⟨p.1, hi, p.2, hj, hcross, ?_⟩
  intro a ha b hb hba
  exact hmin (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hba⟩)

theorem crossing_threshold (P : G.Walk u v) (hp : P.IsPath)
    (hne : ¬ G.Adj (P.getVert 0) (P.getVert P.length))
    (hex : ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      min (P.length + 1) ((LeftNeighbors P).card + (RightNeighbors P).card) ≤ C.length := by
  obtain ⟨i, hi, j, hj, hji, hmin⟩ := exists_min_crossing (LeftNeighbors P) (RightNeighbors P) hex
  obtain ⟨hA, hB⟩ := neighbors_internal P hne
  have hib := hA i hi
  have hjb := hB j hj
  have hai := ((mem_left P i).mp hi).2
  have hbj := ((mem_right P j).mp hj).2.symm
  obtain ⟨C, hC, hlen, _⟩ := crossing_cycle P hp i j hjb.1 hji hib.2 hai hbj
  refine ⟨C, hC, ?_⟩
  by_cases hg : i - j = 1
  · rw [hlen, hg]
    have := Nat.min_le_left (P.length + 1) ((LeftNeighbors P).card + (RightNeighbors P).card)
    omega
  · have hgap : 2 ≤ i - j := by omega
    have hcount := minimal_gap_count (LeftNeighbors P) (RightNeighbors P) P.length i j hA hB hi hj hgap hmin
    have := Nat.min_le_right (P.length + 1) ((LeftNeighbors P).card + (RightNeighbors P).card)
    omega

theorem adjacent_endpoint_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    (he : G.Adj (P.getVert 0) (P.getVert P.length)) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ C.length = P.length + 1 := by
  let W := P.copy (Walk.getVert_zero P).symm (Walk.getVert_length P).symm
  have hW : W.IsPath := by simpa only [W, Walk.isPath_copy] using hp
  have hlen : W.length = P.length := by simp [W]
  refine ⟨Walk.cons he W.reverse, ?_, ?_⟩
  · exact Erdos1105.GraphHelpers.cycle_of_path_and_edge W.reverse hW.reverse he (by simp only [Walk.length_reverse]; omega)
  · simp [hlen]

theorem endpoint_crossing_branch (P : G.Walk u v) (hp : P.IsPath)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1)
    (hKD : K ≤ (LeftNeighbors P).card + (RightNeighbors P).card)
    (hcase : G.Adj (P.getVert 0) (P.getVert P.length) ∨
      ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  by_cases he : G.Adj (P.getVert 0) (P.getVert P.length)
  · obtain ⟨C, hC, hlen⟩ := adjacent_endpoint_cycle P hp (by omega) he
    exact ⟨C, hC, by omega⟩
  · obtain ⟨C, hC, hlen⟩ := crossing_threshold P hp he (hcase.resolve_left he)
    exact ⟨C, hC, le_trans (Nat.le_min.mpr ⟨hKs, hKD⟩) hlen⟩

theorem path_neighbor_count (P : G.Walk u v) (hp : P.IsPath) (x : V) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    ((Finset.Icc 0 P.length).filter (fun k => G.Adj x (P.getVert k))).card =
      (P.support.toFinset.filter (fun z => G.Adj x z)).card := by
  classical
  let N := (Finset.Icc 0 P.length).filter (fun k => G.Adj x (P.getVert k))
  have himage : N.image P.getVert = P.support.toFinset.filter (fun z => G.Adj x z) := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
      obtain ⟨hki, hadj⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr ?_, hkz ▸ hadj⟩
      exact hkz ▸ Walk.getVert_mem_support P k
    · intro hz
      obtain ⟨hzP, hadj⟩ := Finset.mem_filter.mp hz
      obtain ⟨k, hkz, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hzP)
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkl⟩, ?_⟩, hkz⟩
      exact hkz.symm ▸ hadj
  have hcard : (N.image P.getVert).card = N.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    have hiP := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
    have hjP := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
    exact hp.getVert_injOn hiP hjP he
  rw [himage] at hcard
  exact hcard.symm

theorem left_neighbor_count (P : G.Walk u v) (hp : P.IsPath) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    (LeftNeighbors P).card =
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card := by
  classical
  simpa only [LeftNeighbors] using path_neighbor_count P hp (P.getVert 0)

theorem right_neighbor_count (P : G.Walk u v) (hp : P.IsPath) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    (RightNeighbors P).card =
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card := by
  classical
  simpa only [RightNeighbors] using path_neighbor_count P hp (P.getVert P.length)

theorem endpoint_crossing_vertex_count (P : G.Walk u v) (hp : P.IsPath)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1)
    (hcase : G.Adj (P.getVert 0) (P.getVert P.length) ∨
      ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    K ≤ (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card →
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  intro hKD
  apply endpoint_crossing_branch P hp K hK hKs ?_ hcase
  rw [left_neighbor_count P hp, right_neighbor_count P hp]
  exact hKD

end ErdosProblems.PathUpperReduction.CrossingEndpoint

end

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.BoundaryEndpoint
open VineCycle CrossingEndpoint
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem terminal_fusion (P : G.Walk u v) (hp : P.IsPath) {α : Type*}
    (L R : α → ℕ) (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    {previous reach : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert reach)}
    (h : Rails P L R Q previous reach U W)
    (hpr : previous < reach) (hrs : reach < P.length) (b : ℕ)
    (hpb : previous ≤ b) (hbr : b < reach)
    (he : G.Adj (P.getVert b) (P.getVert P.length)) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ z, z ∈ U.support ∨ z ∈ W.support → z ∈ C.support) ∧
      (∀ k, (previous ≤ k ∧ k ≤ b) ∨ (reach ≤ k ∧ k ≤ P.length) →
        P.getVert k ∈ C.support) := by
  let S := Erdos1105.GraphHelpers.pathInterval P previous b hpb
  let T := Erdos1105.GraphHelpers.pathInterval P reach P.length hrs.le
  let E := he.toWalk
  have hS : S.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp previous b hpb
  have hT : T.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp reach P.length hrs.le
  have hbP : b ≤ P.length := by omega
  have hUS : (U.append S).IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only U S h.1 hS
    intro z hz hzS
    obtain ⟨k, hpk, hkb, hkz⟩ := (interval_support P previous b hpb hbP z).mp hzS
    have := h.2.2.1 k (by omega) (hkz.symm ▸ hz)
    have : k = previous := by omega
    simpa [this] using hkz.symm
  have hUScontact : ∀ k, k ≤ P.length → P.getVert k ∈ (U.append S).support → k ≤ b := by
    intro k hk hmem
    rcases (Walk.mem_support_append_iff _ _).mp hmem with hmem | hmem
    · have := h.2.2.1 k hk hmem
      omega
    · exact (interval_contacts P hp previous b hpb hbP k hk hmem).2
  have hUSE : ((U.append S).append E).IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only (U.append S) E hUS he.isPath_toWalk
    intro z hz hzE
    simp only [E, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
    rcases hzE with hzE | hzE
    · exact hzE
    · have := hUScontact P.length le_rfl (hzE ▸ hz)
      omega
  have hWT : (W.append T).IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only W T h.2.1 hT
    intro z hz hzT
    obtain ⟨k, hrk, hks, hkz⟩ := (interval_support P reach P.length hrs.le le_rfl z).mp hzT
    rcases h.2.2.2.1 k hks (hkz.symm ▸ hz) with he0 | hep | her
    · omega
    · omega
    · simpa [her] using hkz.symm
  let A := (U.append S).append E
  let B := W.append T
  have hmeet : ∀ z, z ∈ A.support → z ∈ B.support →
      z = P.getVert 0 ∨ z = P.getVert P.length := by
    intro z hzA hzB
    rcases (Walk.mem_support_append_iff _ _).mp hzA with hzUS | hzE
    · rcases (Walk.mem_support_append_iff _ _).mp hzB with hzW | hzT
      · rcases (Walk.mem_support_append_iff _ _).mp hzUS with hzU | hzS
        · exact Or.inl (h.2.2.2.2.1 z hzU hzW)
        · obtain ⟨k, hpk, hkb, hkz⟩ := (interval_support P previous b hpb hbP z).mp hzS
          rcases h.2.2.2.1 k (by omega) (hkz.symm ▸ hzW) with he0 | hep | her
          · exact Or.inl (by simpa [he0] using hkz.symm)
          · omega
          · omega
      · obtain ⟨k, hrk, hks, hkz⟩ := (interval_support P reach P.length hrs.le le_rfl z).mp hzT
        have := hUScontact k hks (hkz.symm ▸ hzUS)
        omega
    · simp only [E, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
      rcases hzE with hzE | hzE
      · rcases (Walk.mem_support_append_iff _ _).mp hzB with hzW | hzT
        · rcases h.2.2.2.1 b hbP (hzE ▸ hzW) with he0 | hep | her
          · exact Or.inl (by simpa [he0] using hzE)
          · omega
          · omega
        · have := (interval_contacts P hp reach P.length hrs.le le_rfl b hbP (hzE ▸ hzT)).1
          omega
      · exact Or.inr hzE
  have hWpos : 1 ≤ W.length := by
    by_contra hn
    have heq := Walk.eq_of_length_eq_zero (p := W) (by omega)
    have := hp.getVert_injOn (show 0 ≤ P.length from Nat.zero_le _) hrs.le heq
    omega
  have hTlen : T.length = P.length - reach :=
    Erdos1105.GraphHelpers.pathInterval_length P reach P.length hrs.le le_rfl
  have hlen : 3 ≤ A.length + B.length := by
    simp only [A, B, E, Walk.length_append, Adj.length_toWalk]
    omega
  let C := A.append B.reverse
  refine ⟨C, Erdos1105.GraphHelpers.cycle_of_two_paths A B hUSE hWT hmeet hlen, ?_, ?_⟩
  · intro z hz
    simp only [C, A, B, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
    tauto
  · intro k hk
    rcases hk with hk | hk
    · have hm : P.getVert k ∈ S.support :=
        (interval_support P previous b hpb hbP (P.getVert k)).mpr ⟨k, hk.1, hk.2, rfl⟩
      simp only [C, A, B, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
      tauto
    · have hm : P.getVert k ∈ T.support :=
        (interval_support P reach P.length hrs.le le_rfl (P.getVert k)).mpr ⟨k, hk.1, hk.2, rfl⟩
      simp only [C, A, B, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
      tauto

theorem boundary_finish (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (B : Finset ℕ) (hBP : ∀ b ∈ B, b < P.length)
    (hedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (n : α) (ns : List α) (previous reach : ℕ)
    (hc : Chain P L R previous reach (n :: ns))
    (hterminal : ∀ l ∈ n :: ns, R l = P.length → ∀ b ∈ B, L l ≤ b)
    (U : G.Walk (P.getVert 0) (P.getVert previous))
    (W : G.Walk (P.getVert 0) (P.getVert reach))
    (h : Rails P L R Q previous reach U W) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ z, z ∈ U.support ∨ z ∈ W.support → z ∈ C.support) ∧
      (∀ b ∈ B, P.getVert b ∈ C.support) ∧
      (∀ k, previous ≤ k ∧ k ≤ L n → P.getVert k ∈ C.support) ∧
      P.getVert P.length ∈ C.support := by
  classical
  induction ns generalizing n previous reach with
  | nil =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    have hlast : R n = P.length := ht.1
    have hpr : previous < reach := by omega
    have hrs : reach < P.length := by omega
    let F := B.filter (fun b => b < reach)
    by_cases hF : F.Nonempty
    · obtain ⟨b, hbF, hmax⟩ := Finset.exists_max_image F id hF
      obtain ⟨hbB, hbr⟩ := Finset.mem_filter.mp hbF
      have hnb : L n ≤ b := hterminal n (by simp) hlast b hbB
      obtain ⟨C, hC, hold, hindex⟩ := terminal_fusion P hp L R Q h hpr hrs b
        (by omega) hbr (hedge b hbB)
      refine ⟨C, hC, hold, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hkr : k < reach
        · have hkb : k ≤ b := hmax k (Finset.mem_filter.mpr ⟨hk, hkr⟩)
          have hnk := hterminal n (by simp) hlast k hk
          exact hindex k (Or.inl ⟨by omega, hkb⟩)
        · exact hindex k (Or.inr ⟨by omega, (hBP k hk).le⟩)
      · intro k hk
        exact hindex k (Or.inl ⟨hk.1, le_trans hk.2 hnb⟩)
      · exact hindex P.length (Or.inr ⟨hrs.le, le_rfl⟩)
    · obtain ⟨C, hC, hsupport⟩ := rails_finish P hp hs L R Q paths contact separate
        [n] previous reach ⟨ha, har, hrb, hb, ht⟩ U W h
      refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
      · intro z hz
        apply (hsupport z).mpr
        tauto
      · intro b hbB
        have hrb' : reach ≤ b := by
          by_contra he
          apply hF
          exact ⟨b, Finset.mem_filter.mpr ⟨hbB, by omega⟩⟩
        apply (hsupport (P.getVert b)).mpr
        right; right; right; right
        exact ⟨b, hrb', (hBP b hbB).le, rfl⟩
      · intro k hk
        apply (hsupport (P.getVert k)).mpr
        right; right; left
        exact ⟨k, hk.1, hk.2, rfl⟩
      · apply (hsupport (P.getVert P.length)).mpr
        right; right; right; right
        exact ⟨P.length, hrs.le, le_rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    let S := Erdos1105.GraphHelpers.pathInterval P previous (L n) ha
    have hn := rails_step P hp L R Q paths contact separate h n ha har hrb hb
    have htail : ∀ l ∈ m :: ms, R l = P.length → ∀ b ∈ B, L l ≤ b := by
      intro l hl he b hbB
      exact hterminal l (List.mem_cons_of_mem n hl) he b hbB
    obtain ⟨C, hC, hold, hB, _, hend⟩ := ih m reach (R n) ht htail W
      ((U.append S).append (Q n)) hn
    refine ⟨C, hC, ?_, hB, ?_, hend⟩
    · intro z hz
      apply hold z
      rcases hz with hzU | hzW
      · right
        simp only [Walk.mem_support_append_iff]
        tauto
      · exact Or.inl hzW
    · intro k hk
      have hm : P.getVert k ∈ S.support :=
        (interval_support P previous (L n) ha (by omega) (P.getVert k)).mpr
          ⟨k, hk.1, hk.2, rfl⟩
      apply hold (P.getVert k)
      right
      simp only [Walk.mem_support_append_iff]
      tauto

theorem first_modified_rails (P : G.Walk u v) (hp : P.IsPath) {α : Type*}
    (L R : α → ℕ) (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (first second : α) (hL : L first = 0)
    (hcross : L second < R first) (hrr : R first < R second) (hb : R second ≤ P.length)
    (a : ℕ) (hla : L second < a) (har : a ≤ R first)
    (he : G.Adj (P.getVert 0) (P.getVert a)) :
    ∃ U : G.Walk (P.getVert 0) (P.getVert (R first)),
    ∃ W : G.Walk (P.getVert 0) (P.getVert (R second)),
      Rails P L R Q (R first) (R second) U W ∧
      ∀ k, k ≤ L second ∨ (a ≤ k ∧ k ≤ R first) →
        P.getVert k ∈ U.support ∨ P.getVert k ∈ W.support := by
  let S := Erdos1105.GraphHelpers.pathInterval P 0 (L second) (Nat.zero_le _)
  let W := (Walk.nil.append S).append (Q second)
  let T := Erdos1105.GraphHelpers.pathInterval P a (R first) har
  let U := he.toWalk.append T
  have hrP : R first ≤ P.length := by omega
  have hlP : L second ≤ P.length := by omega
  have haP : a ≤ P.length := by omega
  have ha0 : 0 < a := by omega
  have hi := rails_initial P hp L R Q paths contact first hL
  have hbase : Rails P L R Q (R first) (R second)
      ((Q first).copy (by rw [hL]) rfl) W :=
    rails_step P hp L R Q paths contact separate hi second (Nat.zero_le _) hcross hrr hb
  have hT : T.IsPath := Erdos1105.GraphHelpers.pathInterval_isPath P hp a (R first) har
  have hU : U.IsPath := by
    apply Erdos1105.GraphHelpers.path_append_of_meet_only he.toWalk T he.isPath_toWalk hT
    intro z hz hzT
    simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · obtain ⟨k, hak, hkr, hkz⟩ := (interval_support P a (R first) har hrP z).mp hzT
      have := hp.getVert_injOn (show k ≤ P.length from le_trans hkr hrP)
        (show 0 ≤ P.length from Nat.zero_le _) (hkz.trans hz)
      omega
    · exact hz
  have hUsupport : ∀ z, z ∈ U.support →
      z = P.getVert 0 ∨ ∃ k, a ≤ k ∧ k ≤ R first ∧ P.getVert k = z := by
    intro z hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzE | hzT
    · simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
      rcases hzE with hzE | hzE
      · exact Or.inl hzE
      · exact Or.inr ⟨a, le_rfl, har, hzE.symm⟩
    · exact Or.inr ((interval_support P a (R first) har hrP z).mp hzT)
  have hWcontact : ∀ k, k ≤ P.length → P.getVert k ∈ W.support →
      k ≤ L second ∨ k = R second := by
    intro k hk hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzS | hzQ
    · rcases (Walk.mem_support_append_iff _ _).mp hzS with hz0 | hzS
      · simp only [Walk.support_nil, List.mem_singleton] at hz0
        have := hp.getVert_injOn hk (show 0 ≤ P.length from Nat.zero_le _) hz0
        exact Or.inl (by omega)
      · exact Or.inl ((interval_contacts P hp 0 (L second) (Nat.zero_le _) hlP k hk hzS).2)
    · rcases contact second k hk hzQ with heL | heR
      · exact Or.inl heL.le
      · exact Or.inr heR
  refine ⟨U, W, ⟨hU, hbase.2.1, ?_, hbase.2.2.2.1, ?_, ?_⟩, ?_⟩
  · intro k hk hz
    rcases hUsupport (P.getVert k) hz with he0 | ⟨j, haj, hjr, hjk⟩
    · have := hp.getVert_injOn hk (show 0 ≤ P.length from Nat.zero_le _) he0
      omega
    · have := hp.getVert_injOn (show j ≤ P.length from le_trans hjr hrP) hk hjk
      omega
  · intro z hzU hzW
    rcases hUsupport z hzU with he0 | ⟨k, hak, hkr, hkz⟩
    · exact he0
    · rcases hWcontact k (by omega) (hkz.symm ▸ hzW) with hkL | hkR <;> omega
  · intro z hz hzP
    rcases hz with hzU | hzW
    · rcases hUsupport z hzU with he0 | ⟨k, _, _, hkz⟩
      · exact (hzP (he0 ▸ Walk.getVert_mem_support P 0)).elim
      · exact (hzP (hkz ▸ Walk.getVert_mem_support P k)).elim
    · exact hbase.2.2.2.2.2 z (Or.inr hzW) hzP
  · intro k hk
    rcases hk with hkL | hkA
    · have hm : P.getVert k ∈ S.support :=
        (interval_support P 0 (L second) (Nat.zero_le _) hlP (P.getVert k)).mpr
          ⟨k, Nat.zero_le _, hkL, rfl⟩
      right
      simp only [W, Walk.mem_support_append_iff]
      tauto
    · have hm : P.getVert k ∈ T.support :=
        (interval_support P a (R first) har hrP (P.getVert k)).mpr ⟨k, hkA.1, hkA.2, rfl⟩
      left
      exact (Walk.mem_support_append_iff _ _).mpr (Or.inr hm)

theorem noncrossing_vine_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (first : α) (hL : L first = 0) (rest : List α)
    (hc : Chain P L R 0 (R first) rest)
    (A B : Finset ℕ) (hreach : ∀ a ∈ A, a ≤ R first)
    (hBP : ∀ b ∈ B, b < P.length)
    (hAedge : ∀ a ∈ A, G.Adj (P.getVert 0) (P.getVert a))
    (hBedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (hterminal : ∀ l ∈ rest, R l = P.length → ∀ b ∈ B, L l ≤ b) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ a ∈ A, P.getVert a ∈ C.support) ∧
      (∀ b ∈ B, P.getVert b ∈ C.support) ∧ P.getVert P.length ∈ C.support := by
  classical
  cases rest with
  | nil =>
    have hright : R first = P.length := hc.1
    obtain ⟨C, hC, hsupport⟩ := exists_spliced_cycle P hp hs L R Q paths contact separate
      first hL [] hc
    have hall : ∀ k, k ≤ P.length → P.getVert k ∈ C.support := by
      intro k hk
      apply (hsupport (P.getVert k)).mpr
      right
      exact ⟨k, Nat.zero_le _, hk, rfl⟩
    refine ⟨C, hC, ?_, ?_, hall P.length le_rfl⟩
    · intro a ha
      exact hall a (by have := hreach a ha; omega)
    · intro b hb
      exact hall b (hBP b hb).le
  | cons second ns =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    let F := A.filter (fun a => L second < a)
    by_cases hF : F.Nonempty
    · obtain ⟨a, haF, hmin⟩ := Finset.exists_min_image F id hF
      obtain ⟨haA, hla⟩ := Finset.mem_filter.mp haF
      have ham : ∀ k ∈ A, L second < k → a ≤ k := by
        intro k hk hkl
        exact hmin k (Finset.mem_filter.mpr ⟨hk, hkl⟩)
      obtain ⟨U, W, hrails, hcover⟩ := first_modified_rails P hp L R Q paths contact separate
        first second hL har hrb hb a hla (hreach a haA) (hAedge a haA)
      cases ns with
      | nil =>
        have hright : R second = P.length := ht.1
        let W' := W.copy rfl (congrArg P.getVert hright)
        have hrails' : Rails P L R Q (R first) P.length U W' := by
          simpa only [Rails, W', Walk.support_copy, Walk.isPath_copy, hright] using hrails
        have hprev : R first < P.length := by omega
        let S := Erdos1105.GraphHelpers.pathInterval P (R first) P.length hprev.le
        let C := (U.append S).append W'.reverse
        obtain ⟨hC, hsupport⟩ := rails_close P hp L R Q hrails' hprev hs
        have hkeep : ∀ k, k ≤ L second ∨ (a ≤ k ∧ k ≤ R first) → P.getVert k ∈ C.support := by
          intro k hk
          rcases hcover k hk with hu | hw
          · exact (hsupport (P.getVert k)).mpr (Or.inl hu)
          · have hw' : P.getVert k ∈ W'.support := by simpa only [W', Walk.support_copy] using hw
            exact (hsupport (P.getVert k)).mpr (Or.inr (Or.inr hw'))
        have hsuffix : ∀ k, R first ≤ k → k ≤ P.length → P.getVert k ∈ C.support := by
          intro k hk hkP
          apply (hsupport (P.getVert k)).mpr
          right; left
          exact (interval_support P (R first) P.length hprev.le le_rfl (P.getVert k)).mpr
            ⟨k, hk, hkP, rfl⟩
        refine ⟨C, hC, ?_, ?_, hsuffix P.length hprev.le le_rfl⟩
        · intro k hk
          by_cases hkL : k ≤ L second
          · exact hkeep k (Or.inl hkL)
          · exact hkeep k (Or.inr ⟨ham k hk (by omega), hreach k hk⟩)
        · intro b hbB
          by_cases hbr : b ≤ R first
          · exact hkeep b (Or.inr ⟨hAB a haA b hbB, hbr⟩)
          · exact hsuffix b (by omega) (hBP b hbB).le
      | cons n ns =>
        have hterm : ∀ l ∈ n :: ns, R l = P.length → ∀ b ∈ B, L l ≤ b := by
          intro l hl he b hbB
          exact hterminal l (List.mem_cons_of_mem second hl) he b hbB
        obtain ⟨C, hC, hold, hB, _, hend⟩ := boundary_finish P hp hs L R Q paths contact separate
          B hBP hBedge n ns (R first) (R second) ht hterm U W hrails
        refine ⟨C, hC, ?_, hB, hend⟩
        intro k hk
        apply hold (P.getVert k)
        by_cases hkL : k ≤ L second
        · exact hcover k (Or.inl hkL)
        · exact hcover k (Or.inr ⟨ham k hk (by omega), hreach k hk⟩)
    · let W := (Q first).copy (by rw [hL]) rfl
      have hi := rails_initial P hp L R Q paths contact first hL
      obtain ⟨C, hC, _, hB, hprefix, hend⟩ := boundary_finish P hp hs L R Q paths contact separate
        B hBP hBedge second ns 0 (R first) ⟨ha, har, hrb, hb, ht⟩ hterminal Walk.nil W hi
      refine ⟨C, hC, ?_, hB, hend⟩
      intro a haA
      apply hprefix a
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra he
      exact hF ⟨a, Finset.mem_filter.mpr ⟨haA, by omega⟩⟩

theorem exists_actual_noncrossing_cycle [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hs : 2 ≤ P.length)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAP : ∀ a ∈ A, 0 < a ∧ a < P.length)
    (hBP : ∀ b ∈ B, 0 < b ∧ b < P.length)
    (hAedge : ∀ a ∈ A, G.Adj (P.getVert 0) (P.getVert a))
    (hBedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ a ∈ A, P.getVert a ∈ C.support) ∧
      (∀ b ∈ B, P.getVert b ∈ C.support) ∧ P.getVert P.length ∈ C.support := by
  classical
  obtain ⟨a, haA, hmax⟩ := Finset.exists_max_image A id hA
  obtain ⟨b, hbB, hmin⟩ := Finset.exists_min_image B id hB
  let af : Fin (P.length + 1) := ⟨a, by have := hAP a haA; omega⟩
  let bf : Fin (P.length + 1) := ⟨b, by have := hBP b hbB; omega⟩
  have haf : 0 < af := by exact (hAP a haA).1
  have hbf : bf < Fin.last P.length := by exact (hBP b hbB).2
  have hinj : Function.Injective (fun j : Fin (P.length + 1) => P.getVert j.val) := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) he
  obtain ⟨L, R, Q, hd, F, fi, intervals, labels, _, _, _, _, hzero, hreach, _,
    ht, hmap, _, _, _, _, _, hterminal⟩ :=
    ActualBridgeFamily.exists_actual_interval_vine (G := G)
      (fun j : Fin (P.length + 1) => P.getVert j.val) hinj hs hdel af bf haf hbf
      (hAedge a haA) (hBedge b hbB)
  cases labels with
  | nil => simp at hmap
  | cons first rest =>
    simp only [List.map_cons] at hmap
    obtain ⟨hfi, hrest⟩ := List.cons.inj hmap
    have hL : (L first).val = 0 := (congrArg Prod.fst hfi).trans hzero
    have hR : (R first).val = fi.2 := congrArg Prod.snd hfi
    have htail : IntervalVine.GreedyTail F P.length 1 (R first).val
        (rest.map (fun l => ((L l).val, (R l).val))) := by
      rw [hrest, hR]
      exact ht
    have hpositive : 0 < (R first).val := by
      have hlt := hd.1 first
      change (L first).val < (R first).val at hlt
      omega
    have hc := chain_of_greedy P (fun l => (L l).val) (fun l => (R l).val)
      F rest 0 1 (R first).val htail (by omega) hpositive
    have hfirst : ∀ k ∈ A, k ≤ (R first).val := by
      intro k hk
      have hkmax : k ≤ a := hmax k hk
      change a ≤ fi.2 at hreach
      omega
    have hterm : ∀ l ∈ rest, (R l).val = P.length → ∀ k ∈ B, (L l).val ≤ k := by
      intro l hl he k hk
      have hleft := hterminal l (List.mem_cons_of_mem first hl) he
      change (L l).val ≤ b at hleft
      have hbmin : b ≤ k := hmin k hk
      omega
    apply noncrossing_vine_cycle P hp hs (fun l => (L l).val) (fun l => (R l).val) Q
      (fun l => (hd.2.1 l).1) ?_ ?_ first hL rest hc A B hfirst
      (fun k hk => (hBP k hk).2) hAedge hBedge hAB hterm
    · intro l k hk hmem
      have he := (hd.2.1 l).2 (⟨k, by omega⟩ : Fin (P.length + 1)) hmem
      rcases he with he | he
      · exact Or.inl (congrArg Fin.val he)
      · exact Or.inr (congrArg Fin.val he)
    · intro l r hlr
      simpa only [Interior] using hd.2.2.2.2.2 l r hlr

theorem cycle_vertex_card {x : V} (C : G.Walk x x) (hC : C.IsCycle) :
    letI := Classical.decEq V
    C.support.toFinset.card = C.length := by
  classical
  have heq : C.support.toFinset = C.tail.support.toFinset := by
    rw [← Walk.cons_support_tail (p := C) hC.not_nil]
    simp only [List.toFinset_cons]
    exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr C.tail.end_mem_support)
  rw [heq, List.toFinset_card_of_nodup hC.isPath_tail.support_nodup, Walk.length_support,
    Walk.length_tail_add_one hC.not_nil]

theorem protected_neighbor_count (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    (A B : Finset ℕ) (hAP : ∀ a ∈ A, 0 < a ∧ a < P.length)
    (hBP : ∀ b ∈ B, 0 < b ∧ b < P.length)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (C : G.Walk (P.getVert 0) (P.getVert 0)) (hC : C.IsCycle)
    (hA : ∀ a ∈ A, P.getVert a ∈ C.support)
    (hB : ∀ b ∈ B, P.getVert b ∈ C.support)
    (hend : P.getVert P.length ∈ C.support) :
    A.card + B.card + 1 ≤ C.length := by
  classical
  have hinter : (A ∩ B).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haA, haB⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbA, hbB⟩ := Finset.mem_inter.mp hb
    exact Nat.le_antisymm (hAB a haA b hbB) (hAB b hbA a haB)
  have hzero : 0 ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have := hAP 0 hz
      omega
    · have := hBP 0 hz
      omega
  have hlast : P.length ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have := hAP P.length hz
      omega
    · have := hBP P.length hz
      omega
  let E := insert 0 (insert P.length (A ∪ B))
  have hcard : E.card = (A ∪ B).card + 2 := by
    have hzero' : 0 ∉ insert P.length (A ∪ B) := by simp [hzero]; omega
    simp only [E, Finset.card_insert_of_notMem hzero', Finset.card_insert_of_notMem hlast]
  have hbound : ∀ k ∈ E, k ≤ P.length := by
    intro k hk
    rcases Finset.mem_insert.mp hk with he0 | hk
    · omega
    · rcases Finset.mem_insert.mp hk with hes | hk
      · omega
      · rcases Finset.mem_union.mp hk with hk | hk
        · exact (hAP k hk).2.le
        · exact (hBP k hk).2.le
  have himage : (E.image P.getVert).card = E.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact hp.getVert_injOn (hbound i hi) (hbound j hj) he
  have hsubset : E.image P.getVert ⊆ C.support.toFinset := by
    intro z hz
    obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
    apply List.mem_toFinset.mpr
    subst z
    rcases Finset.mem_insert.mp hk with he0 | hk
    · exact he0 ▸ C.start_mem_support
    · rcases Finset.mem_insert.mp hk with hes | hk
      · exact hes ▸ hend
      · rcases Finset.mem_union.mp hk with hk | hk
        · exact hA k hk
        · exact hB k hk
  have hle := Finset.card_le_card hsubset
  rw [himage, hcard, cycle_vertex_card C hC] at hle
  have hledger := Finset.card_union_add_card_inter A B
  omega

theorem exists_actual_noncrossing_threshold [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hs : 2 ≤ P.length)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAP : ∀ a ∈ A, 0 < a ∧ a < P.length)
    (hBP : ∀ b ∈ B, 0 < b ∧ b < P.length)
    (hAedge : ∀ a ∈ A, G.Adj (P.getVert 0) (P.getVert a))
    (hBedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ A.card + B.card + 1 ≤ C.length := by
  obtain ⟨C, hC, hAcover, hBcover, hend⟩ := exists_actual_noncrossing_cycle P hp hs hdel
    A B hA hB hAP hBP hAedge hBedge hAB
  exact ⟨C, hC, protected_neighbor_count P hp hs A B hAP hBP hAB C hC hAcover hBcover hend⟩

theorem uniform_endpoint_threshold [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1)
    (hKD : K ≤ (LeftNeighbors P).card + (RightNeighbors P).card) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  have hs : 2 ≤ P.length := by omega
  by_cases he : G.Adj (P.getVert 0) (P.getVert P.length)
  · exact endpoint_crossing_branch P hp K hK hKs hKD (Or.inl he)
  · by_cases hcross : ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i
    · exact endpoint_crossing_branch P hp K hK hKs hKD (Or.inr hcross)
    · obtain ⟨hAinternal, hBinternal⟩ := neighbors_internal P he
      have hA : (LeftNeighbors P).Nonempty := by
        refine ⟨1, (mem_left P 1).mpr ⟨by omega, ?_⟩⟩
        exact P.adj_getVert_succ (i := 0) (by omega)
      have hB : (RightNeighbors P).Nonempty := by
        refine ⟨P.length - 1, (mem_right P (P.length - 1)).mpr ⟨by omega, ?_⟩⟩
        have hedge := P.adj_getVert_succ (i := P.length - 1) (by omega)
        have hindex : P.length - 1 + 1 = P.length := by omega
        simpa only [hindex] using hedge.symm
      have hAedge : ∀ a ∈ LeftNeighbors P, G.Adj (P.getVert 0) (P.getVert a) := by
        intro a ha
        exact ((mem_left P a).mp ha).2
      have hBedge : ∀ b ∈ RightNeighbors P, G.Adj (P.getVert b) (P.getVert P.length) := by
        intro b hb
        exact ((mem_right P b).mp hb).2.symm
      have hAB : ∀ a ∈ LeftNeighbors P, ∀ b ∈ RightNeighbors P, a ≤ b := by
        intro a ha b hb
        by_contra hba
        exact hcross ⟨a, ha, b, hb, by omega⟩
      obtain ⟨C, hC, hlen⟩ := exists_actual_noncrossing_threshold P hp hs hdel
        (LeftNeighbors P) (RightNeighbors P) hA hB hAinternal hBinternal hAedge hBedge hAB
      exact ⟨C, hC, by omega⟩

theorem uniform_endpoint_vertex_threshold [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    K ≤ (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card →
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  intro hKD
  apply uniform_endpoint_threshold P hp hdel K hK hKs
  rw [left_neighbor_count P hp, right_neighbor_count P hp]
  exact hKD

end ErdosProblems.PathUpperReduction.BoundaryEndpoint

end

namespace ErdosProblems.PathUpperReduction.CycleCutBothEndpoints1105

open SimpleGraph

theorem last_eq_neg_one (n : ℕ) :
    (Fin.last (n + 2) : Fin (n + 3)) = -1 := by
  apply Fin.ext
  simp only [Fin.val_last, Fin.coe_neg_one]

theorem no_wrap_path_edge (n : ℕ) :
    ¬(pathGraph (n + 3)).Adj (-1) 0 ∧ ¬(pathGraph (n + 3)).Adj 0 (-1) := by
  constructor <;> intro h <;> rcases pathGraph_adj.mp h with h | h <;>
    simp only [Fin.coe_neg_one, Fin.val_zero] at h <;> omega

def path_copy_avoiding {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (old : Sym2 V) (q : Fin (n + 3) → V) (hq : Function.Injective q)
    (hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j))
    (ha : ∀ i j, (pathGraph (n + 3)).Adj i j → s(q i, q j) ≠ old) :
    (pathGraph (n + 3)).Copy (G.deleteEdges {old}) :=
  ⟨⟨q, by
    intro i j hij
    exact deleteEdges_adj.mpr
      ⟨hm i j hij, by simpa only [Set.mem_singleton_iff] using ha i j hij⟩⟩, hq⟩

theorem shift_cycle_adj (n : ℕ) (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (i + r) (j + r) := by
  rw [cycleGraph_adj'] at h ⊢
  simpa only [add_sub_add_right_eq_sub] using h

theorem reverse_cycle_adj (n : ℕ) (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (r - i) (r - j) := by
  have h₁ : (r - i) - (r - j) = j - i := by abel
  have h₂ : (r - j) - (r - i) = i - j := by abel
  rw [cycleGraph_adj'] at h ⊢
  simpa only [h₁, h₂, or_comm] using h

/-- The forward order begins at `c r` and ends at its actual predecessor. -/
theorem path_of_cycle_cut_predecessor_at_both_ends {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G) (r : Fin (n + 3)) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c (r - 1), c r)}),
      p 0 = c r ∧ p (Fin.last (n + 2)) = c (r - 1) ∧
        Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (i + r)
  have hq : Function.Injective q := by
    intro i j h
    exact add_right_cancel (c.injective h)
  have hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    exact c.toHom.map_rel' (shift_cycle_adj n r i j (pathGraph_le_cycleGraph hij))
  have ha : ∀ i j, (pathGraph (n + 3)).Adj i j →
      s(q i, q j) ≠ s(c (r - 1), c r) := by
    intro i j hij he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = -1 := by
        have h := c.injective hi
        calc i = (i + r) - r := by abel
             _ = (r - 1) - r := by rw [h]
             _ = -1 := by abel
      have hj' : j = 0 := by
        have h := c.injective hj
        calc j = (j + r) - r := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      exact (no_wrap_path_edge n).1 (by simpa only [hi', hj'] using hij)
    · have hi' : i = 0 := by
        have h := c.injective hi
        calc i = (i + r) - r := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      have hj' : j = -1 := by
        have h := c.injective hj
        calc j = (j + r) - r := by abel
             _ = (r - 1) - r := by rw [h]
             _ = -1 := by abel
      exact (no_wrap_path_edge n).2 (by simpa only [hi', hj'] using hij)
  refine ⟨path_copy_avoiding G _ q hq hm ha, ?_, ?_, ?_⟩
  · change c (0 + r) = c r
    rw [zero_add]
  · change c (Fin.last (n + 2) + r) = c (r - 1)
    rw [last_eq_neg_one]
    congr 1
    abel
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i + r, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i - r, ?_⟩
      change c (i - r + r) = c i
      rw [sub_add_cancel]

/-- The reverse order begins at `c r` and ends at its actual successor. -/
theorem path_of_cycle_cut_successor_at_both_ends {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G) (r : Fin (n + 3)) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c r, c (r + 1))}),
      p 0 = c r ∧ p (Fin.last (n + 2)) = c (r + 1) ∧
        Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (r - i)
  have hq : Function.Injective q := by
    intro i j h
    have he := c.injective h
    calc i = r - (r - i) := by abel
         _ = r - (r - j) := by rw [he]
         _ = j := by abel
  have hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    exact c.toHom.map_rel' (reverse_cycle_adj n r i j (pathGraph_le_cycleGraph hij))
  have ha : ∀ i j, (pathGraph (n + 3)).Adj i j →
      s(q i, q j) ≠ s(c r, c (r + 1)) := by
    intro i j hij he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 0 := by
        have h := c.injective hi
        calc i = r - (r - i) := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      have hj' : j = -1 := by
        have h := c.injective hj
        calc j = r - (r - j) := by abel
             _ = r - (r + 1) := by rw [h]
             _ = -1 := by abel
      exact (no_wrap_path_edge n).2 (by simpa only [hi', hj'] using hij)
    · have hi' : i = -1 := by
        have h := c.injective hi
        calc i = r - (r - i) := by abel
             _ = r - (r + 1) := by rw [h]
             _ = -1 := by abel
      have hj' : j = 0 := by
        have h := c.injective hj
        calc j = r - (r - j) := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      exact (no_wrap_path_edge n).1 (by simpa only [hi', hj'] using hij)
  refine ⟨path_copy_avoiding G _ q hq hm ha, ?_, ?_, ?_⟩
  · change c (r - 0) = c r
    rw [sub_zero]
  · change c (r - Fin.last (n + 2)) = c (r + 1)
    rw [last_eq_neg_one]
    congr 1
    abel
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨r - i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨r - i, ?_⟩
      change c (r - (r - i)) = c i
      congr 1
      abel

/-- Cutting any actual cycle edge retains the prescribed ordered endpoints. -/
theorem path_of_cycle_cut_edge_at_both_endpoints {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (u v : Fin (n + 3)) (huv : (cycleGraph (n + 3)).Adj u v) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c u, c v)}),
      p 0 = c u ∧ p (Fin.last (n + 2)) = c v ∧
        Set.range p = Set.range c := by
  classical
  rcases cycleGraph_adj'.mp huv with h | h
  · have hdiff : u - v = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simpa only [Fin.val_one] using h
    have hv : v = u - 1 := by
      have he := sub_eq_iff_eq_add.mp hdiff
      calc v = (1 + v) - 1 := by abel
           _ = u - 1 := by rw [← he]
    have he : s(c (u - 1), c u) = s(c u, c v) := by
      rw [hv]
      exact Sym2.eq_swap
    rw [← he, hv]
    exact path_of_cycle_cut_predecessor_at_both_ends G c u
  · have hdiff : v - u = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simpa only [Fin.val_one] using h
    have hv : v = u + 1 := by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp hdiff)
    rw [hv]
    exact path_of_cycle_cut_successor_at_both_ends G c u

end ErdosProblems.PathUpperReduction.CycleCutBothEndpoints1105

namespace ErdosProblems.PathUpperReduction.EndpointAttachment1105

open SimpleGraph

/-- Two distinct fresh endpoint contacts extend a path by two vertices. -/
theorem attach_two_to_pathCopy {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (P : (pathGraph (m + 1)).Copy G) (z z' : V)
    (hz : z ∉ Set.range P) (hz' : z' ∉ Set.range P) (hne : z ≠ z')
    (hleft : G.Adj z (P 0)) (hright : G.Adj (P (Fin.last m)) z') :
    (pathGraph (m + 3)) ⊑ G := by
  classical
  let Q : Fin (m + 2) → V := Fin.cons z P
  let W : Fin (m + 3) → V := Fin.snoc Q z'
  have hQinj : Function.Injective Q :=
    Fin.cons_injective_of_injective hz P.injective
  have hz'Q : z' ∉ Set.range Q := by
    rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero =>
        apply hne
        simpa only [Q, Fin.cons_zero] using hi
    | succ j =>
        apply hz'
        exact ⟨j, by simpa only [Q, Fin.cons_succ] using hi⟩
  have hWinj : Function.Injective W :=
    Fin.snoc_injective_of_injective hQinj hz'Q
  have hQmap (i j : Fin (m + 2)) (hij : i.val + 1 = j.val) :
      G.Adj (Q i) (Q j) := by
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      have hj : j = (0 : Fin (m + 1)).succ := Fin.ext (by simp; omega)
      rw [hi, hj]
      simpa only [Q, Fin.cons_zero, Fin.cons_succ] using hleft
    · let ii : Fin (m + 1) := ⟨i.val - 1, by have hi := i.isLt; omega⟩
      let jj : Fin (m + 1) := ⟨j.val - 1, by have hj := j.isLt; omega⟩
      have hi : i = ii.succ := Fin.ext (by dsimp [ii]; omega)
      have hj : j = jj.succ := Fin.ext (by dsimp [jj]; omega)
      have hadj : (pathGraph (m + 1)).Adj ii jj :=
        pathGraph_adj.mpr (Or.inl (by dsimp [ii, jj]; omega))
      rw [hi, hj]
      simpa only [Q, Fin.cons_succ, Copy.toHom_apply] using P.toHom.map_adj hadj
  have hforward (i j : Fin (m + 3)) (hij : i.val + 1 = j.val) :
      G.Adj (W i) (W j) := by
    by_cases hjlast : j.val = m + 2
    · have hj : j = Fin.last (m + 2) := Fin.ext hjlast
      have hi : i = (Fin.last (m + 1)).castSucc := Fin.ext (by simp; omega)
      have hlast : Fin.last (m + 1) = (Fin.last m).succ := Fin.ext (by simp)
      rw [hi, hj]
      simpa only [W, Fin.snoc_castSucc, Fin.snoc_last, hlast,
        Q, Fin.cons_succ] using hright
    · let ii : Fin (m + 2) := ⟨i.val, by have hi := i.isLt; omega⟩
      let jj : Fin (m + 2) := ⟨j.val, by have hj := j.isLt; omega⟩
      have hi : i = ii.castSucc := Fin.ext rfl
      have hj : j = jj.castSucc := Fin.ext rfl
      rw [hi, hj]
      simp only [W, Fin.snoc_castSucc]
      exact hQmap ii jj hij
  let phi : (pathGraph (m + 3)) →g G := ⟨W, by
    intro i j hij
    rcases pathGraph_adj.mp hij with h | h
    · exact hforward i j h
    · exact (hforward j i h).symm⟩
  exact ⟨⟨phi, hWinj⟩⟩

/-- Original path-freedom excludes those two actual fresh endpoint contacts. -/
theorem endpoint_contacts_incompatible_of_free {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (hfree : (pathGraph (m + 3)).Free G)
    (P : (pathGraph (m + 1)).Copy G) (z z' : V)
    (hz : z ∉ Set.range P) (hz' : z' ∉ Set.range P) (hne : z ≠ z') :
    ¬(G.Adj z (P 0) ∧ G.Adj (P (Fin.last m)) z') := by
  rintro ⟨hleft, hright⟩
  exact hfree (attach_two_to_pathCopy G m P z z' hz hz' hne hleft hright)

end ErdosProblems.PathUpperReduction.EndpointAttachment1105

namespace ErdosProblems.PathUpperReduction.CommonOutsideNeighbors1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CycleCutBothEndpoints1105
open ErdosProblems.PathUpperReduction.EndpointAttachment1105

/-- Opposite contacts at an actual consecutive cycle edge would produce the
forbidden path on all cycle vertices plus the two actual outsiders. -/
theorem successor_contacts_incompatible_of_free {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (hfree : (pathGraph (n + 5)).Free G)
    (u v : V) (hu : u ∉ Set.range c) (hv : v ∉ Set.range c)
    (hne : u ≠ v) (i : Fin (n + 3)) :
    ¬(G.Adj u (c i) ∧ G.Adj v (c (i + 1))) := by
  classical
  have hi : (cycleGraph (n + 3)).Adj i (i + 1) :=
    cycleGraph_adj.mpr (Or.inr (by abel))
  obtain ⟨p, hp0, hplast, hprange⟩ :=
    path_of_cycle_cut_edge_at_both_endpoints G c i (i + 1) hi
  let P : (pathGraph (n + 3)).Copy G :=
    ⟨⟨p, by
      intro a b hab
      exact (deleteEdges_adj.mp (p.toHom.map_rel' hab)).1⟩, p.injective⟩
  have hP0 : P 0 = c i := by
    change p 0 = c i
    exact hp0
  have hPlast : P (Fin.last (n + 2)) = c (i + 1) := by
    change p (Fin.last (n + 2)) = c (i + 1)
    exact hplast
  have hPrange : Set.range P = Set.range c := by
    change Set.range p = Set.range c
    exact hprange
  have huP : u ∉ Set.range P := by
    rw [hPrange]
    exact hu
  have hvP : v ∉ Set.range P := by
    rw [hPrange]
    exact hv
  rintro ⟨hui, hvi⟩
  apply endpoint_contacts_incompatible_of_free G (n + 2) hfree P u v huP hvP hne
  constructor
  · simpa only [hP0] using hui
  · simpa only [hPlast] using hvi.symm

/-- Derived per-outsider alternation forces the SAME actual cycle contact set.
The toggles are explicit intermediate hypotheses, to be derived by the graph
caller; no parity half or common-contact-set oracle is supplied. -/
theorem outside_contact_sets_agree_of_toggles {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (hfree : (pathGraph (n + 5)).Free G)
    (u v : V) (hu : u ∉ Set.range c) (hv : v ∉ Set.range c)
    (hne : u ≠ v)
    (htoggleu : ∀ i : Fin (n + 3), G.Adj u (c (i + 1)) ↔ ¬G.Adj u (c i))
    (htogglev : ∀ i : Fin (n + 3), G.Adj v (c (i + 1)) ↔ ¬G.Adj v (c i)) :
    {i : Fin (n + 3) | G.Adj u (c i)} =
      {i : Fin (n + 3) | G.Adj v (c i)} := by
  classical
  ext i
  change G.Adj u (c i) ↔ G.Adj v (c i)
  constructor
  · intro hui
    by_contra hnvi
    have hvs : G.Adj v (c (i + 1)) := (htogglev i).mpr hnvi
    exact (successor_contacts_incompatible_of_free G c hfree u v hu hv hne i)
      ⟨hui, hvs⟩
  · intro hvi
    by_contra hnui
    have hus : G.Adj u (c (i + 1)) := (htoggleu i).mpr hnui
    exact (successor_contacts_incompatible_of_free G c hfree v u hv hu hne.symm i)
      ⟨hvi, hus⟩

end ErdosProblems.PathUpperReduction.CommonOutsideNeighbors1105

section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.CorePreliminaries1105

variable {V : Type*} [Fintype V]

theorem nonempty_degree_core_card_ge_add_two (G : SimpleGraph V) (d : ℕ)
    (hC : (degreeCore G d).Nonempty) :
    d + 2 ≤ (degreeCore G d).card := by
  classical
  obtain ⟨x, hx⟩ := hC
  have hgood : d < ((degreeCore G d).filter (fun z => G.Adj x z)).card :=
    degree_core_good G d x hx
  have hstrict : (degreeCore G d).filter (fun z => G.Adj x z) ⊂ degreeCore G d :=
    Finset.filter_ssubset.mpr ⟨x, hx, G.irrefl⟩
  have hcard : ((degreeCore G d).filter (fun z => G.Adj x z)).card <
      (degreeCore G d).card := Finset.card_lt_card hstrict
  have hstep : d + 1 < (degreeCore G d).card :=
    lt_of_le_of_lt (Nat.succ_le_of_lt hgood) hcard
  exact Nat.succ_le_of_lt hstep

theorem exists_vertex_ne_pair (hN : 3 ≤ Fintype.card V) (x z : V) :
    ∃ w : V, w ≠ x ∧ w ≠ z := by
  classical
  have huniv : 2 < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    exact lt_of_lt_of_le (by decide : 2 < 3) hN
  have hpair : ({x, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hsmall : ({x, z} : Finset V).card < (Finset.univ : Finset V).card :=
    lt_of_le_of_lt hpair huniv
  obtain ⟨w, _hw, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
  exact ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩

theorem exists_adj_avoiding_deleted_vertex (G : SimpleGraph V)
    (hN : 3 ≤ Fintype.card V)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (x z : V) (hxz : x ≠ z) :
    ∃ y : V, G.Adj x y ∧ y ≠ z := by
  classical
  obtain ⟨w, hwx, hwz⟩ := exists_vertex_ne_pair hN x z
  let x' : {v : V | v ≠ z} := ⟨x, hxz⟩
  let w' : {v : V | v ≠ z} := ⟨w, hwz⟩
  have hne : x' ≠ w' := by
    intro h
    exact hwx (congrArg (fun q : {v : V | v ≠ z} => q.val) h).symm
  have hreach : (G.induce {v | v ≠ z}).Reachable x' w' := (hdel z) x' w'
  obtain ⟨y, hy⟩ := SimpleGraph.Reachable.nonempty_neighborSet_left hne hreach
  exact ⟨y.val, SimpleGraph.induce_adj.mp hy, y.property⟩

theorem two_distinct_neighbors_of_deletion_connected (G : SimpleGraph V)
    (hN : 3 ≤ Fintype.card V)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) (x : V) :
    ∃ a b : V, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
  obtain ⟨z, hzx, _hzx⟩ := exists_vertex_ne_pair hN x x
  obtain ⟨a, hxa, _haz⟩ := exists_adj_avoiding_deleted_vertex G hN hdel x z hzx.symm
  obtain ⟨b, hxb, hba⟩ := exists_adj_avoiding_deleted_vertex G hN hdel x a hxa.ne
  exact ⟨a, b, hba.symm, hxa, hxb⟩

theorem ambient_neighbor_filter_card_ge_two (G : SimpleGraph V)
    (hN : 3 ≤ Fintype.card V)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) (x : V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    2 ≤ ((Finset.univ : Finset V).filter (fun z => G.Adj x z)).card := by
  classical
  obtain ⟨a, b, hab, hxa, hxb⟩ := two_distinct_neighbors_of_deletion_connected G hN hdel x
  have ha : a ∈ (Finset.univ : Finset V).filter (fun z => G.Adj x z) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, hxa⟩
  have hb : b ∈ (Finset.univ : Finset V).filter (fun z => G.Adj x z) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ b, hxb⟩
  have hcard : 1 < ((Finset.univ : Finset V).filter (fun z => G.Adj x z)).card :=
    Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  exact Nat.succ_le_of_lt hcard

end ErdosProblems.PathUpperReduction.CorePreliminaries1105

end

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.EndpointCapture

variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- A maximum in the actual nonadjacent endpoint family captures its left neighbors. -/
theorem left_neighbors_on_path (A B : Finset V) (P : G.Walk x y)
    (hp : P.IsPath) (hy : y ∈ B) {K : ℕ} (hK : 5 ≤ K)
    (hKP : K ≤ P.length + 1)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K)
    (hmax : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length) :
    ∀ z ∈ A, G.Adj x z → z ∈ P.support := by
  intro z hz hxz
  by_contra hzOutside
  let Q := Walk.cons hxz.symm P
  have hQ : Q.IsPath := hp.cons hzOutside
  by_cases hzy : G.Adj z y
  · have htwo : 2 ≤ Q.length := by
      simp only [Q, Walk.length_cons]
      omega
    let C := Walk.cons hzy.symm Q
    have hC : C.IsCycle := Erdos1105.GraphHelpers.cycle_of_path_and_edge Q hQ hzy.symm htwo
    have hshort := noLong y C hC
    simp only [C, Q, Walk.length_cons] at hshort
    omega
  · have hbound := hmax z hz y hy hzy Q hQ
    simp only [Q, Walk.length_cons] at hbound
    omega

/-- Reversal derives the exact right-endpoint family rather than fixing endpoints. -/
theorem neighbors_on_path (A B : Finset V) (P : G.Walk x y)
    (hp : P.IsPath) (hx : x ∈ A) (hy : y ∈ B) {K : ℕ} (hK : 5 ≤ K)
    (hKP : K ≤ P.length + 1)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K)
    (hmax : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b →
      ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length) :
    (∀ z ∈ A, G.Adj x z → z ∈ P.support) ∧
      (∀ z ∈ B, G.Adj y z → z ∈ P.support) := by
  constructor
  · exact left_neighbors_on_path A B P hp hy hK hKP noLong hmax
  · have hrevmax : ∀ a ∈ B, ∀ b ∈ A, ¬ G.Adj a b →
        ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.reverse.length := by
      intro a ha b hb hab Q hQ
      have hba : ¬ G.Adj b a := fun h ↦ hab h.symm
      simpa using hmax b hb a ha hba Q.reverse hQ.reverse
    have hc := left_neighbors_on_path B A P.reverse hp.reverse hx hK
      (by simpa using hKP) noLong hrevmax
    intro z hz hyz
    simpa using hc z hz hyz

/-- A finite actual endpoint family containing P has an actual maximum at least as long. -/
theorem exists_family_maximum [Finite V] (A B : Finset V) (P : G.Walk x y)
    (hp : P.IsPath) (hx : x ∈ A) (hy : y ∈ B) (hxy : ¬ G.Adj x y) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ Q : G.Walk a b, Q.IsPath ∧ ¬ G.Adj a b ∧
      P.length ≤ Q.length ∧
      (∀ c ∈ A, ∀ d ∈ B, ¬ G.Adj c d →
        ∀ R : G.Walk c d, R.IsPath → R.length ≤ Q.length) := by
  classical
  let _ := Fintype.ofFinite V
  let s : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ B, ∃ Q : G.Walk a b,
    Q.IsPath ∧ ¬ G.Adj a b ∧ Q.length = n}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (by
      intro n hn
      obtain ⟨a, ha, b, hb, Q, hQ, hab, hlen⟩ := hn
      exact hlen ▸ hQ.length_lt.le)
  have hseed : P.length ∈ s := ⟨x, hx, y, hy, P, hp, hxy, rfl⟩
  obtain ⟨n, ⟨hn, hmax⟩⟩ := hs.exists_maximal ⟨P.length, hseed⟩
  obtain ⟨a, ha, b, hb, Q, hQ, hab, hlen⟩ := hn
  have hbound : ∀ c ∈ A, ∀ d ∈ B, ¬ G.Adj c d →
      ∀ R : G.Walk c d, R.IsPath → R.length ≤ Q.length := by
    intro c hc d hd hcd R hR
    have hm := hmax (show R.length ∈ s from ⟨c, hc, d, hd, R, hR, hcd, rfl⟩)
    omega
  exact ⟨a, ha, b, hb, Q, hQ, hab, hbound x hx y hy hxy P hp, hbound⟩

/-- The maximum and both neighbor-capture facts are derived from one initial actual path. -/
theorem exists_captured_family_maximum [Finite V] (A B : Finset V)
    (P : G.Walk x y) (hp : P.IsPath) (hx : x ∈ A) (hy : y ∈ B)
    (hxy : ¬ G.Adj x y) {K : ℕ} (hK : 5 ≤ K) (hKP : K ≤ P.length + 1)
    (noLong : ∀ q (C : G.Walk q q), C.IsCycle → C.length < K) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ Q : G.Walk a b, Q.IsPath ∧ ¬ G.Adj a b ∧
      P.length ≤ Q.length ∧
      (∀ c ∈ A, ∀ d ∈ B, ¬ G.Adj c d →
        ∀ R : G.Walk c d, R.IsPath → R.length ≤ Q.length) ∧
      (∀ z ∈ A, G.Adj a z → z ∈ Q.support) ∧
      (∀ z ∈ B, G.Adj b z → z ∈ Q.support) := by
  obtain ⟨a, ha, b, hb, Q, hQ, hab, hlen, hmax⟩ :=
    exists_family_maximum A B P hp hx hy hxy
  have hKQ : K ≤ Q.length + 1 := by omega
  obtain ⟨hleft, hright⟩ := neighbors_on_path A B Q hQ ha hb hK hKQ noLong hmax
  exact ⟨a, ha, b, hb, Q, hQ, hab, hlen, hmax, hleft, hright⟩

end ErdosProblems.PathUpperReduction.EndpointCapture

end

section

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

end

section

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

end

section

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

end

section

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

end

noncomputable section
namespace ErdosProblems.PathUpperReduction.ConnectedPathBoundChecked1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)
open ErdosProblems.PathUpperReduction.CoreEndpointBound1105 (extremalCount)

theorem connected_path_free_edge_bound {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : 5 ≤ k) (hkn : k ≤ n) (hG : G.Connected)
    (hfree : (pathGraph k).Free G) :
    Nat.card G.edgeSet ≤ max (extremalCount n (k - 1) 1)
      (extremalCount n (k - 1) ((k - 2) / 2)) := by
  classical
  have hc := UniformConeStructure1105.finite_connected_path_free_cone
    G hk hkn hG hfree
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hbound := GraphCoreBound1105.long_cycle_free_edge_bound
    (cone G) (K := k + 1) (by omega) (by simpa only [hN] using Nat.add_le_add_right hkn 1)
    hc.2.2.1 (by
      intro z
      exact hc.2.1 z)
  rw [hN] at hbound
  have hcount : Nat.card (cone G).edgeSet = Nat.card G.edgeSet + n := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hc.2.2.2
  rw [hcount, Nat.add_comm (Nat.card G.edgeSet) n] at hbound
  exact (ConnectedPathScalarChecked1105.cone_endpoint_bound_iff n k
    (Nat.card G.edgeSet) hk hkn).mp hbound

end ErdosProblems.PathUpperReduction.ConnectedPathBoundChecked1105
end

noncomputable section
namespace ErdosProblems.PathUpperReduction.ComponentScalarCap1105

open SimpleGraph
open ErdosProblems.PathLemmaFourEnvelope (scalarCap h)
open ErdosProblems.PathUpperReduction.CoreEndpointBound1105 (extremalCount)

theorem connected_component_scalar_cap {V : Type*} [Finite V]
    (a : ℕ) (ha : 4 ≤ a) (G : SimpleGraph V)
    (f : (pathGraph a).Copy G)
    (hfree : (pathGraph (a + 1)).Free G) (hconn : G.Connected) :
    Nat.card G.edgeSet ≤ scalarCap a (Nat.card V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hav : a ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (fun x : Fin a => f x) f.injective
  by_cases hva : Fintype.card V = a
  · have hb : Nat.card G.edgeSet ≤ (Fintype.card V).choose 2 := by
      simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
        G.card_edgeFinset_le_card_choose_two
    simpa only [Nat.card_eq_fintype_card, scalarCap, ite_eq_left hva.le] using hb
  · have hn : a + 1 ≤ Fintype.card V := by omega
    have hnotle : ¬Fintype.card V ≤ a := by omega
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e.symm
    let i : H ≃g G := SimpleGraph.Iso.comap e.symm G
    have hc : H.Connected := i.connected_iff.mpr hconn
    have hf : (pathGraph (a + 1)).Free H :=
      (SimpleGraph.free_congr_right i).mpr hfree
    have hb :=
      ConnectedPathBoundChecked1105.connected_path_free_edge_bound
        H (by omega) hn hc hf
    have he : Nat.card H.edgeSet = Nat.card G.edgeSet :=
      Nat.card_congr i.mapEdgeSet
    rw [he] at hb
    have hm1 : a + 1 - 1 = a := by omega
    have hm2 : a + 1 - 2 = a - 1 := by omega
    simpa only [Nat.card_eq_fintype_card, scalarCap, ite_eq_right hnotle,
      h, extremalCount, hm1, hm2] using hb

end ErdosProblems.PathUpperReduction.ComponentScalarCap1105
end

section

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

end

section

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

end

namespace ErdosProblems.PathUpperReduction.CycleChordPath1105

open SimpleGraph

/-- In coordinates rooted at the first chord endpoint, the order is
`1,...,t,0,m-1,...,t+1`. -/
def chordOrder {n : ℕ} (t i : Fin (n + 3)) : Fin (n + 3) :=
  if h : i.val < t.val then
    ⟨i.val + 1, by have ht := t.isLt; omega⟩
  else if he : i.val = t.val then 0
  else
    ⟨n + 3 + t.val - i.val, by
      have hi := i.isLt
      have ht := t.isLt
      omega⟩

theorem chordOrder_val {n : ℕ} (t i : Fin (n + 3)) :
    (chordOrder t i).val =
      if i.val < t.val then i.val + 1
      else if i.val = t.val then 0
      else n + 3 + t.val - i.val := by
  by_cases h : i.val < t.val
  · simp only [chordOrder, dite_eq_left h, ite_eq_left h]
  · by_cases he : i.val = t.val
    · simp only [chordOrder, dite_eq_right h, dite_eq_left he,
        ite_eq_right h, ite_eq_left he, Fin.val_zero]
    · simp only [chordOrder, dite_eq_right h, dite_eq_right he,
        ite_eq_right h, ite_eq_right he]

theorem chordOrder_injective {n : ℕ} (t : Fin (n + 3)) :
    Function.Injective (chordOrder t) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [chordOrder_val, chordOrder_val] at hv
  have ha := a.isLt
  have hb := b.isLt
  have ht := t.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem chordOrder_surjective {n : ℕ} (t : Fin (n + 3)) :
    Function.Surjective (chordOrder t) := by
  intro l
  by_cases hz : l.val = 0
  · refine ⟨t, ?_⟩
    apply Fin.ext
    rw [chordOrder_val]
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    exact hz.symm
  · by_cases hl : l.val ≤ t.val
    · let k : Fin (n + 3) := ⟨l.val - 1, by have h := l.isLt; omega⟩
      have hk : k.val < t.val := by dsimp [k]; omega
      refine ⟨k, ?_⟩
      apply Fin.ext
      rw [chordOrder_val, ite_eq_left hk]
      dsimp [k]
      omega
    · let k : Fin (n + 3) :=
        ⟨n + 3 + t.val - l.val, by
          have h := l.isLt
          have ht := t.isLt
          omega⟩
      have hk : ¬k.val < t.val := by dsimp [k]; have h := l.isLt; omega
      have hkne : k.val ≠ t.val := by dsimp [k]; have h := l.isLt; omega
      refine ⟨k, ?_⟩
      apply Fin.ext
      rw [chordOrder_val, ite_eq_right hk, ite_eq_right hkne]
      dsimp [k]
      have h := l.isLt
      have ht := t.isLt
      omega

theorem chordOrder_zero {n : ℕ} (t : Fin (n + 3))
    (ht : 0 < t.val) : chordOrder t 0 = 1 := by
  have hpos : (0 : Fin (n + 3)).val < t.val := ht
  apply Fin.ext
  rw [chordOrder_val, ite_eq_left hpos]
  simp only [Fin.val_zero, Fin.val_one]

theorem chordOrder_last {n : ℕ} (t : Fin (n + 3)) :
    chordOrder t (Fin.last (n + 2)) = t + 1 := by
  have ht := t.isLt
  have hnlt : ¬n + 2 < t.val := by omega
  by_cases he : t.val = n + 2
  · have hq : (chordOrder t (Fin.last (n + 2))).val = 0 := by
      rw [chordOrder_val]
      simp only [Fin.val_last, ite_eq_right hnlt, ite_eq_left he.symm]
    apply Fin.ext
    rw [hq, Fin.val_add]
    simp only [Fin.val_one]
    rw [he]
    have hsum : n + 2 + 1 = n + 3 := by omega
    rw [hsum, Nat.mod_self]
  · have hq : (chordOrder t (Fin.last (n + 2))).val = t.val + 1 := by
      rw [chordOrder_val]
      simp only [Fin.val_last, ite_eq_right hnlt, ite_eq_right (Ne.symm he)]
      omega
    apply Fin.ext
    rw [hq, Fin.val_add_eq_of_add_lt]
    · simp only [Fin.val_one]
    · simp only [Fin.val_one]
      omega

theorem shifted_cycle_adj {n : ℕ} (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (i + r) (j + r) := by
  rw [cycleGraph_adj'] at h ⊢
  simpa only [add_sub_add_right_eq_sub] using h

theorem original_successive_adj {V : Type*} {n : ℕ}
    {G : SimpleGraph V} (c : (cycleGraph (n + 3)).Copy G)
    {a b : Fin (n + 3)} (hab : a.val + 1 = b.val) :
    G.Adj (c a) (c b) :=
  c.toHom.map_rel' (pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl hab)))

theorem chordOrder_successive_adj {V : Type*} {n : ℕ}
    {G : SimpleGraph V} (c : (cycleGraph (n + 3)).Copy G)
    (t : Fin (n + 3)) (hchord : G.Adj (c t) (c 0))
    {a b : Fin (n + 3)} (hab : a.val + 1 = b.val) :
    G.Adj (c (chordOrder t a)) (c (chordOrder t b)) := by
  have haLt := a.isLt
  have hbLt := b.isLt
  have htLt := t.isLt
  by_cases ha : a.val < t.val
  · by_cases hb : b.val < t.val
    · apply original_successive_adj c
      rw [chordOrder_val, chordOrder_val, ite_eq_left ha, ite_eq_left hb]
      omega
    · have hbe : b.val = t.val := by omega
      have hqa : chordOrder t a = t := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_left ha]
        omega
      have hqb : chordOrder t b = 0 := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_right hb, ite_eq_left hbe]
        rfl
      rw [hqa, hqb]
      exact hchord
  · have hb : ¬b.val < t.val := by omega
    by_cases hae : a.val = t.val
    · have hbne : b.val ≠ t.val := by omega
      have hqa : chordOrder t a = 0 := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_right ha, ite_eq_left hae]
        rfl
      have hqb : chordOrder t b = Fin.last (n + 2) := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_right hb, ite_eq_right hbne]
        simp only [Fin.val_last]
        omega
      rw [hqa, hqb]
      apply c.toHom.map_rel'
      simp [cycleGraph_adj]
    · have hbne : b.val ≠ t.val := by omega
      apply SimpleGraph.Adj.symm
      apply original_successive_adj c
      rw [chordOrder_val, chordOrder_val, ite_eq_right hb, ite_eq_right hbne,
        ite_eq_right ha, ite_eq_right hae]
      omega

/-- The actual chord endpoints determine the path internally.  Both endpoints
and the entire original cycle population are certified in the conclusion. -/
theorem path_of_actual_cycle_chord {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (c : (cycleGraph (n + 3)).Copy G) (r s : Fin (n + 3))
    (hrs : r ≠ s) (hchord : G.Adj (c r) (c s)) :
    ∃ p : (pathGraph (n + 3)).Copy G,
      p 0 = c (r + 1) ∧
      p (Fin.last (n + 2)) = c (s + 1) ∧
      Set.range p = Set.range c := by
  classical
  let f : (cycleGraph (n + 3)) →g G :=
    ⟨fun i => c (i + r), fun hab => c.toHom.map_rel' (shifted_cycle_adj r _ _ hab)⟩
  have hf : Function.Injective f := by
    intro i j h
    change c (i + r) = c (j + r) at h
    exact add_right_cancel (c.injective h)
  let c' := f.toCopy hf
  let t : Fin (n + 3) := s - r
  have htne : t ≠ 0 := by
    change s - r ≠ 0
    exact sub_ne_zero.mpr (Ne.symm hrs)
  have htpos : 0 < t.val := by
    have h : t.val ≠ 0 := by
      intro he
      apply htne
      apply Fin.ext
      simpa only [Fin.val_zero] using he
    omega
  have hchord' : G.Adj (c' t) (c' 0) := by
    change G.Adj (c ((s - r) + r)) (c (0 + r))
    simpa only [sub_add_cancel, zero_add] using hchord.symm
  let h : (pathGraph (n + 3)) →g G :=
    ⟨fun i => c' (chordOrder t i), by
      intro i j hij
      rcases pathGraph_adj.mp hij with hij | hji
      · exact chordOrder_successive_adj c' t hchord' hij
      · exact (chordOrder_successive_adj c' t hchord' hji).symm⟩
  have hinj : Function.Injective h := by
    intro i j hij
    exact chordOrder_injective t (c'.injective hij)
  let p := h.toCopy hinj
  refine ⟨p, ?_, ?_, ?_⟩
  · change c ((chordOrder t 0) + r) = c (r + 1)
    rw [chordOrder_zero t htpos]
    exact congrArg c (add_comm (1 : Fin (n + 3)) r)
  · change c ((chordOrder t (Fin.last (n + 2))) + r) = c (s + 1)
    rw [chordOrder_last]
    change c ((s - r + 1) + r) = c (s + 1)
    congr 1
    abel
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨chordOrder t i + r, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := chordOrder_surjective t (i - r)
      refine ⟨k, ?_⟩
      change c (chordOrder t k + r) = c i
      rw [hk, sub_add_cancel]

end ErdosProblems.PathUpperReduction.CycleChordPath1105

namespace ErdosProblems.PathUpperReduction.LongCycleOutside1105

open SimpleGraph

/-- A simple cycle has exactly its length many distinct actual vertices. -/
theorem support_finset_card_of_cycle {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) :
    C.support.toFinset.card = C.length := by
  classical
  have hsame : C.support.toFinset = C.support.tail.toFinset := by
    calc
      C.support.toFinset = (a :: C.support.tail).toFinset :=
        congrArg List.toFinset C.cons_tail_support.symm
      _ = insert a C.support.tail.toFinset := by rw [List.toFinset_cons]
      _ = C.support.tail.toFinset :=
        Finset.insert_eq_of_mem (List.mem_toFinset.mpr
          (C.end_mem_tail_support hC.not_nil))
  rw [hsame, List.toFinset_card_of_nodup hC.support_nodup]
  simp only [List.length_tail, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]

/-- Any actual vertex outside a cycle in the original connected graph forces
an actual path with one more vertex than that cycle. -/
theorem path_copy_of_cycle_with_outside_vertex {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (z : V) (hz : z ∉ C.support) : pathGraph (C.length + 1) ⊑ G := by
  classical
  let O : Set V := {w | w ∉ C.support}
  have hzO : z ∈ O := hz
  have haO : a ∉ O := fun ha => ha C.start_mem_support
  obtain ⟨p⟩ := hconn z a
  obtain ⟨b, _, hbOutside, hbNotOutside⟩ := p.exists_boundary_dart O hzO haO
  have hbCycle : b.snd ∈ C.support := by
    by_contra hb
    exact hbNotOutside hb
  let rot := C.rotate b.snd hbCycle
  have hrot : rot.IsCycle := hC.rotate hbCycle
  have hbDrop : b.fst ∉ rot.dropLast.support := by
    intro hb
    rw [rot.support_dropLast hrot.not_nil] at hb
    have hbRot := List.mem_of_mem_dropLast hb
    exact hbOutside ((C.mem_support_rotate_iff b.snd hbCycle).mp hbRot)
  let q := SimpleGraph.Walk.cons b.adj rot.dropLast
  have hq : q.IsPath := hrot.isPath_dropLast.cons hbDrop
  have hdrop : rot.dropLast.length + 1 = C.length := by
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = C.length := SimpleGraph.Walk.length_rotate C b.snd hbCycle
  have hlength : q.length + 1 = C.length + 1 := by
    change (rot.dropLast.length + 1) + 1 = C.length + 1
    omega
  have hcopy : (pathGraph (q.length + 1)).Copy G := hq.pathGraphCopy
  rw [hlength] at hcopy
  exact ⟨hcopy⟩

/-- Original host surplus and path freedom exclude an actual cycle on one
fewer vertices than the forbidden path. No separate cycle cap is assumed. -/
theorem no_cycle_of_order_one_below_forbidden_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (d : ℕ)
    (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) : C.length ≠ 2 * d + 1 := by
  classical
  intro hlength
  have hsmall : C.support.toFinset.card < (Finset.univ : Finset V).card := by
    rw [support_finset_card_of_cycle G C hC, Finset.card_univ]
    omega
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hzOutside : z ∉ C.support := by
    intro hzC
    exact hz (List.mem_toFinset.mpr hzC)
  have hcopy := path_copy_of_cycle_with_outside_vertex G hconn C hC z hzOutside
  have heq : C.length + 1 = 2 * d + 2 := by omega
  rw [heq] at hcopy
  exact hfree hcopy

end ErdosProblems.PathUpperReduction.LongCycleOutside1105

namespace ErdosProblems.PathUpperReduction.CycleInsertion1105

open SimpleGraph

theorem cycle_of_fresh_endpoint_contact {V : Type*} (G : SimpleGraph V)
    {u v : V} (P : G.Walk u v) (hP : P.IsPath) (z : V)
    (hLength : 1 ≤ P.length) (hz : z ∉ P.support)
    (hzu : G.Adj z u) (hvz : G.Adj v z) :
    (SimpleGraph.Walk.cons hzu (P.concat hvz)).IsCycle ∧
      (SimpleGraph.Walk.cons hzu (P.concat hvz)).length = P.length + 2 := by
  classical
  constructor
  · apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.tail_cons,
        SimpleGraph.Walk.isPath_copy]
      exact hP.concat hz hvz
    · simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
      omega
  · simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]

theorem cycle_of_dropLast_and_fresh_contact {V : Type*} (G : SimpleGraph V)
    {u : V} (C : G.Walk u u) (hC : C.IsCycle) (z : V)
    (hz : z ∉ C.support) (hzu : G.Adj z u) (hvz : G.Adj C.penultimate z) :
    (SimpleGraph.Walk.cons hzu (C.dropLast.concat hvz)).IsCycle ∧
      (SimpleGraph.Walk.cons hzu (C.dropLast.concat hvz)).length = C.length + 1 := by
  classical
  have hzDrop : z ∉ C.dropLast.support := by
    intro hz'
    rw [C.support_dropLast hC.not_nil] at hz'
    exact hz (List.mem_of_mem_dropLast hz')
  have hdrop : C.dropLast.length + 1 = C.length :=
    SimpleGraph.Walk.length_dropLast_add_one hC.not_nil
  have hthree : 3 ≤ C.length := hC.three_le_length
  have hpositive : 1 ≤ C.dropLast.length := by omega
  obtain ⟨hnew, hnewLength⟩ := cycle_of_fresh_endpoint_contact G C.dropLast
    hC.isPath_dropLast z hpositive hzDrop hzu hvz
  refine ⟨hnew, ?_⟩
  calc
    (SimpleGraph.Walk.cons hzu (C.dropLast.concat hvz)).length =
        C.dropLast.length + 2 := hnewLength
    _ = C.length + 1 := by omega

end ErdosProblems.PathUpperReduction.CycleInsertion1105

namespace ErdosProblems.PathUpperReduction.CycleEdgeContact1105

open SimpleGraph

/-- The natural order of an actual path Copy gives an original simple walk,
including every copied vertex and both endpoint equations. -/
theorem walk_of_path_copy {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (q : (pathGraph (n + 3)).Copy G) :
    ∃ P : G.Walk (q 0) (q (Fin.last (n + 2))),
      P.IsPath ∧ P.length = n + 2 ∧
        ∀ w : V, w ∈ P.support ↔ w ∈ Set.range q := by
  classical
  let l : List V := List.ofFn (fun i : Fin (n + 3) => q i)
  have hne : l ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [l, List.length_ofFn, List.length_nil] at hlen
    omega
  have hchain : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hi' : i + 1 < n + 3 := by
      simpa only [l, List.length_ofFn] using hi
    have ha : G.Adj (q ⟨i, by omega⟩) (q ⟨i + 1, hi'⟩) :=
      q.toHom.map_rel' (pathGraph_adj.mpr (Or.inl rfl))
    simpa only [l, List.getElem_ofFn] using ha
  have hhead : l.head hne = q 0 := by
    exact List.head_ofFn hne
  have hlast : l.getLast hne = q (Fin.last (n + 2)) := by
    exact List.getLast_ofFn_succ (fun i : Fin (n + 3) => q i)
  let W : G.Walk (l.head hne) (l.getLast hne) :=
    SimpleGraph.Walk.ofSupport l hne hchain
  let P : G.Walk (q 0) (q (Fin.last (n + 2))) := W.copy hhead hlast
  refine ⟨P, ?_, ?_, ?_⟩
  · apply (SimpleGraph.Walk.isPath_copy W hhead hlast).mpr
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [W, SimpleGraph.Walk.support_ofSupport, l] using
      (List.nodup_ofFn_ofInjective (f := fun i : Fin (n + 3) => q i) (by
        intro a b h
        exact q.injective h))
  · simp only [P, W, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_ofSupport, l, List.length_ofFn]
    omega
  · intro w
    change w ∈ (W.copy hhead hlast).support ↔ w ∈ Set.range q
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]
    exact List.mem_ofFn

/-- A vertex outside an actual cycle Copy that contacts the endpoints of an
actual cycle edge yields an explicitly constructed longer original cycle. -/
theorem cycle_of_fresh_contacts_to_cycle_edge {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (u v : Fin (n + 3))
    (huv : (cycleGraph (n + 3)).Adj u v) (z : V)
    (hz : z ∉ Set.range c) (hzu : G.Adj z (c u)) (hvz : G.Adj (c v) z) :
    ∃ D : G.Walk z z, D.IsCycle ∧ D.length = n + 4 := by
  classical
  obtain ⟨p, hp0, hpLast, hpRange⟩ :=
    CycleCutBothEndpoints1105.path_of_cycle_cut_edge_at_both_endpoints G c u v huv
  let q : (pathGraph (n + 3)).Copy G :=
    ⟨⟨(fun i => p i), by
      intro i j hij
      exact (SimpleGraph.deleteEdges_adj.mp (p.toHom.map_rel' hij)).1⟩,
      p.injective⟩
  obtain ⟨P, hP, hPLength, hPSupport⟩ := walk_of_path_copy G q
  have hq0 : q 0 = c u := hp0
  have hqLast : q (Fin.last (n + 2)) = c v := hpLast
  let Q : G.Walk (c u) (c v) := P.copy hq0 hqLast
  have hQ : Q.IsPath := (SimpleGraph.Walk.isPath_copy P hq0 hqLast).mpr hP
  have hQLength : Q.length = n + 2 := by
    simpa only [Q, SimpleGraph.Walk.length_copy] using hPLength
  have hzQ : z ∉ Q.support := by
    intro hm
    have hmP : z ∈ P.support := by
      simpa only [Q, SimpleGraph.Walk.support_copy] using hm
    have hmRange := (hPSupport z).mp hmP
    change z ∈ Set.range p at hmRange
    exact hz (hpRange ▸ hmRange)
  obtain ⟨hD, hDLength⟩ := CycleInsertion1105.cycle_of_fresh_endpoint_contact
    G Q hQ z (by omega) hzQ hzu hvz
  refine ⟨SimpleGraph.Walk.cons hzu (Q.concat hvz), hD, ?_⟩
  omega

end ErdosProblems.PathUpperReduction.CycleEdgeContact1105

namespace ErdosProblems.PathUpperReduction.CycleHalfAlternation1105

/-- An independent half-sized set under a permutation fills exactly one half
of the carrier, and the permutation interchanges membership and nonmembership.
The disjointness, exact size, and exhaustive partition are conclusions. -/
theorem half_partition_and_alternation
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (N : Finset α) (d : ℕ)
    (hα : Fintype.card α = 2 * d)
    (hN : d ≤ N.card)
    (havoid : ∀ i ∈ N, σ i ∉ N) :
    Disjoint N (N.image σ) ∧
      (N.image σ).card = N.card ∧
      N.card = d ∧
      N ∪ N.image σ = Finset.univ ∧
      ∀ i : α, σ i ∈ N ↔ i ∉ N := by
  have hdisjoint : Disjoint N (N.image σ) := by
    apply Finset.disjoint_left.mpr
    intro x hxN hxImage
    rcases Finset.mem_image.mp hxImage with ⟨i, hiN, hix⟩
    apply havoid i hiN
    rw [hix]
    exact hxN
  have himage : (N.image σ).card = N.card :=
    Finset.card_image_of_injective N σ.injective
  have hunionCard : (N ∪ N.image σ).card = N.card + N.card := by
    rw [Finset.card_union_of_disjoint hdisjoint, himage]
  have hle : N.card + N.card ≤ 2 * d := by
    have h := Finset.card_le_univ (N ∪ N.image σ)
    rw [hunionCard, hα] at h
    exact h
  have hcard : N.card = d := by
    omega
  have hunion : N ∪ N.image σ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hunionCard, hcard, hα]
    omega
  refine ⟨hdisjoint, himage, hcard, hunion, ?_⟩
  intro i
  constructor
  · intro hσi hiN
    exact havoid i hiN hσi
  · intro hiN
    have hσiUnion : σ i ∈ N ∪ N.image σ := by
      rw [hunion]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hσiUnion with hσiN | hσiImage
    · exact hσiN
    · rcases Finset.mem_image.mp hσiImage with ⟨j, hjN, hji⟩
      have hji' : j = i := σ.injective hji
      exact False.elim (hiN (hji' ▸ hjN))

end ErdosProblems.PathUpperReduction.CycleHalfAlternation1105

namespace ErdosProblems.PathUpperReduction.CycleContactCap1105

open SimpleGraph

/-- Original path freedom and host surplus forbid a fresh vertex's two
contacts to an actual edge of the supplied original cycle Copy. -/
theorem no_fresh_cycle_edge_contacts
    {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (hsize : n + 3 = 2 * d)
    (u v : Fin (n + 3)) (huv : (cycleGraph (n + 3)).Adj u v)
    (z : V) (hz : z ∉ Set.range c) :
    ¬(G.Adj z (c u) ∧ G.Adj z (c v)) := by
  rintro ⟨hzu, hzv⟩
  obtain ⟨D, hD, hDLength⟩ :=
    CycleEdgeContact1105.cycle_of_fresh_contacts_to_cycle_edge
      G c u v huv z hz hzu hzv.symm
  have horder : D.length = 2 * d + 1 := by omega
  exact LongCycleOutside1105.no_cycle_of_order_one_below_forbidden_path
    G hconn d hcard hfree D hD horder

/-- Literal ORIGINAL contacts, with no preselected half. -/
def actualContacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (z : V) : Finset (Fin (n + 3)) :=
  Finset.univ.filter (fun i => G.Adj z (c i))

/-- With actual outside-independence, every actual neighbor of an outsider
lies in the original cycle range; injection then gives the exact degree. -/
theorem contact_card_eq_degree_of_outside_independence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G)
    (hind : ∀ x y : V, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y)
    (z : V) (hz : z ∉ Set.range c) :
    (actualContacts G c z).card = G.degree z := by
  have himage : (actualContacts G c z).image c = G.neighborFinset z := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
      apply (G.mem_neighborFinset z (c i)).mpr
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      have hadj : G.Adj z v := (G.mem_neighborFinset z v).mp hv
      have hrange : v ∈ Set.range c := by
        by_contra hvOutside
        exact hind z v hz hvOutside hadj
      rcases hrange with ⟨i, rfl⟩
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hadj⟩, rfl⟩
  calc
    (actualContacts G c z).card = ((actualContacts G c z).image c).card :=
      (Finset.card_image_of_injective (actualContacts G c z) c.injective).symm
    _ = G.degree z := by rw [himage, SimpleGraph.card_neighborFinset_eq_degree]

/-- The original degree bound becomes a pointwise successor toggle. The
longer-cycle cap is derived, and the contact count is proved above. Only the
actual outside-independence/support transport remains a conditional premise. -/
theorem actual_contact_card_and_successor_toggle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hmin : ∀ v : V, d ≤ G.degree v)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (hsize : n + 3 = 2 * d)
    (hind : ∀ x y : V, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y)
    (z : V) (hz : z ∉ Set.range c) :
    (actualContacts G c z).card = d ∧
      ∀ i : Fin (n + 3), G.Adj z (c (i + 1)) ↔ ¬G.Adj z (c i) := by
  let N := actualContacts G c z
  have hdegree : N.card = G.degree z :=
    contact_card_eq_degree_of_outside_independence G c hind z hz
  have hN : d ≤ N.card := by rw [hdegree]; exact hmin z
  have havoid : ∀ i ∈ N, finRotate (n + 3) i ∉ N := by
    intro i hi hnext
    have hzi : G.Adj z (c i) := (Finset.mem_filter.mp hi).2
    have hznext : G.Adj z (c (finRotate (n + 3) i)) :=
      (Finset.mem_filter.mp hnext).2
    rw [finRotate_apply] at hznext
    have hedge : (cycleGraph (n + 3)).Adj i (i + 1) := by
      simp [cycleGraph_adj]
    exact no_fresh_cycle_edge_contacts G d hconn hcard hfree c hsize
      i (i + 1) hedge z hz ⟨hzi, hznext⟩
  obtain ⟨_, _, hNcard, _, htoggle⟩ :=
    CycleHalfAlternation1105.half_partition_and_alternation
      (finRotate (n + 3)) N d (by simpa only [Fintype.card_fin] using hsize) hN havoid
  refine ⟨hNcard, ?_⟩
  intro i
  simpa only [finRotate_apply, N, actualContacts, Finset.mem_filter,
    Finset.mem_univ, true_and] using htoggle i

end ErdosProblems.PathUpperReduction.CycleContactCap1105

namespace ErdosProblems.PathUpperReduction.CycleIndex1105

open SimpleGraph

/-- Before its repeated closing vertex, an actual simple cycle enumerates
distinct original vertices. -/
theorem cycle_getVert_injective {V : Type*} (G : SimpleGraph V) {a : V}
    (C : G.Walk a a) (hC : C.IsCycle) :
    Function.Injective (fun i : Fin C.length => C.getVert i.val) := by
  intro i j hij
  have hiBound := i.isLt
  have hjBound := j.isLt
  apply Fin.ext
  exact hC.getVert_injOn'
    (show i.val ≤ C.length - 1 from by omega)
    (show j.val ≤ C.length - 1 from by omega) hij

/-- The finite enumeration contains every actual cycle vertex, including the
start vertex, and introduces no vertex outside its original support. -/
theorem cycle_getVert_range {V : Type*} (G : SimpleGraph V) {a : V}
    (C : G.Walk a a) (hC : C.IsCycle) :
    Set.range (fun i : Fin C.length => C.getVert i.val) = {v | v ∈ C.support} := by
  have hpositive : 0 < C.length := by
    have hthree := hC.three_le_length
    omega
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact C.getVert_mem_support i.val
  · intro hv
    obtain ⟨j, hjv, hjLength⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    by_cases hj : j < C.length
    · exact ⟨⟨j, hj⟩, hjv⟩
    · have hjLast : j = C.length := by omega
      refine ⟨⟨0, hpositive⟩, ?_⟩
      change C.getVert 0 = v
      rw [C.getVert_zero]
      rw [hjLast, C.getVert_length] at hjv
      exact hjv

/-- Cyclic successor indices of an actual closed walk give original adjacent
vertices.  The last index wraps to zero by the actual endpoint equality. -/
theorem closed_walk_getVert_cyclic_adj {V : Type*} (G : SimpleGraph V) {a : V}
    (C : G.Walk a a) (i : Fin C.length) :
    G.Adj (C.getVert i.val) (C.getVert ((i.val + 1) % C.length)) := by
  have hiBound := i.isLt
  have hadj := C.adj_getVert_succ hiBound
  by_cases hi : i.val + 1 < C.length
  · rw [Nat.mod_eq_of_lt hi]
    exact hadj
  · have hiLast : i.val + 1 = C.length := by omega
    rw [hiLast, C.getVert_length] at hadj
    rw [hiLast, Nat.mod_self, C.getVert_zero]
    exact hadj

end ErdosProblems.PathUpperReduction.CycleIndex1105

namespace ErdosProblems.PathUpperReduction.CycleCopy1105

open SimpleGraph

/-- Every actual simple cycle gives an injective actual cycle-graph copy with
exactly its original support, without a supplied copy or enumeration. -/
theorem exists_cycle_copy_with_exact_support {V : Type*} (G : SimpleGraph V)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) :
    ∃ c : SimpleGraph.Copy (cycleGraph C.length) G,
      (∀ i : Fin C.length, c i = C.getVert i.val) ∧
      Set.range c = {v | v ∈ C.support} := by
  have hthree : 3 ≤ C.length := hC.three_le_length
  let : NeZero C.length := ⟨by omega⟩
  have hone : (1 : Fin C.length).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hmap : ∀ i j : Fin C.length, (cycleGraph C.length).Adj i j →
      G.Adj (C.getVert i.val) (C.getVert j.val) := by
    intro i j hij
    rcases SimpleGraph.cycleGraph_adj'.mp hij with hijDiff | hjiDiff
    · have hdiff : i - j = (1 : Fin C.length) := by
        apply Fin.ext
        rw [hone]
        exact hijDiff
      have hi : i = j + 1 := sub_eq_iff_eq_add'.mp hdiff
      rw [hi, Fin.val_add, hone]
      exact (CycleIndex1105.closed_walk_getVert_cyclic_adj G C j).symm
    · have hdiff : j - i = (1 : Fin C.length) := by
        apply Fin.ext
        rw [hone]
        exact hjiDiff
      have hj : j = i + 1 := sub_eq_iff_eq_add'.mp hdiff
      rw [hj, Fin.val_add, hone]
      exact CycleIndex1105.closed_walk_getVert_cyclic_adj G C i
  let f : (cycleGraph C.length) →g G :=
    { toFun := fun i => C.getVert i.val
      map_rel' := fun {i j} hij => hmap i j hij }
  let c : SimpleGraph.Copy (cycleGraph C.length) G :=
    f.toCopy (CycleIndex1105.cycle_getVert_injective G C hC)
  refine ⟨c, ?_, ?_⟩
  · intro i
    rfl
  · change Set.range (fun i : Fin C.length => C.getVert i.val) = {v | v ∈ C.support}
    exact CycleIndex1105.cycle_getVert_range G C hC

end ErdosProblems.PathUpperReduction.CycleCopy1105

namespace ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105

open SimpleGraph

/-- Interleave one anchor before each covering path, retaining the last anchor.
The length guard used by the lemmas is anchors.length = paths.length + 1. -/
def stitch {V : Type*} : List V → List (List V) → List V
  | [], _ => []
  | a :: as, [] => a :: as
  | a :: as, p :: ps => a :: (p ++ stitch as ps)

theorem stitch_head? {V : Type*} (as : List V) (ps : List (List V)) :
    (stitch as ps).head? = as.head? := by
  cases as <;> cases ps <;> rfl

theorem stitch_ne_nil {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) : stitch as ps ≠ [] := by
  cases as with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as => cases ps <;> simp [stitch]

theorem stitch_mem {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) (z : V) :
    z ∈ stitch as ps ↔ z ∈ as ∨ z ∈ ps.flatten := by
  induction ps generalizing as z with
  | nil => cases as <;> simp [stitch]
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      simp only [stitch, List.mem_cons, List.mem_append, List.flatten_cons,
        ih (as := as) (z := z) hrest]
      aesop

theorem stitch_getLast? {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) :
    (stitch as ps).getLast? = as.getLast? := by
  induction ps generalizing as with
  | nil => cases as <;> rfl
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      cases as with
      | nil => simp only [List.length_nil] at hrest; omega
      | cons b bs =>
        have htail : stitch (b :: bs) ps ≠ [] := stitch_ne_nil _ _ hrest
        calc
          (stitch (a :: b :: bs) (p :: ps)).getLast? =
              (stitch (b :: bs) ps).getLast? := by
            change ((a :: p) ++ stitch (b :: bs) ps).getLast? = _
            exact List.getLast?_append_of_ne_nil _ htail
          _ = (b :: bs).getLast? := ih _ hrest
          _ = (a :: b :: bs).getLast? := by rw [List.getLast?_cons_cons]

theorem stitch_nodup {V : Type*} (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1) (ha : as.Nodup)
    (hp : ps.flatten.Nodup)
    (hsep : ∀ z, z ∈ as → z ∈ ps.flatten → False) :
    (stitch as ps).Nodup := by
  induction ps generalizing as with
  | nil => cases as <;> simpa only [stitch] using ha
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      rcases List.nodup_cons.mp ha with ⟨hanot, has⟩
      have hpapp : (p ++ ps.flatten).Nodup := by
        simpa only [List.flatten_cons] using hp
      rcases List.nodup_append'.mp hpapp with ⟨hpn, hpsn, hpsep⟩
      have hseprest : ∀ z, z ∈ as → z ∈ ps.flatten → False := by
        intro z hz hzp
        exact hsep z (List.mem_cons.mpr (Or.inr hz))
          (by simpa only [List.flatten_cons, List.mem_append] using
            (Or.inr hzp : z ∈ p ∨ z ∈ ps.flatten))
      have htail := ih as hrest has hpsn hseprest
      have hpTail : p.Disjoint (stitch as ps) := by
        rw [List.disjoint_left]
        intro z hzp hzt
        rcases (stitch_mem as ps hrest z).mp hzt with hza | hzps
        · exact hsep z (List.mem_cons.mpr (Or.inr hza))
            (by simpa only [List.flatten_cons, List.mem_append] using
              (Or.inl hzp : z ∈ p ∨ z ∈ ps.flatten))
        · exact List.disjoint_left.mp hpsep hzp hzps
      have happ : (p ++ stitch as ps).Nodup := hpn.append htail hpTail
      have hanotAll : a ∉ p ++ stitch as ps := by
        intro hz
        rcases List.mem_append.mp hz with hzp | hzt
        · exact hsep a (by simp)
            (by simpa only [List.flatten_cons, List.mem_append] using
              (Or.inl hzp : a ∈ p ∨ a ∈ ps.flatten))
        · rcases (stitch_mem as ps hrest a).mp hzt with hza | hzps
          · exact hanot hza
          · exact hsep a (by simp)
              (by simpa only [List.flatten_cons, List.mem_append] using
                (Or.inr hzps : a ∈ p ∨ a ∈ ps.flatten))
      exact List.nodup_cons.mpr ⟨hanotAll, happ⟩

theorem stitch_chain {V : Type*} (F : SimpleGraph V)
    (C O : Set V) (as : List V) (ps : List (List V))
    (hlen : as.length = ps.length + 1)
    (ha : ∀ a, a ∈ as → a ∈ C)
    (hp : ∀ p, p ∈ ps → p ≠ [] ∧ p.IsChain F.Adj ∧
      ∀ x, x ∈ p → x ∈ O)
    (hcross : ∀ x, x ∈ O → ∀ a, a ∈ C → F.Adj x a) :
    (stitch as ps).IsChain F.Adj := by
  induction ps generalizing as with
  | nil =>
    cases as with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons a as =>
      have has : as = [] := by
        have hzero : as.length = 0 := by
          simp only [List.length_cons, List.length_nil] at hlen
          omega
        exact List.length_eq_zero_iff.mp hzero
      subst as
      simpa only [stitch] using List.IsChain.singleton (R := F.Adj) a
  | cons p ps ih =>
    cases as with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons a as =>
      have hrest : as.length = ps.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      have hastail : ∀ b, b ∈ as → b ∈ C := by
        intro b hb
        exact ha b (List.mem_cons.mpr (Or.inr hb))
      have hpstail : ∀ q, q ∈ ps → q ≠ [] ∧ q.IsChain F.Adj ∧
          ∀ x, x ∈ q → x ∈ O := by
        intro q hq
        exact hp q (List.mem_cons.mpr (Or.inr hq))
      have htail := ih as hrest hastail hpstail
      rcases hp p (by simp) with ⟨hpne, hpchain, hpO⟩
      have hjoin : (p ++ stitch as ps).IsChain F.Adj := by
        apply hpchain.append htail
        intro x hx b hb
        have hxO : x ∈ O := hpO x (List.mem_of_mem_getLast? hx)
        have hbhead : b ∈ as.head? := by
          simpa only [stitch_head?] using hb
        exact hcross x hxO b (hastail b (List.mem_of_mem_head? hbhead))
      change (a :: (p ++ stitch as ps)).IsChain F.Adj
      apply hjoin.cons
      intro x hx
      have hxhead : x ∈ p.head? := by
        simpa only [List.head?_append_of_ne_nil _ hpne] using hx
      exact (hcross x (hpO x (List.mem_of_mem_head? hxhead)) a
        (ha a (by simp))).symm

/-- Actual original outsider paths covering the SAME carrier, with enough
complete contacted-core anchors in F, yield an injective spanning cycle in F.
The cover has no placement, anchor-order or desired-cycle premise. -/
theorem cycle_of_actual_outsider_path_cover {d : ℕ} (hd : 1 ≤ d)
    (G F : SimpleGraph (Fin (2 * d + 3))) (hGF : G ≤ F)
    (S C : Finset (Fin (2 * d + 3))) (_hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3)))) (hCS : C ⊆ S)
    (cover : List (List (Fin (2 * d + 3))))
    (hnonempty : ∀ p, p ∈ cover → p ≠ [])
    (hpaths : ∀ p, p ∈ cover → p.IsChain G.Adj)
    (hdisjoint : cover.flatten.Nodup)
    (hcovers : ∀ z, z ∈ cover.flatten ↔ z ∉ S)
    (hcapacity : cover.length + 1 ≤ C.card)
    (hfilled : ∀ x, x ∉ S → ∀ a, a ∈ C → F.Adj x a) :
    cycleGraph (2 * d + 3) ⊑ F := by
  classical
  obtain ⟨A, hAC, hAcard⟩ := Finset.exists_subset_card_eq hcapacity
  have hAS : A ⊆ S := fun z hz => hCS (hAC hz)
  let anchors : List (Fin (2 * d + 3)) := A.toList
  have halign : anchors.length = cover.length + 1 := by
    simpa only [anchors, Finset.length_toList] using hAcard
  have hAnchorCover : ∀ z, z ∈ anchors → z ∈ cover.flatten → False := by
    intro z hz hzO
    exact (hcovers z).mp hzO (hAS (Finset.mem_toList.mp hz))
  let B : List (Fin (2 * d + 3)) := stitch anchors cover
  have hBne : B ≠ [] := stitch_ne_nil anchors cover halign
  have hBn : B.Nodup := stitch_nodup anchors cover halign
    A.nodup_toList hdisjoint hAnchorCover
  have hBmem : ∀ z, z ∈ B ↔ z ∈ A ∨ z ∉ S := by
    intro z
    simpa only [B, anchors, Finset.mem_toList, hcovers z] using
      stitch_mem anchors cover halign z
  have hBhead : B.head? = anchors.head? := stitch_head? _ _
  have hBlast : B.getLast? = anchors.getLast? := stitch_getLast? _ _ halign
  have hBlastA : ∀ z, z ∈ B.getLast? → z ∈ A := by
    intro z hz
    rw [hBlast] at hz
    exact Finset.mem_toList.mp (List.mem_of_mem_getLast? hz)
  have hBchain : B.IsChain F.Adj := by
    apply stitch_chain F (C : Set (Fin (2 * d + 3)))
      ((S : Set (Fin (2 * d + 3)))ᶜ) anchors cover halign
    · intro a ha
      exact hAC (Finset.mem_toList.mp ha)
    · intro p hp
      refine ⟨hnonempty p hp, (hpaths p hp).imp (fun {_x _y} h => hGF h), ?_⟩
      intro x hx
      exact (hcovers x).mp (List.mem_flatten.mpr ⟨p, hp, hx⟩)
    · exact hfilled
  let R : Finset (Fin (2 * d + 3)) := S \ A
  have hRS : R ⊆ S := fun z hz => (Finset.mem_sdiff.mp hz).1
  have hBR : B.Disjoint R.toList := by
    rw [List.disjoint_left]
    intro z hzB hzR
    have hzR' := Finset.mem_sdiff.mp (Finset.mem_toList.mp hzR)
    rcases (hBmem z).mp hzB with hzA | hzO
    · exact hzR'.2 hzA
    · exact hzO hzR'.1
  have hRchain : R.toList.IsChain F.Adj := by
    apply List.Pairwise.isChain
    exact R.nodup_toList.pairwise_of_forall_ne
      (fun x hx y hy hxy => hGF (hclique
        (hRS (Finset.mem_toList.mp hx)) (hRS (Finset.mem_toList.mp hy)) hxy))
  let L : List (Fin (2 * d + 3)) := B ++ R.toList
  have hLn : L.Nodup := hBn.append R.nodup_toList hBR
  have hLchain : L.IsChain F.Adj := by
    apply hBchain.append hRchain
    intro x hx y hy
    have hxA : x ∈ A := hBlastA x hx
    have hyR : y ∈ R := Finset.mem_toList.mp (List.mem_of_mem_head? hy)
    have hxy : x ≠ y := by
      intro hxy
      exact (Finset.mem_sdiff.mp hyR).2 (hxy ▸ hxA)
    exact hGF (hclique (hAS hxA) (hRS hyR) hxy)
  have hLmem : ∀ z, z ∈ L := by
    intro z
    by_cases hzS : z ∈ S
    · by_cases hzA : z ∈ A
      · exact List.mem_append.mpr (Or.inl ((hBmem z).mpr (Or.inl hzA)))
      · exact List.mem_append.mpr (Or.inr (Finset.mem_toList.mpr
          (Finset.mem_sdiff.mpr ⟨hzS, hzA⟩)))
    · exact List.mem_append.mpr (Or.inl ((hBmem z).mpr (Or.inr hzS)))
  have hLfin : L.toFinset = Finset.univ := by
    ext z
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hLmem z
  have hLlength : L.length = 2 * d + 3 := by
    rw [← List.toFinset_card_of_nodup hLn, hLfin, Finset.card_univ,
      Fintype.card_fin]
  have hLne : L ≠ [] := by
    intro hnil
    simp only [hnil, List.length_nil] at hLlength
    omega
  have hheadS : L.head hLne ∈ S := by
    have hz : L.head hLne ∈ L.head? := List.head_mem_head? hLne
    have hh : L.head? = anchors.head? := by
      change (B ++ R.toList).head? = anchors.head?
      rw [List.head?_append_of_ne_nil _ hBne, hBhead]
    rw [hh] at hz
    exact hAS (Finset.mem_toList.mp (List.mem_of_mem_head? hz))
  have hlastS : L.getLast hLne ∈ S := by
    have hz : L.getLast hLne ∈ L.getLast? := List.getLast_mem_getLast? hLne
    by_cases hRnil : R.toList = []
    · have hh : L.getLast? = B.getLast? := by simp only [L, hRnil, List.append_nil]
      rw [hh] at hz
      exact hAS (hBlastA _ hz)
    · have hh : L.getLast? = R.toList.getLast? :=
        List.getLast?_append_of_ne_nil _ hRnil
      rw [hh] at hz
      exact hRS (Finset.mem_toList.mp (List.mem_of_mem_getLast? hz))
  have hendpoints : L.head hLne ≠ L.getLast hLne := by
    intro heq
    obtain ⟨x, hsingle⟩ := (List.Nodup.head_eq_getLast_iff hLne hLn).mp heq
    have hone : L.length = 1 := by simp only [hsingle, List.length_cons, List.length_nil]
    omega
  let P : F.Walk (L.head hLne) (L.getLast hLne) := Walk.ofSupport L hLne hLchain
  have hP : P.IsPath := by
    rw [Walk.isPath_def]
    simpa only [P, Walk.support_ofSupport] using hLn
  have hPlength : P.length = 2 * d + 2 := by
    simp only [P, Walk.length_ofSupport, hLlength]
    omega
  have hclose : F.Adj (L.getLast hLne) (L.head hLne) :=
    hGF (hclique hlastS hheadS hendpoints.symm)
  have hPtail : L.head hLne ∉ P.support.tail := by
    have hn := hP.support_nodup
    rw [← Walk.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hcycle : (P.append hclose.toWalk).IsCycle := by
    apply hP.isCycle_append hclose.isPath_toWalk
    · rw [List.disjoint_left]
      intro z hzP hzClose
      have hz : z = L.head hLne := by
        simpa only [SimpleGraph.Adj.support_toWalk, List.tail_cons,
          List.mem_singleton] using hzClose
      exact hPtail (hz ▸ hzP)
    · left
      omega
  apply (cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨L.head hLne, P.append hclose.toWalk, hcycle, ?_⟩
  simp only [Walk.length_append, SimpleGraph.Adj.length_toWalk, hPlength]

end ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105

namespace ErdosProblems.PathUpperReduction.EvenOutsiderEdgeCover1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105

/-- In the corrected d+3-core/d-outsider last block, an actual ORIGINAL
outsider edge and filled outsider/contact pairs force a spanning cycle in F.
The edge endpoints' distinctness follows from actual simple-graph adjacency. -/
theorem cycle_of_actual_outsider_edge {d : ℕ} (hd : 1 ≤ d)
    (G F : SimpleGraph (Fin (2 * d + 3))) (hGF : G ≤ F)
    (S C : Finset (Fin (2 * d + 3))) (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3)))) (hCS : C ⊆ S)
    (hCcard : C.card = d)
    (hfilled : ∀ x, x ∉ S → ∀ a, a ∈ C → F.Adj x a)
    (hedge : ∃ x y, x ∉ S ∧ y ∉ S ∧ G.Adj x y) :
    cycleGraph (2 * d + 3) ⊑ F := by
  classical
  obtain ⟨x, y, hxS, hyS, hxy⟩ := hedge
  have hne : x ≠ y := hxy.ne
  let O : Finset (Fin (2 * d + 3)) := Finset.univ \ S
  have hOcard : O.card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    change O.card + S.card = (Finset.univ : Finset (Fin (2 * d + 3))).card at hcard
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hcard
    omega
  have hxO : x ∈ O := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
  have hyO : y ∈ O := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩
  let R : Finset (Fin (2 * d + 3)) := (O.erase x).erase y
  have hxR : x ∉ R := by simp [R]
  have hyR : y ∉ R := by simp [R]
  have hRO : R ⊆ O := by
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have hyErase : y ∈ O.erase x := Finset.mem_erase.mpr ⟨hne.symm, hyO⟩
  have hRcard : R.card + 2 = d := by
    have hxcard := Finset.card_erase_add_one hxO
    have hycard := Finset.card_erase_add_one hyErase
    change R.card + 1 = (O.erase x).card at hycard
    omega
  let cover : List (List (Fin (2 * d + 3))) :=
    [x, y] :: R.toList.map (fun z => [z])
  have hflatten : cover.flatten = x :: y :: R.toList := by
    change [x, y] ++ (R.toList.map (fun z => [z])).flatten = x :: y :: R.toList
    rw [← List.flatMap_def, List.flatMap_singleton']
    rfl
  have hnonempty : ∀ p, p ∈ cover → p ≠ [] := by
    intro p hp
    rcases List.mem_cons.mp hp with hpair | hsingleton
    · subst p
      simp
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hsingleton
      simp
  have hpaths : ∀ p, p ∈ cover → p.IsChain G.Adj := by
    intro p hp
    rcases List.mem_cons.mp hp with hpair | hsingleton
    · subst p
      exact List.isChain_pair.mpr hxy
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hsingleton
      exact List.IsChain.singleton (R := G.Adj) z
  have hdisjoint : cover.flatten.Nodup := by
    rw [hflatten]
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, R.nodup_toList⟩⟩
    · simp only [List.mem_cons, not_or, Finset.mem_toList]
      exact ⟨hne, hxR⟩
    · simpa only [Finset.mem_toList] using hyR
  have hcovers : ∀ z, z ∈ cover.flatten ↔ z ∉ S := by
    intro z
    rw [hflatten]
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with hzx | hz
      · exact hzx.symm ▸ hxS
      · rcases List.mem_cons.mp hz with hzy | hzR
        · exact hzy.symm ▸ hyS
        · exact (Finset.mem_sdiff.mp (hRO (Finset.mem_toList.mp hzR))).2
    · intro hzS
      by_cases hzx : z = x
      · exact List.mem_cons.mpr (Or.inl hzx)
      by_cases hzy : z = y
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hzy)))
      have hzO : z ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩
      have hzR : z ∈ R := Finset.mem_erase.mpr
        ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hzO⟩⟩
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (Finset.mem_toList.mpr hzR))))
  have hcoverPlus : cover.length + 1 = d := by
    simp only [cover, List.length_cons, List.length_map, Finset.length_toList]
    omega
  have hcoverLength : cover.length = d - 1 := by omega
  have hcapacity : cover.length + 1 ≤ C.card := by
    rw [hcoverLength, hCcard]
    omega
  exact cycle_of_actual_outsider_path_cover hd G F hGF S C hScard
    hclique hCS cover hnonempty hpaths hdisjoint hcovers hcapacity hfilled

end ErdosProblems.PathUpperReduction.EvenOutsiderEdgeCover1105

section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination

namespace ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105

variable {V : Type*} [Fintype V]

/-- A complete exact forward-degree deletion order, represented by finite
induction rather than list indices. Its ONLY terminal carrier is S. Each
constructor removes one actual outsider; the head's degree is measured in
the same actual current carrier. The explicit classical erase keeps the
certificate independent of any externally supplied DecidableEq instance. -/
inductive ExactCoreDeletion (G : SimpleGraph V) (d : ℕ) (S : Finset V) :
    Finset V → Prop where
  | stop : ExactCoreDeletion G d S S
  | delete (T : Finset V) (x : V) (hx : x ∈ T) (hxS : x ∉ S)
      (hdegree : withinDegree G T x = d)
      (tail : ExactCoreDeletion G d S (@Finset.erase V (Classical.decEq V) T x)) :
      ExactCoreDeletion G d S T

/-- Every tight actual induced carrier has a complete exact deletion
certificate. The d<=|S| input normalizes the existing maximum in the generic
bound; the full nonempty-core caller below derives it internally. -/
theorem exact_core_deletion_of_tight_induced_count
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hdS : d ≤ S.card)
    (T : Finset V) (hST : S ⊆ T)
    (htight : (withinEdges G T).card =
      S.card.choose 2 + d * (T.card - S.card)) :
    ExactCoreDeletion G d S T := by
  classical
  have hmax : max d (degreeCore G d).card = S.card := by
    rw [hcore]
    exact max_eq_right hdS
  let P : Finset V → Prop := fun U => S ⊆ U →
    (withinEdges G U).card = S.card.choose 2 + d * (U.card - S.card) →
      ExactCoreDeletion G d S U
  have hP : ∀ U, P U := by
    intro U
    refine Finset.strongInductionOn U ?_
    intro U ih
    dsimp only [P]
    intro hSU hU
    by_cases hbase : U = S
    · subst U
      exact ExactCoreDeletion.stop
    · have hcard : S.card < U.card := by
        have hle : S.card ≤ U.card := Finset.card_le_card hSU
        by_contra hnot
        have hUS : U.card ≤ S.card := by omega
        have heq : S = U := Finset.eq_of_subset_of_card_le hSU hUS
        exact hbase heq.symm
      have hCU : degreeCore G d ⊆ U := by
        simpa only [hcore] using hSU
      have hlarge : max d (degreeCore G d).card < U.card := by
        simpa only [hmax] using hcard
      obtain ⟨x, hxU, hxC, hlow⟩ := outside_core_low_degree G d U hCU hlarge
      have hxS : x ∉ S := by simpa only [hcore] using hxC
      have hSerase : S ⊆ U.erase x := by
        intro z hzS
        apply Finset.mem_erase.mpr
        refine ⟨?_, hSU hzS⟩
        intro hzx
        exact hxS (hzx ▸ hzS)
      have hCerase : degreeCore G d ⊆ U.erase x := by
        simpa only [hcore] using hSerase
      have hMerase : max d (degreeCore G d).card ≤ (U.erase x).card := by
        rw [hmax]
        exact Finset.card_le_card hSerase
      have hbound := core_induced_edge_bound G d (U.erase x) hCerase hMerase
      rw [hmax] at hbound
      have hledger := withinEdges_erase_ledger G U x hxU
      have hcardErase : (U.erase x).card = U.card - 1 :=
        Finset.card_erase_of_mem hxU
      have hsteps : U.card - S.card = ((U.erase x).card - S.card) + 1 := by
        omega
      have hbudget : S.card.choose 2 + d * (U.card - S.card) =
          (S.card.choose 2 + d * ((U.erase x).card - S.card)) + d := by
        rw [hsteps, Nat.mul_add, Nat.mul_one]
        exact (Nat.add_assoc _ _ _).symm
      have heq : (withinEdges G (U.erase x)).card + withinDegree G U x =
          (S.card.choose 2 + d * ((U.erase x).card - S.card)) + d := by
        calc
          (withinEdges G (U.erase x)).card + withinDegree G U x =
              (withinEdges G U).card := hledger.symm
          _ = S.card.choose 2 + d * (U.card - S.card) := hU
          _ = (S.card.choose 2 + d * ((U.erase x).card - S.card)) + d := hbudget
      have hdegree : withinDegree G U x = d := by omega
      have htail : (withinEdges G (U.erase x)).card =
          S.card.choose 2 + d * ((U.erase x).card - S.card) := by omega
      have hcertificate : ExactCoreDeletion G d S (U.erase x) :=
        ih (U.erase x) (Finset.erase_ssubset hxU) hSerase htail
      exact ExactCoreDeletion.delete U x hxU hxS hdegree hcertificate
  exact hP T hST htight

/-- The original full-carrier endpoint: actual nonempty greatest core and
tight edge count imply an exact deletion order of ALL outsiders. No public
order or supplied d<=core-size hypothesis appears. The outside set may be
empty, in which case the certificate stops immediately at the actual core. -/
theorem exact_core_deletion_of_tight_nonempty_core
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hS : S.Nonempty)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card)) :
    ExactCoreDeletion G d S Finset.univ := by
  classical
  obtain ⟨x, hxS⟩ := hS
  have hgood : GoodCore G d S := by
    rw [← hcore]
    exact degree_core_good G d
  have hdegree : d < (S.filter (fun z => G.Adj x z)).card := hgood x hxS
  have hfilter : (S.filter (fun z => G.Adj x z)).card ≤ S.card := by
    apply Finset.card_le_card
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hdS : d ≤ S.card := by omega
  have hEdgesUniv : withinEdges G Finset.univ = G.edgeFinset := by
    ext e
    simp [withinEdges]
  have hfull : (withinEdges G Finset.univ).card =
      S.card.choose 2 + d * ((Finset.univ : Finset V).card - S.card) := by
    simpa only [hEdgesUniv, Finset.card_univ, Nat.card_eq_fintype_card,
      G.card_edgeSet] using htight
  exact exact_core_deletion_of_tight_induced_count G d S hcore hdS
    Finset.univ (Finset.subset_univ S) hfull

end ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105

end

section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105

namespace ErdosProblems.PathUpperReduction.LastTightCoreBlock1105

variable {V : Type*} [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

omit [Fintype V] in
theorem certificate_core_subset {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (h : ExactCoreDeletion G d S T) : S ⊆ T := by
  classical
  induction h with
  | stop => exact fun _ hx => hx
  | delete T x hx hxS hdegree tail ih =>
      intro z hz
      exact (Finset.mem_erase.mp (ih hz)).2

omit [Fintype V] in
theorem certificate_outsider_degree_ge {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (h : ExactCoreDeletion G d S T) :
    ∀ x ∈ T, x ∉ S → d ≤ withinDegree G T x := by
  classical
  induction h with
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

omit [Fintype V] in
/-- A complete exact deletion certificate with at least d actual outsiders
has an actual suffix carrier with exactly d outsiders. The suffix retains the
whole same core and a complete same-G certificate; every outsider has degree
at least d INSIDE this carrier, derived from the recorded forward degrees.
For d=0 the suffix is precisely S, so the degree assertion is vacuous. -/
theorem exists_last_tight_core_block (G : SimpleGraph V) (d : ℕ)
    (S T : Finset V) (hcertificate : ExactCoreDeletion G d S T)
    (houtside : d ≤ (T \ S).card) :
    ∃ U : Finset V, S ⊆ U ∧ U ⊆ T ∧ (U \ S).card = d ∧
      ExactCoreDeletion G d S U ∧
      ∀ x ∈ U, x ∉ S → d ≤ withinDegree G U x := by
  classical
  revert houtside
  induction hcertificate with
  | stop =>
      intro houtside
      have hd0 : d = 0 := by
        have hh : d ≤ 0 := by
          simpa only [Finset.sdiff_self, Finset.card_empty] using houtside
        omega
      refine ⟨S, (fun _ hx => hx), (fun _ hx => hx), ?_,
        ExactCoreDeletion.stop, ?_⟩
      · simp only [Finset.sdiff_self, Finset.card_empty, hd0]
      · exact certificate_outsider_degree_ge ExactCoreDeletion.stop
  | delete T x hx hxS hdegree tail ih =>
      intro houtside
      have hcurrent : ExactCoreDeletion G d S T :=
        ExactCoreDeletion.delete T x hx hxS hdegree tail
      by_cases hlast : (T \ S).card = d
      · exact ⟨T, certificate_core_subset hcurrent, (fun _ hz => hz), hlast,
          hcurrent, certificate_outsider_degree_ge hcurrent⟩
      · have hxOutside : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
        have hcount : ((T.erase x) \ S).card = (T \ S).card - 1 := by
          rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem hxOutside]
        have htailOutside : d ≤ ((T.erase x) \ S).card := by
          rw [hcount]
          omega
        obtain ⟨U, hSU, hUtail, hUcard, hUcertificate, hUdegree⟩ := ih htailOutside
        refine ⟨U, hSU, ?_, hUcard, hUcertificate, hUdegree⟩
        exact hUtail.trans (Finset.erase_subset x T)

/-- Full ambient actual-core caller. Tight original edge count and the actual
nonempty greatest d-core derive the COMPLETE certificate internally; the only
size premise is that the original ambient outside population is at least d.
All ambient vertices, including isolates, remain in Finset.univ. No order,
suffix, minimum degree or d<=|S| input is supplied by the caller. -/
theorem exists_last_tight_core_block_of_tight_nonempty_core
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hS : S.Nonempty)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card))
    (houtside : d ≤ Nat.card V - S.card) :
    ∃ U : Finset V, S ⊆ U ∧ U ⊆ Finset.univ ∧ (U \ S).card = d ∧
      ExactCoreDeletion G d S U ∧
      ∀ x ∈ U, x ∉ S → d ≤ withinDegree G U x := by
  classical
  have hcertificate : ExactCoreDeletion G d S Finset.univ :=
    exact_core_deletion_of_tight_nonempty_core G d S hcore hS htight
  have houtsideFinset : d ≤ ((Finset.univ : Finset V) \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
    simpa only [Nat.card_eq_fintype_card] using houtside
  exact exists_last_tight_core_block G d S Finset.univ hcertificate houtsideFinset

end ErdosProblems.PathUpperReduction.LastTightCoreBlock1105

end

noncomputable section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.LastTightCoreBlock1105

namespace ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105

variable {V : Type*} [Fintype V]

-- Internal classical instance only: no caller-supplied equality decision or
-- extra mathematical hypothesis is added to the public statements.
local instance : DecidableEq V := Classical.decEq V

/-- Every actual edge of the carrier that is not wholly inside S. This
includes BOTH cross edges and edges internal to the actual outsiders. -/
noncomputable def nonCoreEdges (G : SimpleGraph V) (S U : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact (withinEdges G U).filter (fun e => ¬ e.toFinset ⊆ S)

/-- Actual cross edges: among noncore edges, exclude those whose two
endpoints are both in the actual outsider carrier U\S. -/
noncomputable def coreCrossEdges (G : SimpleGraph V) (S U : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact (nonCoreEdges G S U).filter (fun e => ¬ e.toFinset ⊆ U \ S)

/-- A complete exact deletion certificate telescopes the actual undirected
edge ledger. No supplied intermediate edge equality or clique is required. -/
theorem certificate_edge_ledger {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (hcertificate : ExactCoreDeletion G d S T) :
    (withinEdges G T).card =
      (withinEdges G S).card + d * (T \ S).card := by
  classical
  induction hcertificate with
  | stop => simp only [Finset.sdiff_self, Finset.card_empty,
      Nat.mul_zero, Nat.add_zero]
  | delete T x hx hxS hdegree tail ih =>
      have hxOutside : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
      have hcount : (T \ S).card = ((T.erase x) \ S).card + 1 := by
        rw [Finset.erase_sdiff_comm]
        exact (Finset.card_erase_add_one hxOutside).symm
      calc
        (withinEdges G T).card =
            (withinEdges G (T.erase x)).card + withinDegree G T x :=
          withinEdges_erase_ledger G T x hx
        _ = ((withinEdges G S).card + d * ((T.erase x) \ S).card) + d := by
          rw [ih, hdegree]
        _ = (withinEdges G S).card + d * (((T.erase x) \ S).card + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        _ = (withinEdges G S).card + d * (T \ S).card := by rw [← hcount]

/-- For the actual last d outsiders the exact surplus above the actual core
edge count is d*d, even when the outsiders contain edges. -/
theorem last_block_edge_ledger {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    (withinEdges G U).card = (withinEdges G S).card + d * d := by
  rw [certificate_edge_ledger hcertificate, houtside]

theorem withinEdges_filter_core (G : SimpleGraph V) (S U : Finset V)
    (hSU : S ⊆ U) :
    letI : DecidableEq V := Classical.decEq V
    (withinEdges G U).filter (fun e => e.toFinset ⊆ S) = withinEdges G S := by
  classical
  unfold withinEdges
  ext e
  constructor
  · intro he
    obtain ⟨heU, heS⟩ := Finset.mem_filter.mp he
    obtain ⟨heG, _⟩ := Finset.mem_filter.mp heU
    exact Finset.mem_filter.mpr ⟨heG, heS⟩
  · intro he
    obtain ⟨heG, heS⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨heG, heS.trans hSU⟩, heS⟩

/-- The last block's actual cross plus internal-outside population has d*d
edges. Core containment is exactly the property returned by extraction. -/
theorem nonCoreEdges_card_of_last_block {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hSU : S ⊆ U)
    (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    (nonCoreEdges G S U).card = d * d := by
  classical
  have hpartition := (withinEdges G U).card_filter_add_card_filter_not
    (fun e => e.toFinset ⊆ S)
  rw [withinEdges_filter_core G S U hSU] at hpartition
  have hledger := last_block_edge_ledger hcertificate houtside
  unfold nonCoreEdges
  omega

theorem nonCoreEdges_filter_outside (G : SimpleGraph V)
    (S U : Finset V) :
    letI : DecidableEq V := Classical.decEq V
    (nonCoreEdges G S U).filter (fun e => e.toFinset ⊆ U \ S) =
      withinEdges G (U \ S) := by
  classical
  unfold nonCoreEdges withinEdges
  ext e
  constructor
  · intro he
    obtain ⟨heNonCore, heOutside⟩ := Finset.mem_filter.mp he
    obtain ⟨heU, _⟩ := Finset.mem_filter.mp heNonCore
    obtain ⟨heG, _⟩ := Finset.mem_filter.mp heU
    exact Finset.mem_filter.mpr ⟨heG, heOutside⟩
  · intro he
    obtain ⟨heG, heOutside⟩ := Finset.mem_filter.mp he
    have heU : e.toFinset ⊆ U := heOutside.trans Finset.sdiff_subset
    have heNotCore : ¬ e.toFinset ⊆ S := by
      intro heCore
      obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
      exact (Finset.mem_sdiff.mp (heOutside hz)).2 (heCore hz)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨heG, heU⟩, heNotCore⟩, heOutside⟩

/-- Exact even-rigidity input: actual cross edges plus actual edges among
the last d outsiders sum to d*d. An outsider edge consumes one unit of the
cross-edge budget; it is not forbidden by tightness alone. -/
theorem last_block_cross_edge_ledger {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hSU : S ⊆ U)
    (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    (coreCrossEdges G S U).card + (withinEdges G (U \ S)).card = d * d := by
  classical
  have hpartition := (nonCoreEdges G S U).card_filter_add_card_filter_not
    (fun e => e.toFinset ⊆ U \ S)
  rw [nonCoreEdges_filter_outside G S U] at hpartition
  have hcount := nonCoreEdges_card_of_last_block hSU hcertificate houtside
  unfold coreCrossEdges
  omega

/-- A concrete cross-edge lower constraint, retaining the exact possible
internal outsider edge capacity instead of assuming it is zero. -/
theorem last_block_core_cross_edges_lower {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hSU : S ⊆ U)
    (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    d * d ≤ (coreCrossEdges G S U).card + d.choose 2 := by
  have hledger := last_block_cross_edge_ledger hSU hcertificate houtside
  have hbound := withinEdges_card_le_choose G (U \ S)
  rw [houtside] at hbound
  calc
    d * d = (coreCrossEdges G S U).card + (withinEdges G (U \ S)).card :=
      hledger.symm
    _ ≤ (coreCrossEdges G S U).card + d.choose 2 := Nat.add_le_add_left hbound _

/-- Original full-host caller, strengthened by the derived suffix counts.
No suffix, ordering, degree/count oracle, clique, independence or equality
family is supplied. All original ambient vertices remain in univ. -/
theorem exists_last_tight_core_block_with_edge_ledger
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hS : S.Nonempty)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card))
    (houtside : d ≤ Nat.card V - S.card) :
    ∃ U : Finset V, S ⊆ U ∧ U ⊆ Finset.univ ∧ (U \ S).card = d ∧
      ExactCoreDeletion G d S U ∧
      (∀ x ∈ U, x ∉ S → d ≤ withinDegree G U x) ∧
      (withinEdges G U).card = (withinEdges G S).card + d * d ∧
      (coreCrossEdges G S U).card + (withinEdges G (U \ S)).card = d * d := by
  obtain ⟨U, hSU, hUuniv, hUoutside, hcertificate, hdegree⟩ :=
    exists_last_tight_core_block_of_tight_nonempty_core G d S
      hcore hS htight houtside
  exact ⟨U, hSU, hUuniv, hUoutside, hcertificate, hdegree,
    last_block_edge_ledger hcertificate hUoutside,
    last_block_cross_edge_ledger hSU hcertificate hUoutside⟩

end ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
end

namespace ErdosProblems.PathUpperReduction.EvenRestorationLedger1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105

/-- The old invariant derives exact ORIGINAL degree d in every actual
intermediate support retaining S. No outsider-degree oracle is supplied. -/
theorem old_outsider_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S C T : Finset V)
    (hST : S ⊆ T) (hCS : C ⊆ S) (hCcard : C.card = d)
    (hOld : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)))
    (A : Finset V) (hSA : S ⊆ A) (hAT : A ⊆ T)
    (y : V) (hyA : y ∈ A) (hyS : y ∉ S) :
    withinDegree G A y = d := by
  classical
  have hfilter : A.filter (fun z => G.Adj y z) = C := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzA, hyz⟩ := Finset.mem_filter.mp hz
      have hrel := (hOld y (hAT hyA) z (hAT hzA)).mp hyz
      rcases hrel.2 with hSS | hSC | hCS'
      · exact False.elim (hyS hSS.1)
      · exact hSC.2
      · exact False.elim (hyS (hCS hCS'.2))
    · intro hzC
      have hzS := hCS hzC
      have hyz : y ≠ z := by
        intro heq
        exact hyS (heq.symm ▸ hzS)
      apply Finset.mem_filter.mpr
      refine ⟨hSA hzS, ?_⟩
      apply (hOld y (hAT hyA) z (hST hzS)).mpr
      exact ⟨hyz, Or.inr (Or.inl ⟨hyS, hzC⟩)⟩
  change (A.filter (fun z => G.Adj y z)).card = d
  rw [hfilter, hCcard]

/-- Construct the COMPLETE old-support certificate internally from the
actual old join invariant. It terminates at the SAME S and G. -/
theorem old_join_exact_deletion {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S C T L : Finset V)
    (hST : S ⊆ T) (hCS : C ⊆ S) (hCcard : C.card = d)
    (hOld : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)))
    (hLO : letI : DecidableEq V := Classical.decEq V
      L ⊆ T \ S) :
    letI : DecidableEq V := Classical.decEq V
    ExactCoreDeletion G d S (S ∪ L) := by
  classical
  revert hLO
  refine Finset.induction_on L ?_ ?_
  · intro _hLO
    simpa only [Finset.union_empty] using
      (ExactCoreDeletion.stop : ExactCoreDeletion G d S S)
  · intro v R hvR ih hLO
    have hvO := hLO (Finset.mem_insert_self v R)
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hvO).2
    have hRO : R ⊆ T \ S := by
      intro z hzR
      exact hLO (Finset.mem_insert_of_mem hzR)
    have htailOld : ExactCoreDeletion G d S (S ∪ R) := ih hRO
    have hSU : S ⊆ S ∪ insert v R := Finset.subset_union_left
    have hUT : S ∪ insert v R ⊆ T := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzS | hzR
      · exact hST hzS
      · exact (Finset.mem_sdiff.mp (hLO hzR)).1
    have hvU : v ∈ S ∪ insert v R :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self v R))
    have hdegree : withinDegree G (S ∪ insert v R) v = d :=
      old_outsider_degree G d S C T hST hCS hCcard hOld
        (S ∪ insert v R) hSU hUT v hvU hvS
    have herase : (S ∪ insert v R).erase v = S ∪ R := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hvS,
        Finset.erase_insert hvR]
    have htail : ExactCoreDeletion G d S ((S ∪ insert v R).erase v) := by
      rw [herase]
      exact htailOld
    exact ExactCoreDeletion.delete (S ∪ insert v R) v hvU hvS hdegree htail

/-- The internally selected old outsider support and the actual restored
degree derive BOTH original edge populations. In particular the unordered
cross-plus-outside count is d²; possible new x-L edges are retained.
The actual selected support and its degree come from the separate support
adapter. Neither a certificate nor a count is a public premise here. -/
theorem restoration_edge_ledgers {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S C T L : Finset V) (x : V)
    (hd : 2 ≤ d) (hST : S ⊆ T) (hScard : S.card = d + 3)
    (hCS : C ⊆ S) (hCcard : C.card = d)
    (hOld : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)))
    (hx : x ∉ T)
    (hLO : letI : DecidableEq V := Classical.decEq V
      L ⊆ T \ S)
    (hLcard : L.card = d - 1)
    (hdegree : letI : DecidableEq V := Classical.decEq V
      withinDegree G (insert x (S ∪ L)) x = d) :
    letI : DecidableEq V := Classical.decEq V
    let W := insert x (S ∪ L)
    (withinEdges G W).card = (withinEdges G S).card + d * d ∧
      (coreCrossEdges G S W).card + (withinEdges G (W \ S)).card = d * d := by
  classical
  let W := insert x (S ∪ L)
  have hLT : L ⊆ T := by
    intro z hzL
    exact (Finset.mem_sdiff.mp (hLO hzL)).1
  have hxS : x ∉ S := fun hxS => hx (hST hxS)
  have hxSL : x ∉ S ∪ L := by
    intro hxSL
    rcases Finset.mem_union.mp hxSL with hxS' | hxL
    · exact hxS hxS'
    · exact hx (hLT hxL)
  have hSL : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro z hzS hzL
    exact (Finset.mem_sdiff.mp (hLO hzL)).2 hzS
  have hSW : S ⊆ W := by
    intro z hzS
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl hzS))
  have hWcard : W.card = 2 * d + 3 := by
    dsimp only [W]
    rw [Finset.card_insert_of_notMem hxSL, Finset.card_union_of_disjoint hSL,
      hScard, hLcard]
    omega
  have hWoutside : (W \ S).card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card hSW
    rw [hScard, hWcard] at hcard
    omega
  have hOldCertificate : ExactCoreDeletion G d S (S ∪ L) :=
    old_join_exact_deletion G d S C T L hST hCS hCcard hOld hLO
  have herase : W.erase x = S ∪ L := Finset.erase_insert hxSL
  have htail : ExactCoreDeletion G d S (W.erase x) := by
    rw [herase]
    exact hOldCertificate
  have hcertificate : ExactCoreDeletion G d S W :=
    ExactCoreDeletion.delete W x (Finset.mem_insert_self x (S ∪ L))
      hxS hdegree htail
  exact ⟨last_block_edge_ledger hcertificate hWoutside,
    last_block_cross_edge_ledger hSW hcertificate hWoutside⟩

end ErdosProblems.PathUpperReduction.EvenRestorationLedger1105

namespace ErdosProblems.PathUpperReduction.EvenRestorationSupport1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

/-- Internally select d-1 actual later outsiders containing ALL original
outside neighbors of x. Together with the original core and x they form an
actual carrier of size 2d+3 retaining x's exact original degree d.
No clique, cycle-freedom, old classification or edge ledger is assumed. -/
theorem exists_actual_restoration_support {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S T : Finset V) (x a : V)
    (hd : 2 ≤ d) (hST : S ⊆ T) (hScard : S.card = d + 3)
    (houtside : letI : DecidableEq V := Classical.decEq V
      d ≤ (T \ S).card)
    (hx : x ∉ T) (ha : a ∈ S) (hxa : G.Adj x a)
    (hdegree : letI : DecidableEq V := Classical.decEq V
      withinDegree G (insert x T) x = d) :
    letI : DecidableEq V := Classical.decEq V
    ∃ L : Finset V, L ⊆ T \ S ∧ L.card = d - 1 ∧
      (∀ y ∈ T \ S, G.Adj x y → y ∈ L) ∧
      (∀ y ∈ insert x T, G.Adj x y → y ∈ insert x (S ∪ L)) ∧
      (insert x (S ∪ L)).card = 2 * d + 3 ∧
      withinDegree G (insert x (S ∪ L)) x = d := by
  classical
  let O := T \ S
  let R := O.filter (fun y => G.Adj x y)
  let N := (insert x T).filter (fun y => G.Adj x y)
  have hOcard : d ≤ O.card := houtside
  have hRO : R ⊆ O := Finset.filter_subset _ _
  have haR : a ∉ R := by
    intro haR
    have haO : a ∈ O := (Finset.mem_filter.mp haR).1
    exact (Finset.mem_sdiff.mp haO).2 ha
  have hsub : insert a R ⊆ N := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hya | hyR
    · subst y
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (hST ha), hxa⟩
    · obtain ⟨hyO, hxy⟩ := Finset.mem_filter.mp hyR
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hyO).1, hxy⟩
  have hNcard : N.card = d := by
    change ((insert x T).filter (fun y => G.Adj x y)).card = d at hdegree
    exact hdegree
  have hRcard : R.card ≤ d - 1 := by
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem haR, hNcard] at hcard
    omega
  obtain ⟨L, hRL, hLO, hLcard⟩ :=
    Finset.exists_subsuperset_card_eq hRO hRcard (by omega : d - 1 ≤ O.card)
  have hLT : L ⊆ T := by
    intro y hyL
    exact (Finset.mem_sdiff.mp (hLO hyL)).1
  have hSL : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro y hyS hyL
    exact (Finset.mem_sdiff.mp (hLO hyL)).2 hyS
  have hxSL : x ∉ S ∪ L := by
    intro hxSL
    rcases Finset.mem_union.mp hxSL with hxS | hxL
    · exact hx (hST hxS)
    · exact hx (hLT hxL)
  let W := insert x (S ∪ L)
  have hWsub : W ⊆ insert x T := by
    intro y hyW
    rcases Finset.mem_insert.mp hyW with hyx | hySL
    · exact Finset.mem_insert.mpr (Or.inl hyx)
    · rcases Finset.mem_union.mp hySL with hyS | hyL
      · exact Finset.mem_insert_of_mem (hST hyS)
      · exact Finset.mem_insert_of_mem (hLT hyL)
  have hretain : ∀ y ∈ insert x T, G.Adj x y → y ∈ W := by
    intro y hy hxy
    have hyT : y ∈ T := by
      rcases Finset.mem_insert.mp hy with hyx | hyT
      · exact False.elim (G.ne_of_adj hxy hyx.symm)
      · exact hyT
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · apply Or.inr
      apply hRL
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyT, hyS⟩, hxy⟩
  have hWcard : W.card = 2 * d + 3 := by
    dsimp only [W]
    rw [Finset.card_insert_of_notMem hxSL, Finset.card_union_of_disjoint hSL,
      hScard, hLcard]
    omega
  have hfilter : (insert x T).filter (fun y => G.Adj x y) =
      W.filter (fun y => G.Adj x y) := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨hyT, hxy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hretain y hyT hxy, hxy⟩
    · intro y hy
      obtain ⟨hyW, hxy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hWsub hyW, hxy⟩
  have hWdegree : withinDegree G W x = d := by
    change (W.filter (fun y => G.Adj x y)).card = d
    rw [← hfilter]
    exact hNcard
  refine ⟨L, hLO, hLcard, ?_, hretain, hWcard, hWdegree⟩
  intro y hyO hxy
  exact hRL (Finset.mem_filter.mpr ⟨hyO, hxy⟩)

end ErdosProblems.PathUpperReduction.EvenRestorationSupport1105

section

namespace ErdosProblems.PathThirteenBridgeEquality

open SimpleGraph
open scoped BigOperators

/-- In the three actual parts obtained from deleting a bridge, density forces
the ten-vertex core, one pendant vertex and the two-vertex outside part.
The outside part may initially contain several components. -/
theorem three_cut_cardinalities
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c)
    (hcomponent : 9 ≤ a + b) (hsum : a + b + c = 13)
    (hdense : 47 ≤ a.choose 2 + b.choose 2 + c.choose 2 + 1) :
    c = 2 ∧ ((a = 1 ∧ b = 10) ∨ (a = 10 ∧ b = 1)) := by
  let x := a - 1
  let y := b - 1
  have hax : a = x + 1 := by dsimp [x]; omega
  have hby : b = y + 1 := by dsimp [y]; omega
  have hx : (x + 1) * x = (x + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq x 1
  have hy : (y + 1) * y = (y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq y 1
  rw [hax, hby] at hsum hcomponent hdense
  have hcupper : c ≤ 4 := by omega
  have hc2 : c = 2 := by
    by_contra hne
    have hcases : c = 3 ∨ c = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hdense
      nlinarith [Nat.zero_le (x * y)]
    · change 47 ≤ (x + 1).choose 2 + (y + 1).choose 2 + 6 + 1 at hdense
      nlinarith [Nat.zero_le (x * y)]
  subst c
  norm_num at hdense
  have hxy : x * y = 0 := by nlinarith [Nat.zero_le (x * y)]
  refine ⟨rfl, ?_⟩
  rcases Nat.mul_eq_zero.mp hxy with hx0 | hy0
  · left
    omega
  · right
    omega

/-- Equality in the complete-graph edge cap forces the actual graph to be
complete. This is applied to each actual induced part, without relabeling. -/
theorem eq_top_of_card_edgeFinset_eq_choose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : G.edgeFinset.card = (Fintype.card V).choose 2) : G = ⊤ := by
  classical
  apply SimpleGraph.edgeFinset_inj.mp
  apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  exact hcard.ge

/-- Forty-seven selected edges force a vertex whose actual component has
at least nine vertices. Global maximality then gives this size to the
chosen largest component. -/
theorem exists_degree_eight_of_edges_forty_seven
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (hdense : 47 ≤ G.edgeFinset.card) : ∃ v, 8 ≤ G.degree v := by
  by_contra h
  push Not at h
  have hsum : (∑ v : Fin 13, G.degree v) ≤ ∑ _v : Fin 13, 7 := by
    apply Finset.sum_le_sum
    intro v _hv
    exact Nat.le_of_lt_succ (h v)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  norm_num at hsum
  omega

/-- Once the actual bridge cut has sizes one, ten and two, its total edge
cap forces both nontrivial induced parts to be complete. -/
theorem actual_parts_complete_of_bridge_cap
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (S T U : Finset (Fin 13)) (hS : S.card = 1) (hT : T.card = 10)
    (hU : U.card = 2) (hdense : 47 ≤ G.edgeFinset.card)
    (hcap : G.edgeFinset.card ≤
      (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1) :
    G.edgeFinset.card = 47 ∧
      G.induce (↑T : Set (Fin 13)) = ⊤ ∧
      G.induce (↑U : Set (Fin 13)) = ⊤ := by
  classical
  have hScap : (G.induce (↑S : Set (Fin 13))).edgeFinset.card ≤ S.card.choose 2 := by
    calc
      _ ≤ (Fintype.card S).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hTcap : (G.induce (↑T : Set (Fin 13))).edgeFinset.card ≤ T.card.choose 2 := by
    calc
      _ ≤ (Fintype.card T).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hUcap : (G.induce (↑U : Set (Fin 13))).edgeFinset.card ≤ U.card.choose 2 := by
    calc
      _ ≤ (Fintype.card U).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = U.card.choose 2 := by rw [Fintype.card_coe]
  rw [hS] at hScap
  rw [hT] at hTcap
  rw [hU] at hUcap
  change (G.induce (↑S : Set (Fin 13))).edgeFinset.card ≤ 0 at hScap
  change (G.induce (↑T : Set (Fin 13))).edgeFinset.card ≤ 45 at hTcap
  change (G.induce (↑U : Set (Fin 13))).edgeFinset.card ≤ 1 at hUcap
  refine ⟨by omega, ?_, ?_⟩
  · apply eq_top_of_card_edgeFinset_eq_choose
    change (G.induce (↑T : Set (Fin 13))).edgeFinset.card = (Fintype.card T).choose 2
    rw [Fintype.card_coe, hT]
    change (G.induce (↑T : Set (Fin 13))).edgeFinset.card = 45
    omega
  · apply eq_top_of_card_edgeFinset_eq_choose
    change (G.induce (↑U : Set (Fin 13))).edgeFinset.card = (Fintype.card U).choose 2
    rw [Fintype.card_coe, hU]
    change (G.induce (↑U : Set (Fin 13))).edgeFinset.card = 1
    omega

end ErdosProblems.PathThirteenBridgeEquality

namespace ErdosProblems.Fin13ActualBridgeCut

open SimpleGraph
open scoped Classical

/-- The deletion cut of an actual bridge, retaining its ORIGINAL component.
Disconnectedness, minimum degree and component size occur only in the two
conditional consequences; they are not substituted by a favorable cut. -/
theorem actual_bridge_cut_certificate
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (a b : Fin 13) (hab : G.Adj a b) (hbridge : G.IsBridge s(a, b)) :
    let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
    let S := Finset.univ.filter (fun x => D.Reachable a x)
    let T := Finset.univ.filter (fun x => D.Reachable b x)
    let U := Finset.univ \ (S ∪ T)
    Disjoint S T ∧ Disjoint (S ∪ T) U ∧
    (S ∪ T) ∪ U = Finset.univ ∧ a ∈ S ∧ b ∈ T ∧
    S.card + T.card + U.card = 13 ∧
    (∀ x y, G.Adj x y →
      s(x, y) = s(a, b) ∨ (x ∈ S ∧ y ∈ S) ∨
      (x ∈ T ∧ y ∈ T) ∨ (x ∈ U ∧ y ∈ U)) ∧
    S ∪ T = Finset.univ.filter (fun x => G.Reachable a x) ∧
    (¬ G.Connected → (∀ x, 1 ≤ G.degree x) → 2 ≤ U.card) ∧
    (9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card →
      9 ≤ S.card + T.card) ∧
    G.edgeFinset.card ≤ (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 ∧
    G.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 + 1 := by
  classical
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
  let S : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable b x)
  let U : Finset (Fin 13) := Finset.univ \ (S ∪ T)
  change Disjoint S T ∧ Disjoint (S ∪ T) U ∧
    (S ∪ T) ∪ U = Finset.univ ∧ a ∈ S ∧ b ∈ T ∧
    S.card + T.card + U.card = 13 ∧
    (∀ x y, G.Adj x y →
      s(x, y) = s(a, b) ∨ (x ∈ S ∧ y ∈ S) ∨
      (x ∈ T ∧ y ∈ T) ∨ (x ∈ U ∧ y ∈ U)) ∧
    S ∪ T = Finset.univ.filter (fun x => G.Reachable a x) ∧
    (¬ G.Connected → (∀ x, 1 ≤ G.degree x) → 2 ≤ U.card) ∧
    (9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card →
      9 ≤ S.card + T.card) ∧
    G.edgeFinset.card ≤ (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 ∧
    G.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 + 1
  have hle : D ≤ G := G.deleteEdges_le _
  have hsep : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  have hS (x : Fin 13) : x ∈ S ↔ D.Reachable a x := by simp [S]
  have hT (x : Fin 13) : x ∈ T ↔ D.Reachable b x := by simp [T]
  have hU (x : Fin 13) : x ∈ U ↔ x ∉ S ∧ x ∉ T := by simp [U]
  have haS : a ∈ S := (hS a).mpr (SimpleGraph.Reachable.refl _)
  have hbT : b ∈ T := (hT b).mpr (SimpleGraph.Reachable.refl _)
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact hsep (((hS x).mp hxS).trans ((hT x).mp hxT).symm)
  have hSTU : Disjoint (S ∪ T) U := Finset.disjoint_sdiff
  have hparts : (S ∪ T) ∪ U = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsum : S.card + T.card + U.card = 13 := by
    calc
      S.card + T.card + U.card = (S ∪ T).card + U.card := by
        rw [Finset.card_union_of_disjoint hST]
      _ = ((S ∪ T) ∪ U).card := (Finset.card_union_of_disjoint hSTU).symm
      _ = 13 := by simp only [hparts, Finset.card_univ, Fintype.card_fin]
  have hSclosed : ∀ {x y : Fin 13}, D.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    exact (hS y).mpr (((hS x).mp hx).trans hxy.reachable)
  have hTclosed : ∀ {x y : Fin 13}, D.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    exact (hT y).mpr (((hT x).mp hx).trans hxy.reachable)
  have hUclosed : ∀ {x y : Fin 13}, D.Adj x y → x ∈ U → y ∈ U := by
    intro x y hxy hx
    obtain ⟨hxS, hxT⟩ := (hU x).mp hx
    apply (hU y).mpr
    constructor
    · intro hyS
      exact hxS (hSclosed hxy.symm hyS)
    · intro hyT
      exact hxT (hTclosed hxy.symm hyT)
  have hdeleteAdj {x y : Fin 13} (hxy : G.Adj x y)
      (hne : s(x, y) ≠ s(a, b)) : D.Adj x y := by
    change (G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))).Adj x y
    apply SimpleGraph.deleteEdges_adj.mpr
    exact ⟨hxy, by simpa only [Set.mem_singleton_iff] using hne⟩
  have hclosed : ∀ {x y : Fin 13}, G.Adj x y → x ∈ S ∪ T → y ∈ S ∪ T := by
    intro x y hxy hx
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Finset.mem_union.mpr (Or.inr hbT)
      · exact Finset.mem_union.mpr (Or.inl haS)
    · have hxyD := hdeleteAdj hxy he
      rcases Finset.mem_union.mp hx with hxS | hxT
      · exact Finset.mem_union.mpr (Or.inl (hSclosed hxyD hxS))
      · exact Finset.mem_union.mpr (Or.inr (hTclosed hxyD hxT))
  have hcomponent (x : Fin 13) : x ∈ S ∪ T ↔ G.Reachable a x := by
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxS | hxT
      · exact SimpleGraph.Reachable.mono hle ((hS x).mp hxS)
      · exact hab.reachable.trans (SimpleGraph.Reachable.mono hle ((hT x).mp hxT))
    · intro hx
      have hrt := (G.reachable_iff_reflTransGen a x).mp hx
      induction hrt with
      | refl => exact Finset.mem_union.mpr (Or.inl haS)
      | tail hprev hxy ih =>
          exact hclosed hxy (ih ((G.reachable_iff_reflTransGen a _).mpr hprev))
  have hcomponentSet : S ∪ T = Finset.univ.filter (fun x => G.Reachable a x) := by
    ext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcomponent x
  have hUoriginal (x : Fin 13) : x ∈ U ↔ ¬ G.Reachable a x := by
    rw [← hcomponent x]
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and]
  have hUoriginalClosed : ∀ {x y : Fin 13}, G.Adj x y → x ∈ U → y ∈ U := by
    intro x y hxy hx
    apply (hUoriginal y).mpr
    intro hy
    exact (hUoriginal x).mp hx (hy.trans hxy.symm.reachable)
  have hUtwo : ¬ G.Connected → (∀ x, 1 ≤ G.degree x) → 2 ≤ U.card := by
    intro hdis hdegree
    have hzexists : ∃ z : Fin 13, ¬ G.Reachable a z := by
      by_contra hz
      apply hdis
      apply (G.connected_iff_exists_forall_reachable).mpr
      refine ⟨a, ?_⟩
      intro z
      by_contra haz
      exact hz ⟨z, haz⟩
    obtain ⟨z, haz⟩ := hzexists
    have hzU : z ∈ U := (hUoriginal z).mpr haz
    have hzpos : 0 < G.degree z := by have := hdegree z; omega
    obtain ⟨y, hzy⟩ := (G.degree_pos_iff_exists_adj z).mp hzpos
    have hyU : y ∈ U := hUoriginalClosed hzy hzU
    have hpair : ({z, y} : Finset (Fin 13)) ⊆ U := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzU
      · exact hyU
    calc
      2 = ({z, y} : Finset (Fin 13)).card := by simp [hzy.ne]
      _ ≤ U.card := Finset.card_le_card hpair
  have hlarge : 9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card →
      9 ≤ S.card + T.card := by
    intro hbig
    rw [← hcomponentSet, Finset.card_union_of_disjoint hST] at hbig
    exact hbig
  have hedgeClass : ∀ x y, G.Adj x y →
      s(x, y) = s(a, b) ∨ (x ∈ S ∧ y ∈ S) ∨
      (x ∈ T ∧ y ∈ T) ∨ (x ∈ U ∧ y ∈ U) := by
    intro x y hxy
    by_cases he : s(x, y) = s(a, b)
    · exact Or.inl he
    · have hxyD := hdeleteAdj hxy he
      apply Or.inr
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hxS, hSclosed hxyD hxS⟩
      · apply Or.inr
        by_cases hxT : x ∈ T
        · exact Or.inl ⟨hxT, hTclosed hxyD hxT⟩
        · have hxU := (hU x).mpr ⟨hxS, hxT⟩
          exact Or.inr ⟨hxU, hUclosed hxyD hxU⟩
  let ES := D.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := D.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  let EU := D.edgeFinset.filter (fun e => e.toFinset ⊆ U)
  have hcover : D.edgeFinset ⊆ (ES ∪ ET) ∪ EU := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : D.Adj x y := D.mem_edgeSet.mp (D.mem_edgeFinset.mp he)
    by_cases hxS : x ∈ S
    · have hsub : s(x, y).toFinset ⊆ S := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxS (hSclosed hxy hxS)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨he, hsub⟩))))
    · by_cases hxT : x ∈ T
      · have hsub : s(x, y).toFinset ⊆ T := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxT (hTclosed hxy hxT)
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))))
      · have hxU := (hU x).mpr ⟨hxS, hxT⟩
        have hsub : s(x, y).toFinset ⊆ U := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxU (hUclosed hxy hxU)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))
  have hES : ES.card ≤ S.card.choose 2 := by
    calc
      ES.card = (D.induce (↑S : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) S
      _ ≤ (Fintype.card S).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑S : Set (Fin 13)))
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hET : ET.card ≤ T.card.choose 2 := by
    calc
      ET.card = (D.induce (↑T : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) T
      _ ≤ (Fintype.card T).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑T : Set (Fin 13)))
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hEU : EU.card ≤ U.card.choose 2 := by
    calc
      EU.card = (D.induce (↑U : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) U
      _ ≤ (Fintype.card U).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑U : Set (Fin 13)))
      _ = U.card.choose 2 := by rw [Fintype.card_coe]
  have hDcount : D.edgeFinset.card ≤ ES.card + ET.card + EU.card := by
    calc
      D.edgeFinset.card ≤ ((ES ∪ ET) ∪ EU).card := Finset.card_le_card hcover
      _ ≤ (ES ∪ ET).card + EU.card := Finset.card_union_le (ES ∪ ET) EU
      _ ≤ ES.card + ET.card + EU.card :=
        Nat.add_le_add_right (Finset.card_union_le ES ET) EU.card
  have hDcap : D.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 := by
    omega
  have hpartCount (P : Finset (Fin 13)) :
      (D.edgeFinset.filter (fun e => e.toFinset ⊆ P)).card ≤
      (G.induce (↑P : Set (Fin 13))).edgeFinset.card := by
    calc
      (D.edgeFinset.filter (fun e => e.toFinset ⊆ P)).card ≤
          (G.edgeFinset.filter (fun e => e.toFinset ⊆ P)).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨heD, hsub⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono hle heD, hsub⟩
      _ = (G.induce (↑P : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G) P
  have hdelete : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, Finset.coe_erase, D, SimpleGraph.edgeSet_deleteEdges]
  have hedge : D.edgeFinset.card + 1 = G.edgeFinset.card := by
    rw [hdelete]
    exact Finset.card_erase_add_one (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hab))
  have hGcap : G.edgeFinset.card ≤
      S.card.choose 2 + T.card.choose 2 + U.card.choose 2 + 1 := by omega
  have hSCount : ES.card ≤ (G.induce (↑S : Set (Fin 13))).edgeFinset.card := hpartCount S
  have hTCount : ET.card ≤ (G.induce (↑T : Set (Fin 13))).edgeFinset.card := hpartCount T
  have hUCount : EU.card ≤ (G.induce (↑U : Set (Fin 13))).edgeFinset.card := hpartCount U
  have hGCount : G.edgeFinset.card ≤
      (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 := by omega
  exact ⟨hST, hSTU, hparts, haS, hbT, hsum, hedgeClass,
    hcomponentSet, hUtwo, hlarge, hGCount, hGcap⟩

end ErdosProblems.Fin13ActualBridgeCut

namespace ErdosProblems.PathThirteenBridgeEquality

open scoped Classical

/-- Exact actual deletion parts in the sole dense disconnected bridge case.
This is the ordinary structural seam in the original Fin13 coloring proof;
the original-color exchange remains to be composed. -/
theorem dense_actual_bridge_exception_shape
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (hdis : ¬ G.Connected) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdense : 47 ≤ G.edgeFinset.card)
    (a b : Fin 13) (hab : G.Adj a b) (hbridge : G.IsBridge s(a, b))
    (hlarge : 9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card) :
    let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
    let S := Finset.univ.filter (fun x => D.Reachable a x)
    let T := Finset.univ.filter (fun x => D.Reachable b x)
    let U := Finset.univ \ (S ∪ T)
    G.edgeFinset.card = 47 ∧ U.card = 2 ∧
      ((S.card = 1 ∧ T.card = 10 ∧ G.induce (↑T : Set (Fin 13)) = ⊤) ∨
       (S.card = 10 ∧ T.card = 1 ∧ G.induce (↑S : Set (Fin 13)) = ⊤)) ∧
      G.induce (↑U : Set (Fin 13)) = ⊤ := by
  classical
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
  let S : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable b x)
  let U : Finset (Fin 13) := Finset.univ \ (S ∪ T)
  obtain ⟨_hST, _hSTU, _hparts, haS, hbT, hsum, _hclass,
      _hcomponent, hUtwo, hbig, hcount, hchoose⟩ :=
    ErdosProblems.Fin13ActualBridgeCut.actual_bridge_cut_certificate G a b hab hbridge
  change G.edgeFinset.card ≤
    (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
    (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
    (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 at hcount
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨b, hbT⟩
  have hUtwo' : 2 ≤ U.card := hUtwo hdis hmin
  obtain ⟨hU, hsize⟩ := three_cut_cardinalities S.card T.card U.card
    hSpos hTpos hUtwo' (hbig hlarge) hsum (hdense.trans hchoose)
  rcases hsize with ⟨hS, hT⟩ | ⟨hS, hT⟩
  · obtain ⟨heq, hcore, hout⟩ :=
      actual_parts_complete_of_bridge_cap G S T U hS hT hU hdense hcount
    exact ⟨heq, hU, Or.inl ⟨hS, hT, hcore⟩, hout⟩
  · have hcount' : G.edgeFinset.card ≤
        (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
        (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
        (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 := by omega
    obtain ⟨heq, hcore, hout⟩ :=
      actual_parts_complete_of_bridge_cap G T S U hT hS hU hdense hcount'
    exact ⟨heq, hU, Or.inr ⟨hS, hT, hcore⟩, hout⟩

end ErdosProblems.PathThirteenBridgeEquality

end

noncomputable section
namespace ErdosProblems.PathUpperReduction.H3ResidualCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

omit [Fintype V] in
theorem withinDegree_le_card_sub_one (G : SimpleGraph V)
    (K : Finset V) (x : V) (hx : x ∈ K) :
    withinDegree G K x ≤ K.card - 1 := by
  classical
  have hsub : K.filter (fun z => G.Adj x z) ⊆ K.erase x := by
    intro z hz
    obtain ⟨hzK, hxz⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_erase.mpr ⟨?_, hzK⟩
    exact hxz.ne.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hx] at hcard
  exact hcard

/-- Erasing the ACTUAL arbitrary W counts each removed ORIGINAL edge once.
The residual edges remain untouched; all W-internal and W-to-residual edges
are bounded by the complete capacities without assuming they are present. -/
theorem original_seed_edge_partition_upper (G : SimpleGraph V)
    (K W : Finset V) (hWK : W ⊆ K) :
    (withinEdges G K).card ≤ W.card.choose 2 +
      W.card * (K \ W).card + (withinEdges G (K \ W)).card := by
  classical
  revert K
  induction W using Finset.induction_on with
  | empty =>
      intro K _hWK
      simp
  | @insert x W hx ih =>
      intro K hWK
      have hxK : x ∈ K := hWK (Finset.mem_insert_self x W)
      have hWErase : W ⊆ K.erase x := by
        intro z hzW
        refine Finset.mem_erase.mpr ⟨?_, hWK (Finset.mem_insert_of_mem hzW)⟩
        intro hzx
        exact hx (hzx ▸ hzW)
      have hresidual : K.erase x \ W = K \ insert x W := by
        rw [Finset.erase_sdiff_comm, Finset.sdiff_insert]
      have hprevious := ih (K.erase x) hWErase
      rw [hresidual] at hprevious
      have hnewcard : (insert x W).card = W.card + 1 :=
        Finset.card_insert_of_notMem hx
      have hcardledger := Finset.card_sdiff_add_card_eq_card hWK
      have hdegree := withinDegree_le_card_sub_one G K x hxK
      have hdegreeCapacity : withinDegree G K x ≤
          (K \ insert x W).card + W.card := by
        omega
      have hchoose : (W.card + 1).choose 2 = W.card + W.card.choose 2 := by
        simpa only [Nat.choose_one_right] using (Nat.choose_succ_succ' W.card 1)
      calc
        (withinEdges G K).card =
            (withinEdges G (K.erase x)).card + withinDegree G K x :=
          withinEdges_erase_ledger G K x hxK
        _ ≤ (W.card.choose 2 + W.card * (K \ insert x W).card +
            (withinEdges G (K \ insert x W)).card) +
            ((K \ insert x W).card + W.card) :=
          Nat.add_le_add hprevious hdegreeCapacity
        _ = (W.card + 1).choose 2 + (W.card + 1) * (K \ insert x W).card +
            (withinEdges G (K \ insert x W)).card := by
          rw [hchoose, Nat.add_mul, Nat.one_mul]
          omega
        _ = (insert x W).card.choose 2 +
            (insert x W).card * (K \ insert x W).card +
            (withinEdges G (K \ insert x W)).card := by rw [hnewcard]

/-- In the literal h3 cardinalities, the ACTUAL residual has four vertices
and its original edges are the only unbounded term in the seed partition. -/
theorem h3_original_seed_edge_partition_upper (G : SimpleGraph V)
    (d : ℕ) (K W : Finset V) (hd : 4 ≤ d)
    (hKcard : K.card = d + 3) (hWcard : W.card = d - 1) (hWK : W ⊆ K) :
    (K \ W).card = 4 ∧
      (withinEdges G K).card ≤ (d - 1).choose 2 +
        4 * (d - 1) + (withinEdges G (K \ W)).card := by
  have hcardledger := Finset.card_sdiff_add_card_eq_card hWK
  have hRcard : (K \ W).card = 4 := by omega
  refine ⟨hRcard, ?_⟩
  have hbound := original_seed_edge_partition_upper G K W hWK
  simpa only [hWcard, hRcard, Nat.mul_comm] using hbound

/-- EXACT zero-deficit Q_d(d+3) forces at least three ORIGINAL residual
edges; the two-disjoint-K2 control has at most Q-1 seed edges. -/
theorem h3_residual_edges_ge_three_of_exact_seed_count (G : SimpleGraph V)
    (d : ℕ) (K W : Finset V) (hd : 4 ≤ d)
    (hKcard : K.card = d + 3) (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hQ : (withinEdges G K).card = d.choose 2 + 3 * d) :
    (K \ W).card = 4 ∧ 3 ≤ (withinEdges G (K \ W)).card := by
  obtain ⟨hRcard, hbound⟩ :=
    h3_original_seed_edge_partition_upper G d K W hd hKcard hWcard hWK
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using (Nat.choose_succ_succ' (d - 1) 1)
  have hcapacity : d.choose 2 + 3 * d =
      (d - 1).choose 2 + 4 * (d - 1) + 3 := by
    rw [hchoose]
    omega
  rw [hQ, hcapacity] at hbound
  exact ⟨hRcard, by omega⟩

omit [Fintype V] in
/-- Original K-minimum degree≥d and at most d-1 removed vertices give
residual minimum degree≥1. No edge count or residual connectivity is assumed. -/
theorem h3_residual_min_degree_of_original_seed_degree (G : SimpleGraph V)
    (d : ℕ) (K W : Finset V) (hd : 4 ≤ d) (hWcard : W.card = d - 1)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x) :
    ∀ x ∈ K \ W, 1 ≤ withinDegree G (K \ W) x := by
  classical
  intro x hxR
  have hxK : x ∈ K := (Finset.mem_sdiff.mp hxR).1
  have hsub : K.filter (fun z => G.Adj x z) ⊆
      ((K \ W).filter (fun z => G.Adj x z)) ∪ W := by
    intro z hz
    obtain ⟨hzK, hxz⟩ := Finset.mem_filter.mp hz
    by_cases hzW : z ∈ W
    · exact Finset.mem_union.mpr (Or.inr hzW)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hzK, hzW⟩, hxz⟩))
  have hdegreeLoss : withinDegree G K x ≤ withinDegree G (K \ W) x + W.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdegree := hseed x hxK
  omega

end ErdosProblems.PathUpperReduction.H3ResidualCount1105
end

namespace ErdosProblems.PathUpperReduction.H3ResidualStar1105

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Apply Mathlib's actual IsPath-to-pathGraph API to three original edges.
Extra edges among the four vertices are permitted: this is an ordinary Copy. -/
theorem false_of_three_edge_chain
    (R : SimpleGraph V) (hfree : (pathGraph 4).Free R)
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h01 : R.Adj a b) (h12 : R.Adj b c) (h23 : R.Adj c d) : False := by
  let p : R.Walk a d :=
    .cons h01 (.cons h12 (.cons h23 .nil))
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [p, hab, hac, had, hbc, hbd, hcd]
  have hcopy : pathGraph 4 ⊑ R := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

/-- A reusable finite ORIGINAL four-vertex lemma, needed precisely to remove
the two-K2 h=3 obstruction. The center and all three leaves are derived. -/
theorem exists_center_of_four_min_degree_edges_three_path_free
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : Fintype.card V = 4)
    (hmin : ∀ x : V, 1 ≤ R.degree x)
    (hedges : 3 ≤ R.edgeFinset.card)
    (hfree : (pathGraph 4).Free R) :
    ∃ c : V, (Finset.univ.erase c).card = 3 ∧
      (∀ x : V, x ≠ c → R.Adj c x) ∧
      (∀ x : V, x ≠ c → ∀ y : V, y ≠ c → ¬ R.Adj x y) := by
  classical
  have htwo : ∃ c : V, 2 ≤ R.degree c := by
    by_contra hnone
    have hbound : ∀ x : V, R.degree x ≤ 1 := by
      intro x
      have hx : ¬ 2 ≤ R.degree x := by
        intro hx
        exact hnone ⟨x, hx⟩
      omega
    have hsum : (∑ x : V, R.degree x) ≤ ∑ x : V, (1 : ℕ) :=
      Finset.sum_le_sum (fun x _hx => hbound x)
    have hconstant : (∑ x : V, (1 : ℕ)) = 4 := by simp [hcard]
    have hhand := R.sum_degrees_eq_twice_card_edges
    omega
  obtain ⟨c, hc2⟩ := htwo
  have hneighbors : 1 < (R.neighborFinset c).card := by
    rw [R.card_neighborFinset_eq_degree c]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hneighbors
  have hcu : R.Adj c u := (R.mem_neighborFinset c u).mp hu
  have hcv : R.Adj c v := (R.mem_neighborFinset c v).mp hv
  let T : Finset V := {c, u, v}
  have hTcard : T.card = 3 := by
    simp [T, hcu.ne, hcv.ne, huv]
  have hrestcard : (Finset.univ \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T),
      Finset.card_univ, hcard, hTcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hrestcard
  have hzmem : z ∈ Finset.univ \ T := by
    rw [hz]
    exact Finset.mem_singleton_self z
  have hzT : z ∉ T := (Finset.mem_sdiff.mp hzmem).2
  have hzc : z ≠ c := by
    intro h
    apply hzT
    simp [T, h]
  have hzu : z ≠ u := by
    intro h
    apply hzT
    simp [T, h]
  have hzv : z ≠ v := by
    intro h
    apply hzT
    simp [T, h]
  have hall : ∀ x : V, x = c ∨ x = u ∨ x = v ∨ x = z := by
    intro x
    by_cases hxT : x ∈ T
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxc | hxu | hxv
      · exact Or.inl hxc
      · exact Or.inr (Or.inl hxu)
      · exact Or.inr (Or.inr (Or.inl hxv))
    · have hxrest : x ∈ Finset.univ \ T :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩
      have hxz : x = z := by simpa only [hz, Finset.mem_singleton] using hxrest
      exact Or.inr (Or.inr (Or.inr hxz))
  have hcz : R.Adj c z := by
    have hzpos : 0 < R.degree z := by
      have hm := hmin z
      omega
    obtain ⟨y, hzy⟩ := (R.degree_pos_iff_exists_adj z).mp hzpos
    rcases hall y with hyc | hyu | hyv | hyz
    · subst y
      exact hzy.symm
    · subst y
      exact False.elim (false_of_three_edge_chain R hfree z u c v
        hzu hzc hzv hcu.ne.symm huv hcv.ne hzy hcu.symm hcv)
    · subst y
      exact False.elim (false_of_three_edge_chain R hfree z v c u
        hzv hzc hzu hcv.ne.symm huv.symm hcu.ne hzy hcv.symm hcu)
    · exact False.elim (hzy.ne hyz.symm)
  have hnotuv : ¬ R.Adj u v := by
    intro huvAdj
    exact false_of_three_edge_chain R hfree z c u v
      hzc hzu hzv hcu.ne hcv.ne huv hcz.symm hcu huvAdj
  have hnotuz : ¬ R.Adj u z := by
    intro huzAdj
    exact false_of_three_edge_chain R hfree v c u z
      hcv.ne.symm huv.symm hzv.symm hcu.ne hzc.symm hzu.symm
      hcv.symm hcu huzAdj
  have hnotvz : ¬ R.Adj v z := by
    intro hvzAdj
    exact false_of_three_edge_chain R hfree u c v z
      hcu.ne.symm huv hzu.symm hcv.ne hzc.symm hzv.symm
      hcu.symm hcv hvzAdj
  have hleaf : ∀ x : V, x ≠ c → x = u ∨ x = v ∨ x = z := by
    intro x hxc
    rcases hall x with h | h | h | h
    · exact False.elim (hxc h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, hcard]
  · intro x hxc
    rcases hleaf x hxc with rfl | rfl | rfl
    · exact hcu
    · exact hcv
    · exact hcz
  · intro x hxc y hyc hxy
    rcases hleaf x hxc with rfl | rfl | rfl <;>
      rcases hleaf y hyc with rfl | rfl | rfl
    all_goals first
      | exact hxy.ne rfl
      | exact hnotuv hxy
      | exact hnotuv hxy.symm
      | exact hnotuz hxy
      | exact hnotuz hxy.symm
      | exact hnotvz hxy
      | exact hnotvz hxy.symm

omit [Fintype V] in
/-- Project the generic lemma from precisely ORIGINAL G.induce(K\\W).
The actual ambient center, exact three leaves and their original adjacency
are returned. No cover or universal-W assertion is assumed or concluded. -/
theorem original_residual_star
    (G : SimpleGraph V) [DecidableRel G.Adj] (K W : Finset V)
    (hcard : (K \ W).card = 4)
    (hmin : ∀ x : ((K \ W : Finset V) : Set V),
      1 ≤ (G.induce ((K \ W : Finset V) : Set V)).degree x)
    (hedges : 3 ≤ (G.induce ((K \ W : Finset V) : Set V)).edgeFinset.card)
    (hfree : (pathGraph 4).Free (G.induce ((K \ W : Finset V) : Set V))) :
    ∃ c : V, c ∈ K \ W ∧ ((K \ W).erase c).card = 3 ∧
      (∀ x ∈ (K \ W).erase c, G.Adj c x) ∧
      (∀ x ∈ (K \ W).erase c, ∀ y ∈ (K \ W).erase c, ¬ G.Adj x y) := by
  classical
  let R := G.induce ((K \ W : Finset V) : Set V)
  have hRcard : Fintype.card ((K \ W : Finset V) : Set V) = 4 :=
    (Fintype.card_of_finset' (p := ((K \ W : Finset V) : Set V))
      (K \ W) (fun _ => Iff.rfl)).trans hcard
  obtain ⟨c, _hthree, hcenter, hleaves⟩ :=
    exists_center_of_four_min_degree_edges_three_path_free R hRcard hmin hedges hfree
  refine ⟨c.val, c.property, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem c.property, hcard]
  · intro x hx
    have hx' := Finset.mem_erase.mp hx
    have hxc : (⟨x, hx'.2⟩ : ((K \ W : Finset V) : Set V)) ≠ c := by
      intro heq
      exact hx'.1 (congrArg Subtype.val heq)
    exact hcenter _ hxc
  · intro x hx y hy
    have hx' := Finset.mem_erase.mp hx
    have hy' := Finset.mem_erase.mp hy
    have hxc : (⟨x, hx'.2⟩ : ((K \ W : Finset V) : Set V)) ≠ c := by
      intro heq
      exact hx'.1 (congrArg Subtype.val heq)
    have hyc : (⟨y, hy'.2⟩ : ((K \ W : Finset V) : Set V)) ≠ c := by
      intro heq
      exact hy'.1 (congrArg Subtype.val heq)
    exact hleaves _ hxc _ hyc

end ErdosProblems.PathUpperReduction.H3ResidualStar1105

noncomputable section
namespace ErdosProblems.PathUpperReduction.H3CountStar1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.H3ResidualCount1105
open ErdosProblems.PathUpperReduction.H3ResidualStar1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exact zero-deficit original seed count and original minimum degrees,
together with ordinary P4 exclusion on the SAME residual, force its actual
center and three independent original leaves. No center, clique or cover is
supplied. -/
theorem original_h3_count_to_residual_star (G : SimpleGraph V) (d : ℕ)
    (K W : Finset V) (hd : 4 ≤ d) (hKcard : K.card = d + 3)
    (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hQ : (withinEdges G K).card = d.choose 2 + 3 * d)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hfree : (pathGraph 4).Free (G.induce ((K \ W : Finset V) : Set V))) :
    ∃ c ∈ K \ W, ((K \ W).erase c).card = 3 ∧
      (∀ x ∈ (K \ W).erase c, G.Adj c x) ∧
      (∀ x ∈ (K \ W).erase c, ∀ y ∈ (K \ W).erase c, ¬ G.Adj x y) := by
  classical
  obtain ⟨hRcard, hRedges⟩ :=
    h3_residual_edges_ge_three_of_exact_seed_count G d K W hd hKcard hWcard hWK hQ
  have hRmin := h3_residual_min_degree_of_original_seed_degree G d K W hd hWcard hseed
  have hmin : ∀ u : ((K \ W : Finset V) : Set V),
      1 ≤ (G.induce ((K \ W : Finset V) : Set V)).degree u := by
    intro u
    have hcount := hRmin u.val u.property
    have hpos : 0 < ((K \ W).filter (fun z => G.Adj u.val z)).card := hcount
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨hzR, huz⟩ := Finset.mem_filter.mp hz
    have hadj : (G.induce ((K \ W : Finset V) : Set V)).Adj u ⟨z, hzR⟩ := huz
    exact hadj.degree_pos_left
  have hedgeeq : (withinEdges G (K \ W)).card =
      (G.induce ((K \ W : Finset V) : Set V)).edgeFinset.card := by
    simpa only [withinEdges] using G.card_filter_edgeFinset_toFinset_subset (K \ W)
  have hedges : 3 ≤ (G.induce ((K \ W : Finset V) : Set V)).edgeFinset.card := by
    rw [← hedgeeq]
    exact hRedges
  exact original_residual_star G K W hRcard hmin hedges hfree

end ErdosProblems.PathUpperReduction.H3CountStar1105
end

namespace ErdosProblems.AntiRamseyHighSeedDegreePool1105

open scoped BigOperators

/-- At least `d - 1` vertices have original degree at least `d + 1`.
No minimum-degree assumption is needed for this counting statement. -/
theorem high_seed_degree_pool {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d h : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h)
    (horder : Fintype.card V = d + h)
    (hedges : d * (d - 1) + 2 * d * h ≤
      2 * G.edgeFinset.card + 2 * (h - 3)) :
    d - 1 ≤ (Finset.univ.filter fun v : V => d + 1 ≤ G.degree v).card := by
  classical
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

end ErdosProblems.AntiRamseyHighSeedDegreePool1105

namespace ErdosProblems.PathUpperReduction.KernelCycleInsertion1105

open SimpleGraph Finset

/-- A strict actual seed-cover gap forces an actual predecessor chord and
therefore a spanning original path with two actual contacts to the new vertex.
The contact count is the count on the FULL supplied cycle range. -/
theorem spanning_contact_path_of_cover_gap
    {V : Type*} [DecidableEq V] {n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : (cycleGraph (n + 3)).Copy G)
    (z : V) (K : Finset V) (j t : ℕ)
    (hK : ∀ v ∈ K, v ∈ Set.range c)
    (hcover : ∀ X : Finset V,
      (∀ u ∈ K, ∀ v ∈ K, G.Adj u v → u ∈ X ∨ v ∈ X) → t ≤ X.card)
    (hcount : (Finset.univ.filter (fun i : Fin (n + 3) => G.Adj z (c i))).card = j)
    (hgap : n + 3 - j < t) :
    ∃ p : (pathGraph (n + 3)).Copy G,
      G.Adj z (p 0) ∧ G.Adj z (p (Fin.last (n + 2))) ∧
      Set.range p = Set.range c := by
  classical
  let N : Finset (Fin (n + 3)) := univ.filter (fun i => G.Adj z (c i))
  let P : Finset (Fin (n + 3)) := univ.filter (fun i => G.Adj z (c (i + 1)))
  let σ : Equiv.Perm (Fin (n + 3)) := finRotate (n + 3)
  have hPN : P.image σ = N := by
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hadj := (Finset.mem_filter.mp hi).2
      simpa only [σ, finRotate_apply] using hadj
    · intro ha
      refine ⟨σ.symm a, ?_, σ.apply_symm_apply a⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have he : σ.symm a + 1 = a := by
        simpa only [σ, finRotate_apply] using σ.apply_symm_apply a
      rw [he]
      exact (Finset.mem_filter.mp ha).2
  have hPcard : P.card = j := by
    calc
      P.card = (P.image σ).card := (Finset.card_image_of_injective P σ.injective).symm
      _ = N.card := congrArg Finset.card hPN
      _ = j := hcount
  let Q : Finset (Fin (n + 3)) := univ \ P
  let X : Finset V := Q.image c
  have hXcard : X.card = n + 3 - j := by
    calc
      X.card = Q.card := Finset.card_image_of_injective Q c.injective
      _ = (univ : Finset (Fin (n + 3))).card - P.card :=
        Finset.card_sdiff_of_subset (Finset.subset_univ P)
      _ = n + 3 - j := by rw [Finset.card_univ, Fintype.card_fin, hPcard]
  have hex : ∃ r s : Fin (n + 3), r ∈ P ∧ s ∈ P ∧ G.Adj (c r) (c s) := by
    by_contra hno
    have hind (r s : Fin (n + 3)) (hr : r ∈ P) (hs : s ∈ P) :
        ¬G.Adj (c r) (c s) := by
      intro hadj
      exact hno ⟨r, s, hr, hs, hadj⟩
    have hXcover : ∀ u ∈ K, ∀ v ∈ K, G.Adj u v → u ∈ X ∨ v ∈ X := by
      intro u hu v hv huv
      obtain ⟨r, rfl⟩ := hK u hu
      obtain ⟨s, rfl⟩ := hK v hv
      by_cases hr : r ∈ Q
      · exact Or.inl (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
      by_cases hs : s ∈ Q
      · exact Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
      have hrP : r ∈ P := by
        by_contra hnot
        exact hr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      have hsP : s ∈ P := by
        by_contra hnot
        exact hs (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      exact (hind r s hrP hsP huv).elim
    have hbound := hcover X hXcover
    rw [hXcard] at hbound
    omega
  obtain ⟨r, s, hr, hs, hrsAdj⟩ := hex
  have hrs : r ≠ s := by
    intro he
    exact hrsAdj.ne (congrArg c he)
  obtain ⟨p, hp0, hpLast, hpRange⟩ :=
    CycleChordPath1105.path_of_actual_cycle_chord G c r s hrs hrsAdj
  refine ⟨p, ?_, ?_, hpRange⟩
  · rw [hp0]
    exact (Finset.mem_filter.mp hr).2
  · rw [hpLast]
    exact (Finset.mem_filter.mp hs).2

/-- The derived spanning contact path closes through the ACTUAL fresh vertex.
The new cycle support is exactly the complete old Copy range plus that vertex,
so a later restoration can reuse its genuine full-prefix contact count. -/
theorem cycle_with_exact_support_of_cover_gap
    {V : Type*} [DecidableEq V] {n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : (cycleGraph (n + 3)).Copy G)
    (z : V) (K : Finset V) (j t : ℕ)
    (hK : ∀ v ∈ K, v ∈ Set.range c)
    (hcover : ∀ X : Finset V,
      (∀ u ∈ K, ∀ v ∈ K, G.Adj u v → u ∈ X ∨ v ∈ X) → t ≤ X.card)
    (hcount : (Finset.univ.filter (fun i : Fin (n + 3) => G.Adj z (c i))).card = j)
    (hgap : n + 3 - j < t) (hz : z ∉ Set.range c) :
    ∃ D : G.Walk z z, D.IsCycle ∧ D.length = n + 4 ∧
      ∀ v : V, v ∈ D.support ↔ v = z ∨ v ∈ Set.range c := by
  classical
  obtain ⟨p, hleft, hright, hprange⟩ :=
    spanning_contact_path_of_cover_gap G c z K j t hK hcover hcount hgap
  obtain ⟨P, hP, hPLength, hPSupport⟩ :=
    CycleEdgeContact1105.walk_of_path_copy G p
  have hzP : z ∉ P.support := by
    intro hmem
    have hrange := (hPSupport z).mp hmem
    rw [hprange] at hrange
    exact hz hrange
  let D : G.Walk z z := SimpleGraph.Walk.cons hleft (P.concat hright.symm)
  obtain ⟨hD, hDLength⟩ := CycleInsertion1105.cycle_of_fresh_endpoint_contact
    G P hP z (by omega) hzP hleft hright.symm
  refine ⟨D, hD, ?_, ?_⟩
  · change (SimpleGraph.Walk.cons hleft (P.concat hright.symm)).length = n + 4
    omega
  · intro v
    simp only [D, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    rw [hPSupport v, hprange]
    constructor
    · rintro (hv | hv | hv)
      · exact Or.inl hv
      · exact Or.inr hv
      · exact Or.inl hv
    · rintro (hv | hv)
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)

end ErdosProblems.PathUpperReduction.KernelCycleInsertion1105

section

open SimpleGraph

namespace ErdosProblems.PathUpperReduction.LongCycleFromMinimumDegree1105

variable {V : Type*} [Fintype V]

/-- A maximum over ALL actual simple paths, seeded by an actual nil path. -/
theorem exists_global_maximum_path (G : SimpleGraph V) (x : V) :
    ∃ u v, ∃ P : G.Walk u v, P.IsPath ∧
      ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length := by
  classical
  let s : Set ℕ := {l | ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ Q.length = l}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V)) (by
    intro l hl
    obtain ⟨a, b, Q, hQ, hlen⟩ := hl
    exact hlen ▸ hQ.length_lt.le)
  have hseed : 0 ∈ s := ⟨x, x, Walk.nil, Walk.IsPath.nil, rfl⟩
  obtain ⟨l, hm⟩ := hs.exists_maximal ⟨0, hseed⟩
  obtain ⟨u, v, P, hp, hlen⟩ := hm.1
  refine ⟨u, v, P, hp, ?_⟩
  intro a b Q hQ
  have hbound := hm.le (show Q.length ∈ s from ⟨a, b, Q, hQ, rfl⟩)
  omega

omit [Fintype V] in
/-- Global maximum, rather than merely maximal, captures BOTH endpoints. -/
theorem global_maximum_captures_endpoints {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (hp : P.IsPath)
    (hmax : ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length) :
    (∀ z, G.Adj u z → z ∈ P.support) ∧
      (∀ z, G.Adj v z → z ∈ P.support) := by
  constructor
  · intro z huz
    by_contra hz
    let Q := Walk.cons huz.symm P
    have hQ : Q.IsPath := hp.cons hz
    have hbound := hmax z v Q hQ
    simp only [Q, Walk.length_cons] at hbound
    omega
  · intro z hvz
    by_contra hz
    have hzrev : z ∉ P.reverse.support := by simpa only [Walk.support_reverse,
      List.mem_reverse] using hz
    let Q := Walk.cons hvz.symm P.reverse
    have hQ : Q.IsPath := hp.reverse.cons hzrev
    have hbound := hmax z u Q hQ
    simp only [Q, Walk.length_cons, Walk.length_reverse] at hbound
    omega

/-- A nonspanning actual cycle extends to a path of its FULL cycle length. -/
theorem cycle_length_le_global_maximum {G : SimpleGraph V} {u v x : V}
    (hconn : G.Connected) (P : G.Walk u v)
    (hmax : ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length)
    (C : G.Walk x x) (hC : C.IsCycle) (hsmall : C.length < Fintype.card V) :
    C.length ≤ P.length := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, z ∉ C.support := by
    by_contra hnone
    have hall : ∀ z, z ∈ C.support := by
      intro z
      by_contra hz
      exact hnone ⟨z, hz⟩
    have heq : C.support.toFinset = Finset.univ := by
      ext z
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hall z
    have hcard := BoundaryEndpoint.cycle_vertex_card C hC
    rw [heq, Finset.card_univ] at hcard
    omega
  obtain ⟨w⟩ := hconn x z
  obtain ⟨dart, _hmem, hin, hout⟩ :=
    w.exists_boundary_dart {y | y ∈ C.support} C.start_mem_support hz
  let rot := C.rotate dart.fst hin
  have hrot : rot.IsCycle := hC.rotate hin
  have houtside : dart.snd ∉ rot.dropLast.support := by
    intro h
    rw [rot.support_dropLast hrot.not_nil] at h
    have hrotmem : dart.snd ∈ rot.support := List.mem_of_mem_dropLast h
    have hCmem : dart.snd ∈ C.support :=
      (C.mem_support_rotate_iff dart.fst hin).mp hrotmem
    exact hout hCmem
  let Q := Walk.cons dart.adj.symm rot.dropLast
  have hQ : Q.IsPath := hrot.isPath_dropLast.cons houtside
  have hlen : Q.length = C.length := by
    change rot.dropLast.length + 1 = C.length
    exact (Walk.length_dropLast_add_one hrot.not_nil).trans
      (Walk.length_rotate C dart.fst hin)
  have hbound := hmax _ _ Q hQ
  rw [hlen] at hbound
  exact hbound

/-- The actual Dirac consequence for d≥4, obtained by TWO fitting applications
of BoundaryEndpoint. Every vertex and edge remains in the original graph. -/
theorem exists_long_cycle_of_minimum_degree (G : SimpleGraph V) (d : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdelete : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hdegree : ∀ z, d ≤ Nat.card (G.neighborSet z)) :
    ∃ x, ∃ C : G.Walk x x, C.IsCycle ∧ 2 * d ≤ C.length := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u, v, P, hp, hmax⟩ := exists_global_maximum_path G (Classical.arbitrary V)
  obtain ⟨hleft, hright⟩ := global_maximum_captures_endpoints P hp hmax
  have hcounts (x : V) (hcapture : ∀ z, G.Adj x z → z ∈ P.support) :
      (P.support.toFinset.filter (fun z => G.Adj x z)).card =
        Nat.card (G.neighborSet x) := by
    have heq : P.support.toFinset.filter (fun z => G.Adj x z) = G.neighborFinset x := by
      ext z
      simp only [Finset.mem_filter, List.mem_toFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.2, fun hz => ⟨hcapture z hz, hz⟩⟩
    rw [heq, SimpleGraph.neighborFinset_def, ← Nat.card_eq_card_toFinset]
  have hleftDegree : d ≤ (P.support.toFinset.filter (fun z => G.Adj u z)).card := by
    rw [hcounts u hleft]
    exact hdegree u
  have hrightDegree : d ≤ (P.support.toFinset.filter (fun z => G.Adj v z)).card := by
    rw [hcounts v hright]
    exact hdegree v
  have hleftBound : (P.support.toFinset.filter (fun z => G.Adj u z)).card ≤ P.length := by
    have hsub : P.support.toFinset.filter (fun z => G.Adj u z) ⊆
        P.support.toFinset.erase u := by
      intro z hz
      obtain ⟨hzP, huz⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_erase.mpr ⟨huz.ne', hzP⟩
    have hbound := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr P.start_mem_support),
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hbound
    omega
  have hPfive : 5 ≤ P.length + 1 := by omega
  have hsum : 2 * d ≤
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
        (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card := by
    simp only [Walk.getVert_zero, Walk.getVert_length]
    omega
  have hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected := by
    intro i _hi _hlast
    exact hdelete (P.getVert i.val)
  have hlong : 2 * d < P.length + 1 := by
    by_contra hnot
    have hshort : P.length + 1 ≤ 2 * d := by omega
    obtain ⟨C, hC, hlen⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold
      P hp hdel (P.length + 1) hPfive le_rfl (by omega)
    have hbound := hmax _ _ C.dropLast hC.isPath_dropLast
    have hdrop := Walk.length_dropLast_add_one hC.not_nil
    have hsmall : C.length < Fintype.card V := by omega
    have hbound' := cycle_length_le_global_maximum hconn P hmax C hC hsmall
    omega
  obtain ⟨C, hC, hlen⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold
    P hp hdel (2 * d) (by omega) hlong.le hsum
  exact ⟨P.getVert 0, C, hC, hlen⟩

end ErdosProblems.PathUpperReduction.LongCycleFromMinimumDegree1105

end

namespace ErdosProblems.AntiRamseyEvenPathFiniteWindow

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

def evenBound (ell n : ℕ) : ℕ :=
  max ((2 * ell).choose 2 + 1)
    ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2)

def windowEnd (ell : ℕ) : ℕ :=
  2 * ell + 2 + (ell - 1) / 2

/-- At and above the first integral crossing, the linear branch dominates. -/
theorem constant_le_linear (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : windowEnd ell ≤ m) :
    (2 * ell).choose 2 + 1 ≤
      (ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 2 := by
  have hmell : ell ≤ m := by
    dsimp [windowEnd] at hm
    omega
  have hthreshold : 5 * ell + 2 ≤ 2 * m := by
    dsimp [windowEnd] at hm
    omega
  have hthresholdR : (5 : ℝ) * (ell : ℝ) + 2 ≤ 2 * (m : ℝ) := by
    exact_mod_cast hthreshold
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast (show 1 ≤ ell by omega)
  have hpredR : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    have hsum : ((ell - 1 : ℕ) : ℝ) + 1 = (ell : ℝ) := by
      exact_mod_cast (show ell - 1 + 1 = ell by omega)
    linarith
  have hsubR : ((m - ell : ℕ) : ℝ) = (m : ℝ) - (ell : ℝ) := by
    have hsum : ((m - ell : ℕ) : ℝ) + (ell : ℝ) = (m : ℝ) := by
      exact_mod_cast (show m - ell + ell = m by omega)
    linarith
  have hproduct : 0 ≤ ((ell : ℝ) - 1) *
      (2 * (m : ℝ) - 5 * (ell : ℝ) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hreal :
      (((2 * ell).choose 2 + 1 : ℕ) : ℝ) ≤
        (((ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 2 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [Nat.cast_choose_two ℝ (2 * ell), Nat.cast_choose_two ℝ (ell - 1)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, hpredR, hsubR]
    nlinarith [hproduct]
  exact_mod_cast hreal

/-- The increment is proved only after the full base window. -/
theorem bound_succ (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : windowEnd ell ≤ m) :
    evenBound ell (m + 1) = evenBound ell m + (ell - 1) := by
  have hmell : ell ≤ m := by
    dsimp [windowEnd] at hm
    omega
  have hleft := constant_le_linear ell m hell hm
  have hright := constant_le_linear ell (m + 1) hell (by omega)
  have hsub : m + 1 - ell + 1 = (m - ell + 1) + 1 := by omega
  simp only [evenBound, max_eq_right hleft, max_eq_right hright]
  rw [hsub]
  ring

/-- For ell>=2, high ORIGINAL NEW at every vertex plus every full-host base
in the exact finite window implies the original even-path anti-Ramsey upper
on every n>=2*ell+2. The color type in the high-NEW premise is arbitrary;
no finiteness or original surjectivity is supplied. -/
theorem antiRamseyNum_even_path_le_of_high_new_and_window
    (ell : ℕ) (hell : 2 ≤ ell)
    (hhigh : ∀ (n : ℕ), 2 * ell + 2 ≤ n →
      ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin n) C),
        (∀ v : Fin n, ell ≤ (newColors χ v).card) →
        ∃ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
          IsRainbow f.toHom χ)
    (hbases : ∀ (n : ℕ), 2 * ell + 2 ≤ n →
      n ≤ 2 * ell + 2 + (ell - 1) / 2 →
      antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
        max ((2 * ell).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2)) :
    ∀ (n : ℕ), 2 * ell + 2 ≤ n →
      antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
        max ((2 * ell).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    change antiRamseyNum (pathGraph (2 * ell + 2)) n ≤ evenBound ell n
    by_cases hwindow : n ≤ windowEnd ell
    · exact hbases n hn hwindow
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (by omega)
    have hm : windowEnd ell ≤ m := by omega
    have hmk : 2 * ell + 2 ≤ m := by
      dsimp [windowEnd] at hm
      omega
    have hind :
        antiRamseyNum (pathGraph (2 * ell + 2)) m ≤ evenBound ell m :=
      ih m (by omega) hmk
    have hjump := bound_succ ell m hell hm
    let S : Set ℕ :=
      {q | ∃ χ : TopEdgeLabeling (Fin (m + 1)) (Fin q),
        Function.Surjective χ ∧
        ∀ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin (m + 1))),
          ¬IsRainbow f.toHom χ}
    have hbounded : BddAbove S := by
      refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin (m + 1))).edgeSet), ?_⟩
      intro q hq
      obtain ⟨χ, hχ, _⟩ := hq
      simpa using Fintype.card_le_of_surjective χ hχ
    change sSup S ≤ evenBound ell (m + 1)
    refine (csSup_le_iff' hbounded).2 ?_
    intro q hq
    obtain ⟨χ, hχ, hno⟩ := hq
    by_contra hnot
    have hlarge : evenBound ell (m + 1) < q := by omega
    have hnew : ∀ v : Fin (m + 1), ell ≤ (newColors χ v).card := by
      intro v
      have hdelete :=
        surjective_color_count_le_antiRamseyNum_add_newColors
          (pathGraph (2 * ell + 2)) χ hχ hno v
      have hstep : q ≤ evenBound ell m + (newColors χ v).card :=
        le_trans hdelete (Nat.add_le_add_right hind (newColors χ v).card)
      rw [hjump] at hlarge
      omega
    obtain ⟨f, hf⟩ := hhigh (m + 1) hn (Fin q) χ hnew
    exact hno f hf

end ErdosProblems.AntiRamseyEvenPathFiniteWindow

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

theorem spanning_degree_slots_with_nonuniversal_cap
    (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected) (hneTop : H ≠ ⊤)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2) :
    ∃ (a : ℕ) (L : Finset (Fin k)),
      1 ≤ a ∧ 2 * a ≤ k - 2 ∧ L.card = a + 1 ∧
      (∀ x ∈ L, H.degree x ≤ a) ∧
      H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) ∧
      (∀ x : Fin k, ¬ H.IsUniversal x → H.degree x ≤ k - 2 - a) := by
  classical
  let N : Finset (Fin k) := Finset.univ.filter (fun v => ¬ H.IsUniversal v)
  have hN : N.Nonempty := by
    by_contra hnone
    apply hneTop
    apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
    intro x
    by_contra hx
    apply hnone
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨v, hvN, hmaxv⟩ := Finset.exists_max_image N (fun v => H.degree v) hN
  have hvNU : ¬ H.IsUniversal v := (Finset.mem_filter.mp hvN).2
  let T := Hᶜ.neighborFinset v
  have hTcard : T.card = k - 1 - H.degree v := by
    change (Hᶜ.neighborFinset v).card = k - 1 - H.degree v
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree_compl,
      Fintype.card_fin]
  have hbLt : H.degree v < k - 1 := by
    simpa only [Fintype.card_fin] using
      (SimpleGraph.degree_lt_card_sub_one (G := H) v).mpr hvNU
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, huT, hmaxu⟩ := Finset.exists_max_image T (fun v => H.degree v) hT
  have hcompl : Hᶜ.Adj v u :=
    (SimpleGraph.mem_neighborFinset (G := Hᶜ) (v := v) u).mp huT
  obtain ⟨hvu, hmissing⟩ := (SimpleGraph.compl_adj H v u).mp hcompl
  have huNU : ¬ H.IsUniversal u := by
    intro hu
    exact hmissing (hu hvu.symm).symm
  have huN : u ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huNU⟩
  let a := H.degree u
  have haLeB : a ≤ H.degree v := hmaxv u huN
  have hsum : a + H.degree v ≤ k - 2 := by
    have := hclosure v u hvu hmissing
    dsimp only [a]
    omega
  have haPos : 1 ≤ a := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hvu.symm (hconn u v)
    exact hpos
  have htwo : 2 * a ≤ k - 2 := by omega
  have hk2 : 2 ≤ k := by omega
  have hsumAmbient : a + H.degree v + 2 ≤ k := by
    have h := Nat.add_le_add_right hsum 2
    rw [Nat.sub_add_cancel hk2] at h
    exact h
  have hsize : a + 1 ≤ T.card := by omega
  obtain ⟨L, hLT, hLcard⟩ := Finset.exists_subset_card_eq hsize
  have hLdegree : ∀ x ∈ L, H.degree x ≤ a := by
    intro x hx
    exact hmaxu x (hLT hx)
  have hcount := edge_count_le_complement_clique_and_slots H L a hLdegree
  have hshift : k - (a + 1) = k - 1 - a := by omega
  have hbound : H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) := by
    simpa only [hLcard, hshift, Nat.mul_comm] using hcount
  refine ⟨a, L, haPos, htwo, hLcard, hLdegree, hbound, ?_⟩
  intro x hx
  have hxN : x ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  have hxLe : H.degree x ≤ H.degree v := hmaxv x hxN
  omega

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.ResidualForestStar1105

open SimpleGraph

/-- Ordinary P3 plus a vertex-disjoint ordinary P2 is forbidden. -/
def NoP3AndP2 {V : Type*} (R : SimpleGraph V) : Prop :=
  ∀ p : Fin 5 → V, Function.Injective p →
    R.Adj (p 0) (p 1) → R.Adj (p 1) (p 2) → R.Adj (p 3) (p 4) → False

/-- Three vertex-disjoint ordinary edges are forbidden. -/
def NoThreeP2 {V : Type*} (R : SimpleGraph V) : Prop :=
  ∀ p : Fin 6 → V, Function.Injective p →
    R.Adj (p 0) (p 1) → R.Adj (p 2) (p 3) → R.Adj (p 4) (p 5) → False

/-- Reuse the checked H3 proof's exact ordinary IsPath-to-Copy bridge. -/
theorem false_of_three_edge_chain {V : Type*}
    (R : SimpleGraph V) (hfree : (pathGraph 4).Free R)
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h01 : R.Adj a b) (h12 : R.Adj b c) (h23 : R.Adj c d) : False := by
  classical
  let p : R.Walk a d := .cons h01 (.cons h12 (.cons h23 .nil))
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [p, hab, hac, had, hbc, hbd, hcd]
  have hcopy : pathGraph 4 ⊑ R := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

theorem no_edge_outside_two_edge_path {V : Type*} [DecidableEq V]
    (R : SimpleGraph V) (hforest : NoP3AndP2 R)
    (a b c : V) (hac : a ≠ c) (hab : R.Adj a b) (hbc : R.Adj b c)
    (x y : V) (hx : x ∉ ({a, b, c} : Finset V))
    (hy : y ∉ ({a, b, c} : Finset V)) : ¬ R.Adj x y := by
  classical
  intro hxy
  have habne : a ≠ b := hab.ne
  have hbcne : b ≠ c := hbc.ne
  have hxyne : x ≠ y := hxy.ne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  rcases hx with ⟨hxa, hxb, hxc⟩
  rcases hy with ⟨hya, hyb, hyc⟩
  let p : Fin 5 → V := ![a, b, c, x, y]
  have hinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [p, habne, habne.symm, hac, hac.symm, hbcne, hbcne.symm,
        hxa, Ne.symm hxa, hxb, Ne.symm hxb, hxc, Ne.symm hxc,
        hya, Ne.symm hya, hyb, Ne.symm hyb, hyc, Ne.symm hyc,
        hxyne, hxyne.symm] at hij ⊢
  exact hforest p hinj (by simpa [p] using hab)
    (by simpa [p] using hbc) (by simpa [p] using hxy)

theorem exists_two_edge_path {V : Type*} [Fintype V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : 5 ≤ Fintype.card V) (hmin : ∀ x, 1 ≤ R.degree x)
    (hforest : NoThreeP2 R) :
    ∃ a b c : V, a ≠ c ∧ R.Adj a b ∧ R.Adj b c := by
  classical
  by_contra hnone
  have hpartner : ∀ u v w : V, R.Adj u v → R.Adj u w → w = v := by
    intro u v w huv huw
    by_contra hwv
    exact hnone ⟨v, u, w, Ne.symm hwv, huv.symm, huw⟩
  have neighbor (x : V) : ∃ y, R.Adj x y := by
    apply (R.degree_pos_iff_exists_adj x).mp
    have hx := hmin x
    omega
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a : V := Classical.arbitrary V
  obtain ⟨b, hab⟩ := neighbor a
  let T : Finset V := {a, b}
  have hTcard : T.card = 2 := by simp [T, hab.ne]
  have hTsmall : T.card < (Finset.univ : Finset V).card := by
    rw [hTcard, Finset.card_univ]
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hTsmall
  obtain ⟨d, hcd⟩ := neighbor c
  have hd : d ∉ T := by
    intro hd
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hda | hdb
    · rw [hda] at hcd
      have hcb := hpartner a b c hab hcd.symm
      exact hc (by simp [T, hcb])
    · rw [hdb] at hcd
      have hca := hpartner b a c hab.symm hcd.symm
      exact hc (by simp [T, hca])
  simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  rcases hc with ⟨hca, hcb⟩
  rcases hd with ⟨hda, hdb⟩
  have habne : a ≠ b := hab.ne
  have hcdne : c ≠ d := hcd.ne
  let U : Finset V := {a, b, c, d}
  have hUcard : U.card = 4 := by
    simp [U, habne, Ne.symm hca, Ne.symm hda, Ne.symm hcb, Ne.symm hdb, hcdne]
  have hUsmall : U.card < (Finset.univ : Finset V).card := by
    rw [hUcard, Finset.card_univ]
    omega
  obtain ⟨e, _, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hUsmall
  obtain ⟨f, hef⟩ := neighbor e
  have hf : f ∉ U := by
    intro hf
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with hfa | hfb | hfc | hfd
    · rw [hfa] at hef
      have heb := hpartner a b e hab hef.symm
      exact he (by simp [U, heb])
    · rw [hfb] at hef
      have hea := hpartner b a e hab.symm hef.symm
      exact he (by simp [U, hea])
    · rw [hfc] at hef
      have hed := hpartner c d e hcd hef.symm
      exact he (by simp [U, hed])
    · rw [hfd] at hef
      have hec := hpartner d c e hcd.symm hef.symm
      exact he (by simp [U, hec])
  simp only [U, Finset.mem_insert, Finset.mem_singleton, not_or] at he hf
  rcases he with ⟨hea, heb, hec, hed⟩
  rcases hf with ⟨hfa, hfb, hfc, hfd⟩
  have hefne : e ≠ f := hef.ne
  let p : Fin 6 → V := ![a, b, c, d, e, f]
  have hinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [p, habne, habne.symm, hca, Ne.symm hca, hcb, Ne.symm hcb,
        hda, Ne.symm hda, hdb, Ne.symm hdb, hcdne, hcdne.symm,
        hea, Ne.symm hea, heb, Ne.symm heb, hec, Ne.symm hec, hed, Ne.symm hed,
        hfa, Ne.symm hfa, hfb, Ne.symm hfb, hfc, Ne.symm hfc, hfd, Ne.symm hfd,
        hefne, hefne.symm] at hij ⊢
  exact hforest p hinj (by simpa [p] using hab)
    (by simpa [p] using hcd) (by simpa [p] using hef)

/-- At least five ORIGINAL vertices, minimum degree one, ordinary P4 freedom,
and exclusion of the other two three-edge linear forests force a spanning
star. The actual center is derived and its singleton covers every edge. -/
theorem exists_center_of_min_degree_and_no_three_edge_linear_forest
    {V : Type*} [Fintype V] (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : 5 ≤ Fintype.card V) (hmin : ∀ x : V, 1 ≤ R.degree x)
    (hfree : (pathGraph 4).Free R)
    (hP3P2 : NoP3AndP2 R) (h3P2 : NoThreeP2 R) :
    ∃ b : V, (∀ x : V, x ≠ b → R.Adj b x) ∧
      (∀ x : V, x ≠ b → ∀ y : V, y ≠ b → ¬ R.Adj x y) ∧
      R.IsVertexCover ({b} : Set V) := by
  classical
  obtain ⟨a, b, c, hac, hab, hbc⟩ := exists_two_edge_path R hcard hmin h3P2
  let T : Finset V := {a, b, c}
  have hcenter : ∀ x : V, x ≠ b → R.Adj b x := by
    intro x hxb
    by_cases hx : x ∈ T
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hab.symm
      · exact False.elim (hxb rfl)
      · exact hbc
    · have hxpos : 0 < R.degree x := by
        have hm := hmin x
        omega
      obtain ⟨y, hxy⟩ := (R.degree_pos_iff_exists_adj x).mp hxpos
      have hy : y ∈ T := by
        by_contra hy
        exact no_edge_outside_two_edge_path R hP3P2 a b c hac hab hbc
          x y hx hy hxy
      have hxa : x ≠ a := by intro h; exact hx (by simp [T, h])
      have hxc : x ≠ c := by intro h; exact hx (by simp [T, h])
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hya | hyb | hyc
      · subst hya
        exact False.elim (false_of_three_edge_chain R hfree x y b c
          hxa hxb hxc hab.ne hac hbc.ne hxy hab hbc)
      · subst hyb
        exact hxy.symm
      · subst hyc
        exact False.elim (false_of_three_edge_chain R hfree x y b a
          hxc hxb hxa hbc.ne.symm hac.symm hab.ne.symm
          hxy hbc.symm hab.symm)
  have hleaves : ∀ x : V, x ≠ b → ∀ y : V, y ≠ b → ¬ R.Adj x y := by
    intro x hxb y hyb hxy
    let U : Finset V := {b, x, y}
    have hUcard : U.card = 3 := by simp [U, hxb.symm, hyb.symm, hxy.ne]
    have hsmall : U.card < (Finset.univ : Finset V).card := by
      rw [hUcard, Finset.card_univ]
      omega
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
    have hzb : z ≠ b := by intro h; exact hz (by simp [U, h])
    have hzx : z ≠ x := by intro h; exact hz (by simp [U, h])
    have hzy : z ≠ y := by intro h; exact hz (by simp [U, h])
    exact false_of_three_edge_chain R hfree z b x y
      hzb hzx hzy hxb.symm hyb.symm hxy.ne
      (hcenter z hzb).symm (hcenter x hxb) hxy
  refine ⟨b, hcenter, hleaves, ?_⟩
  intro x y hxy
  by_cases hx : x = b
  · exact Or.inl (by simpa only [Set.mem_singleton_iff] using hx)
  by_cases hy : y = b
  · exact Or.inr (by simpa only [Set.mem_singleton_iff] using hy)
  exact False.elim (hleaves x hx y hy hxy)

end ErdosProblems.PathUpperReduction.ResidualForestStar1105

section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.StrictConeCore1105
open CountCoreBasis UniformCone1105

theorem degreeCore_eq_empty_of_cone_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : SimpleGraph (Option V)) (d : ℕ)
    (hcone : cone G ≤ H) (hH : degreeCore H (d + 1) = ∅) :
    degreeCore G d = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let C := degreeCore G d
  have hxC : x ∈ C := hx
  have hC : GoodCore G d C := degree_core_good G d
  have hsmall : (C.filter (fun z => G.Adj x z)).card < C.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hxx := (Finset.mem_filter.mp (heq.symm ▸ hxC)).2
    exact G.loopless.irrefl x hxx
  have hsize : d + 2 ≤ C.card := by
    have := hC x hxC
    omega
  let T := C.insertNone
  have hT : GoodCore H (d + 1) T := by
    intro a ha
    cases a with
    | none =>
      have hsub : C.image some ⊆ T.filter (fun z => H.Adj none z) := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨Finset.some_mem_insertNone.mpr hy, ?_⟩
        exact hcone (by trivial : (cone G).Adj none (some y))
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective C (Option.some_injective V)] at hc
      omega
    | some y =>
      have hy : y ∈ C := Finset.some_mem_insertNone.mp ha
      have hsub : (C.filter (fun z => G.Adj y z)).insertNone ⊆
          T.filter (fun z => H.Adj (some y) z) := by
        intro z hz
        cases z with
        | none =>
          exact Finset.mem_filter.mpr
            ⟨Finset.none_mem_insertNone,
              hcone (by trivial : (cone G).Adj (some y) none)⟩
        | some z =>
          obtain ⟨hzC, hyz⟩ := Finset.mem_filter.mp
            (Finset.some_mem_insertNone.mp hz)
          exact Finset.mem_filter.mpr
            ⟨Finset.some_mem_insertNone.mpr hzC, hcone hyz⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insertNone] at hc
      have := hC y hy
      omega
  have hnone : none ∈ degreeCore H (d + 1) :=
    good_subset_core H (d + 1) T hT Finset.none_mem_insertNone
  simp [hH] at hnone

end ErdosProblems.PathUpperReduction.StrictConeCore1105

example {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : SimpleGraph (Option V)) (d : ℕ)
    (hcone : ErdosProblems.PathUpperReduction.UniformCone1105.cone G ≤ H)
    (hH : ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore H (d + 1) = ∅) :
    ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d = ∅ :=
  ErdosProblems.PathUpperReduction.StrictConeCore1105.degreeCore_eq_empty_of_cone_le G H d hcone hH

end

namespace ErdosProblems.PathUpperReduction.TwoOutsiderCycleCover1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CommonOutsideNeighbors1105
open ErdosProblems.PathUpperReduction.CycleChordPath1105
open ErdosProblems.PathUpperReduction.EndpointAttachment1105

/-- Only the two distinguished outsiders require alternating contacts.
All other actual outsiders may have smaller contact sets and lower degrees. -/
theorem exists_actual_cover_of_two_outsider_toggles {V : Type*} {n d : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (hsize : n + 3 = 2 * d) (hfree : (pathGraph (n + 5)).Free G)
    (u v : V) (hu : u ∉ Set.range c) (hv : v ∉ Set.range c) (hne : u ≠ v)
    (htoggleu : ∀ i : Fin (n + 3), G.Adj u (c (i + 1)) ↔ ¬G.Adj u (c i))
    (htogglev : ∀ i : Fin (n + 3), G.Adj v (c (i + 1)) ↔ ¬G.Adj v (c i))
    (houtside : ∀ x y, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y) :
    ∃ A : Finset V, A.card = d ∧ G.IsVertexCover (A : Set V) := by
  classical
  let P : Fin (n + 3) → Prop := fun i => G.Adj u (c i)
  let N : Finset (Fin (n + 3)) := Finset.univ.filter P
  let M : Finset (Fin (n + 3)) := Finset.univ.filter (fun i => ¬P i)
  let σ : Equiv.Perm (Fin (n + 3)) := finRotate (n + 3)
  have hσtoggle (i : Fin (n + 3)) : P (σ i) ↔ ¬P i := by
    simpa only [P, σ, finRotate_apply] using htoggleu i
  have himage : N.image σ = M := by
    ext j
    simp only [N, M, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩ hσi
      exact (hσtoggle i).mp hσi hi
    · intro hj
      refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
      by_contra hi
      have hP := (hσtoggle (σ.symm j)).mpr hi
      rw [σ.apply_symm_apply] at hP
      exact hj hP
  have hMcard : M.card = N.card := by
    rw [← himage]
    exact Finset.card_image_of_injective N σ.injective
  have hsum : N.card + M.card = n + 3 := by
    simpa only [N, M, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) P)
  have hNcard : N.card = d := by omega
  have hcontained (z : V) (hz : z ∉ Set.range c) (i : Fin (n + 3)) :
      G.Adj z (c i) → G.Adj u (c i) := by
    intro hzi
    by_cases hzu : z = u
    · subst z
      exact hzi
    · by_contra hnui
      have hus : G.Adj u (c (i + 1)) := (htoggleu i).mpr hnui
      exact (successor_contacts_incompatible_of_free G c hfree z u hz hu hzu i)
        ⟨hzi, hus⟩
  have hcommonv (i : Fin (n + 3)) : G.Adj v (c i) ↔ G.Adj u (c i) := by
    have he := outside_contact_sets_agree_of_toggles G c hfree v u hv hu hne.symm
      htogglev htoggleu
    exact Set.ext_iff.mp he i
  let A : Finset V := N.image c
  have hAcard : A.card = d := by
    calc A.card = N.card := Finset.card_image_of_injective N c.injective
         _ = d := hNcard
  have hAmem (i : Fin (n + 3)) : c i ∈ A ↔ P i := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have he : j = i := c.injective hji
      subst j
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  have hnoBB (r s : Fin (n + 3)) (hr : ¬P r) (hs : ¬P s) :
      ¬G.Adj (c r) (c s) := by
    intro hchord
    have hrs : r ≠ s := by
      intro he
      exact hchord.ne (congrArg c he)
    obtain ⟨p, hp0, hplast, hprange⟩ :=
      path_of_actual_cycle_chord G c r s hrs hchord
    have hup : u ∉ Set.range p := by rw [hprange]; exact hu
    have hvp : v ∉ Set.range p := by rw [hprange]; exact hv
    have hleft : G.Adj u (p 0) := by
      rw [hp0]
      exact (htoggleu r).mpr hr
    have hright : G.Adj (p (Fin.last (n + 2))) v := by
      rw [hplast]
      exact ((hcommonv (s + 1)).mpr ((htoggleu s).mpr hs)).symm
    exact (endpoint_contacts_incompatible_of_free G (n + 2) hfree p u v
      hup hvp hne) ⟨hleft, hright⟩
  refine ⟨A, hAcard, ?_⟩
  intro x y hxy
  by_cases hxA : x ∈ A
  · exact Or.inl hxA
  by_cases hyA : y ∈ A
  · exact Or.inr hyA
  exfalso
  by_cases hxc : x ∈ Set.range c
  · obtain ⟨r, rfl⟩ := hxc
    have hr : ¬P r := fun h => hxA ((hAmem r).mpr h)
    by_cases hyc : y ∈ Set.range c
    · obtain ⟨s, rfl⟩ := hyc
      exact hnoBB r s (hr) (fun h => hyA ((hAmem s).mpr h)) hxy
    · exact hr (hcontained y hyc r hxy.symm)
  · by_cases hyc : y ∈ Set.range c
    · obtain ⟨s, rfl⟩ := hyc
      exact hyA ((hAmem s).mpr (hcontained x hxc s hxy))
    · exact houtside x y hxc hyc hxy

end ErdosProblems.PathUpperReduction.TwoOutsiderCycleCover1105

noncomputable section

namespace ErdosProblems.PathUpperReduction.TwoHighDegreeCycleCover1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CycleContactCap1105
open ErdosProblems.PathUpperReduction.CycleCopy1105
open ErdosProblems.PathUpperReduction.TwoOutsiderCycleCover1105

/-- Only the actual queried outsider needs the original degree bound. -/
theorem actual_contact_card_and_successor_toggle_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (hsize : n + 3 = 2 * d)
    (hind : ∀ x y : V, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y)
    (z : V) (hz : z ∉ Set.range c) (hdegreez : d ≤ G.degree z) :
    (actualContacts G c z).card = d ∧
      ∀ i : Fin (n + 3), G.Adj z (c (i + 1)) ↔ ¬G.Adj z (c i) := by
  let N := actualContacts G c z
  have hdegree : N.card = G.degree z :=
    contact_card_eq_degree_of_outside_independence G c hind z hz
  have hN : d ≤ N.card := by rw [hdegree]; exact hdegreez
  have havoid : ∀ i ∈ N, finRotate (n + 3) i ∉ N := by
    intro i hi hnext
    have hzi : G.Adj z (c i) := (Finset.mem_filter.mp hi).2
    have hznext : G.Adj z (c (finRotate (n + 3) i)) :=
      (Finset.mem_filter.mp hnext).2
    rw [finRotate_apply] at hznext
    have hedge : (cycleGraph (n + 3)).Adj i (i + 1) := by
      simp [cycleGraph_adj]
    exact no_fresh_cycle_edge_contacts G d hconn hcard hfree c hsize
      i (i + 1) hedge z hz ⟨hzi, hznext⟩
  obtain ⟨_, _, hNcard, _, htoggle⟩ :=
    CycleHalfAlternation1105.half_partition_and_alternation
      (finRotate (n + 3)) N d (by simpa only [Fintype.card_fin] using hsize) hN havoid
  refine ⟨hNcard, ?_⟩
  intro i
  simpa only [finRotate_apply, N, actualContacts, Finset.mem_filter,
    Finset.mem_univ, true_and] using htoggle i

local instance {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-- An actual original cycle and two actual high-degree seed outsiders suffice.
The outside independence and both alternating contact sets are derived here. -/
theorem exists_actual_cover_of_cycle_and_two_high_degree_outsiders
    {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlength : C.length = 2 * d)
    (u v : V) (hu : u ∉ C.support) (hv : v ∉ C.support) (hne : u ≠ v)
    (hdegreeu : d ≤ G.degree u) (hdegreev : d ≤ G.degree v) :
    ∃ A : Finset V, A.card = d ∧ G.IsVertexCover (A : Set V) := by
  classical
  have hthree : 3 ≤ 2 * d := by
    rw [← hlength]
    exact hC.three_le_length
  let n : ℕ := 2 * d - 3
  have hsize : n + 3 = 2 * d := by dsimp only [n]; omega
  obtain ⟨c0, _henum, hrange0⟩ := exists_cycle_copy_with_exact_support G C hC
  obtain ⟨c, hrange⟩ :
      ∃ c : (cycleGraph (n + 3)).Copy G,
        Set.range c = {w | w ∈ C.support} := by
    rw [hsize, ← hlength]
    exact ⟨c0, hrange0⟩
  have hu' : u ∉ Set.range c := by
    rw [hrange]
    exact hu
  have hv' : v ∉ Set.range c := by
    rw [hrange]
    exact hv
  have hindC := ActualCycleOutside1105.outside_independent_of_actual_cycle
    G hconn d hfree C hC hlength
  have houtside : ∀ x y : V,
      x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y := by
    intro x y hx hy
    have hx' : x ∉ C.support := by
      intro hxC
      apply hx
      rw [hrange]
      exact hxC
    have hy' : y ∉ C.support := by
      intro hyC
      apply hy
      rw [hrange]
      exact hyC
    exact hindC x y hx' hy'
  have htoggleu := actual_contact_card_and_successor_toggle_of_degree
    G d hconn hcard hfree c hsize houtside u hu' hdegreeu
  have htogglev := actual_contact_card_and_successor_toggle_of_degree
    G d hconn hcard hfree c hsize houtside v hv' hdegreev
  have hfree' : (pathGraph (n + 5)).Free G := by
    have horder : n + 5 = 2 * d + 2 := by omega
    rw [horder]
    exact hfree
  exact exists_actual_cover_of_two_outsider_toggles G c hsize hfree'
    u v hu' hv' hne htoggleu.2 htogglev.2 houtside

end ErdosProblems.PathUpperReduction.TwoHighDegreeCycleCover1105
end
