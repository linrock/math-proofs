module

public import RestorationTrace1105
public import HighSeedLedgerBridge1105
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
The original strict linear threshold internally supplies
the literal initial deficit. ONE actual trace peeler constructs K and Drem;
the actual high-seed bridge is then applied to THAT K and THAT Drem. All edge counts and degrees belong to the SAME original G and actual support.
-/

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

