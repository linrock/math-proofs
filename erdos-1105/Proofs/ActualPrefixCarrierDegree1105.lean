module

public import TracePrefixSlack1105
public import ActualTraceCarrierCut1105
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Actual prefix-carrier degree caller on SAME G/K/S. The ALL-step bound is the structural output of TracePrefixSlack1105, not
a supplied favorable occurrence or carrier degree. The carrier is chosen
internally by the actual trace cut; every retained vertex is handled. The literal-B capstone derives ONE kernel/trace/high-seed witness internally
and exports the carrier conclusion only in its explicit smaller-seed branch. No cycle, outside independence, ambient-degree equality or full path upper
theorem is claimed.
-/

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

