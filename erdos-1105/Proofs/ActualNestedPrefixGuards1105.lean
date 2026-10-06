module

public import ActualPrefixCarrierDegree1105
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Derive the recorded earlier degrees needed by
cycle insertion on internally selected, nested actual prefixes. A degree in
the final carrier is not substituted for the degree at an actual constructor. The public endpoint takes only original strict-B inputs and keeps the explicit
small-kernel branch. Cycle construction and full path(ii) remain separate.
-/

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

