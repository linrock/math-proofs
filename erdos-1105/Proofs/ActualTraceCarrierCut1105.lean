module

public import RestorationTraceLedgers1105
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Cut the SAME actual restoration trace at any
internally constructed feasible cardinality. No caller-selected prefix,
order/list, support, degree or charge oracle is added. Prop induction only. Restricted-degree monotonicity requires explicit actual support inclusion;
late-outside independence and full fixed-carrier retention remain separate.
-/

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
inclusion. It does not assert that an arbitrary carrier retains neighbors. -/
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

