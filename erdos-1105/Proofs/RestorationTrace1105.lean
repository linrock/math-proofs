module

public import CoreElimination
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Derives a minimum-degree-`d` kernel and reverse restoration trace from an
empty strict `d`-core and original unordered-edge deficit by cardinality
descent.
-/

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
