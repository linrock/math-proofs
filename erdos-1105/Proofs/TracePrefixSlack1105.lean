module

public import OriginalThresholdTraceHighSeed1105
public import RestorationTraceLedgers1105
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Literal-threshold slack and EVERY actual restoration
step, represented by Prop-valued actual prefix/suffix traces on SAME G. No caller deficit, degree, chosen order/list, favorable prefix or positivity
oracle is introduced. Not full #1105.
-/

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

