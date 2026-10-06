module

public import SeedFillCycleClosure1105
public import ActualNestedPrefixGuards1105
public import KernelCycleInsertion1105
public import CycleCopy1105
public import CoreSizeUpper1105
public import Mathlib.Data.Fintype.EquivFin
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Construct a cycle on EVERY actual prefix of the
same restoration trace after filling only original seed pairs. The final
original-graph reversal and carrier transport remain separate obligations. No supplied cycle, cover, contact count, chord or filling order occurs here. The strict-B capstone below obtains the actual prefix and its step guards
internally. It concludes a filled-graph cycle, not an original-graph cycle.
-/

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

