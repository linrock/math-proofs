module

public import ActualPrefixFilledCycle1105
public import ActualInducedDegree1105
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.EquivFin
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Reverse precisely the seed filling on the ACTUAL
2d carrier, retaining every carrier vertex including isolates and the SAME
original graph. The original strict-B capstone derives kernel, actual prefix,
recorded degree guards, filled cycle and reversal degree thresholds internally. It concludes an ORIGINAL cycle copy with exact prefix support.
-/

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

