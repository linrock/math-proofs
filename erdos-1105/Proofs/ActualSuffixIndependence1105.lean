module

public import ActualPrefixCarrierDegree1105
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Original-cycle suffix induction on SAME G/S and the
actual restoration trace. No connectedness or equality of arbitrary carriers
is assumed. The structural cycle premise is to be constructed by the separate
actual-cycle acquisition caller on its SAME internally cut prefix A.
-/

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

