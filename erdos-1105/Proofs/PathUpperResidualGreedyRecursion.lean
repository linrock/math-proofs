module

public import PathUpperResidualGreedyStage
public import Mathlib.Data.List.Pairwise

@[expose] public section

/-!
Constructs a finite residual greedy sequence in one final full
original-color representative. All stage maxima and slot partitions are
derived by strong induction on the remaining vertex set `W`.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Every stage is anchored at the SAME full representative R.
The list ends exactly when the actual residual vertex set is empty. -/
def ResidualGreedySequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) :
    Set (Fin q) → Set (Fin n) → List (Fin n) → Prop
  | U, W, [] => W = ∅ ∧ ResidualSlotPartition χ R U W
  | U, W, x :: xs =>
      x ∈ W ∧ ResidualSlotPartition χ R U W ∧
      ResidualLexMaximum χ R U W x ∧
      ResidualGreedySequence χ R
        (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) xs

/-- Prefix equality transports the EXACT residual-family anchor.
The chosen component and its exact internal selected-edge Finset are frozen. -/
theorem residualLexMaximum_of_same_component_and_prefix
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r R : RepresentativeChoice χ) (U : Set (Fin q)) (W : Set (Fin n))
    (x : Fin n) (hprefix : ∀ c ∈ U, R.edge c = r.edge c)
    (hmax : ResidualLexMaximum χ r U W x)
    (hsupport : componentSupport χ R x = componentSupport χ r x)
    (hinternal : internalSelectedEdges χ R (componentSupport χ r x) =
      internalSelectedEdges χ r (componentSupport χ r x)) :
    ResidualLexMaximum χ R U W x := by
  constructor
  · intro t z hz
    let old : OriginalResidualChoice χ r U W :=
      { choice := t.choice
        prefix_eq := fun c hc => (t.prefix_eq c hc).trans (hprefix c hc)
        eligible_inside := t.eligible_inside }
    rw [hsupport]
    exact hmax.1 old z hz
  · intro t z hz hsize
    let old : OriginalResidualChoice χ r U W :=
      { choice := t.choice
        prefix_eq := fun c hc => (t.prefix_eq c hc).trans (hprefix c hc)
        eligible_inside := t.eligible_inside }
    have hsizeOld : (componentSupport χ old.choice z).ncard =
        (componentSupport χ r x).ncard := by
      rw [← hsupport]
      exact hsize
    rw [hsupport, hinternal]
    exact hmax.2 old z hz hsizeOld

/-- Next-stage literal slot admissibility plus whole-support equality also
freezes the exact selected-color set, including when that set is empty. -/
theorem residualSelectedComponentColors_eq_of_frozen_next
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n)
    (t : OriginalResidualChoice χ r
      (U ∪ residualSelectedComponentColors χ r x)
      (W \ componentSupport χ r x))
    (hsupport : componentSupport χ t.choice x = componentSupport χ r x) :
    residualSelectedComponentColors χ t.choice x =
      residualSelectedComponentColors χ r x := by
  ext c
  change EdgeInside (componentSupport χ t.choice x) (t.choice.edge c).val ↔
    EdgeInside (componentSupport χ r x) (r.edge c).val
  rw [hsupport]
  constructor
  · intro hc
    by_cases hfixed : c ∈ U ∪ residualSelectedComponentColors χ r x
    · rw [t.prefix_eq c hfixed] at hc
      exact hc
    · obtain ⟨⟨a, b⟩, hpair⟩ := Sym2.mk_surjective ((t.choice.edge c).val)
      have haOwner : a ∈ (t.choice.edge c).val := by
        rw [← hpair]
        exact Sym2.mem_mk_left a b
      exact ((t.eligible_inside c hfixed a haOwner).2 (hc a haOwner)).elim
  · intro hc
    have hcP : c ∈ residualSelectedComponentColors χ r x := hc
    rw [t.prefix_eq c (Or.inr hcP)]
    exact hc

/-- At EVERY certified stage, freezing its WHOLE component preserves the
literal support, induced graph, internal edge Finset and selected color owners
for ALL next admissible full choices. -/
theorem residualGreedySequence_head_freeze
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) (xs : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W (x :: xs)) :
    let X := componentSupport χ R x
    let P := residualSelectedComponentColors χ R x
    X ⊆ W ∧ Disjoint P U ∧
    ResidualSlotPartition χ R (U ∪ P) (W \ X) ∧
    (W \ X).ncard < W.ncard ∧
    ∀ t : OriginalResidualChoice χ R (U ∪ P) (W \ X),
      (∃ old : OriginalResidualChoice χ R U W, old.choice = t.choice) ∧
      componentSupport χ t.choice x = X ∧
      (selectedGraph χ t.choice).induce X = (selectedGraph χ R).induce X ∧
      internalSelectedEdges χ t.choice X = internalSelectedEdges χ R X ∧
      ∀ c ∈ P, t.choice.edge c = R.edge c := by
  exact residual_component_freeze_invariants χ R U W
    hsequence.2.1 x hsequence.1

/-- The actual whole components of the finite certificate cover EXACTLY
its starting residual vertices; isolated vertices are included. -/
theorem residualGreedySequence_covers
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W roots) :
    ∀ v, v ∈ W ↔ ∃ x ∈ roots, v ∈ componentSupport χ R x := by
  induction roots generalizing U W with
  | nil =>
    intro v
    rw [hsequence.1]
    simp
  | cons x xs ih =>
    have hx : x ∈ W := hsequence.1
    have hpartition : ResidualSlotPartition χ R U W := hsequence.2.1
    have htail := hsequence.2.2.2
    have hX : componentSupport χ R x ⊆ W :=
      componentSupport_subset_of_residualSlotPartition χ R U W hpartition x hx
    have hcoverTail := ih (U ∪ residualSelectedComponentColors χ R x)
      (W \ componentSupport χ R x) htail
    intro v
    constructor
    · intro hv
      by_cases hvX : v ∈ componentSupport χ R x
      · exact ⟨x, List.mem_cons_self, hvX⟩
      · obtain ⟨y, hy, hvY⟩ := (hcoverTail v).mp ⟨hv, hvX⟩
        exact ⟨y, List.mem_cons_of_mem x hy, hvY⟩
    · rintro ⟨y, hy, hvY⟩
      rcases List.mem_cons.mp hy with hyHead | hyTail
      · subst y
        exact hX hvY
      · exact ((hcoverTail v).mpr ⟨y, hyTail, hvY⟩).1

/-- Every certified component is disjoint from all later WHOLE components. -/
theorem residualGreedySequence_pairwise_disjoint
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W roots) :
    roots.Pairwise (fun x y =>
      Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  induction roots generalizing U W with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have htail := hsequence.2.2.2
    have hcoverTail := residualGreedySequence_covers χ R
      (U ∪ residualSelectedComponentColors χ R x)
      (W \ componentSupport χ R x) xs htail
    apply List.pairwise_cons.mpr
    constructor
    · intro y hy
      apply Set.disjoint_left.mpr
      intro v hvX hvY
      exact ((hcoverTail v).mpr ⟨y, hy, hvY⟩).2 hvX
    · exact ih (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) htail

/-- Actual strict remaining-vertex descent constructs a FINAL full choice
and a finite sequence. EVERY stage maximum and boundary is expressed using
that SAME final choice, with all initial U slots fixed to original r. -/
theorem exists_residual_greedy_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W) :
    ∃ (s : OriginalResidualChoice χ r U W) (roots : List (Fin n)),
      ResidualGreedySequence χ s.choice U W roots ∧
      (∀ v, v ∈ W ↔ ∃ x ∈ roots, v ∈ componentSupport χ s.choice x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ s.choice x) (componentSupport χ s.choice y)) := by
  classical
  have hrec : ∀ N : ℕ, ∀ (r : RepresentativeChoice χ)
      (U : Set (Fin q)) (W : Set (Fin n)), W.ncard = N →
      ResidualSlotPartition χ r U W →
      ∃ (s : OriginalResidualChoice χ r U W) (roots : List (Fin n)),
        ResidualGreedySequence χ s.choice U W roots := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro r U W hcard hpartition
      by_cases hW : W.Nonempty
      · obtain ⟨s, x, hx, hmax, _hpartitionS, _hX, _hdisjoint,
          hnext, hdecrease, hforall⟩ :=
          exists_residual_greedy_stage χ r U W hpartition hW
        have hsmaller : (W \ componentSupport χ s.choice x).ncard < N := by
          rw [← hcard]
          exact hdecrease
        obtain ⟨t, xs, htailOld⟩ :=
          ih (W \ componentSupport χ s.choice x).ncard hsmaller s.choice
            (U ∪ residualSelectedComponentColors χ s.choice x)
            (W \ componentSupport χ s.choice x) rfl hnext
        obtain ⟨⟨original, horiginal⟩, hsupport, _hgraph, hinternal, _hslots⟩ :=
          hforall t
        have hcolors :=
          residualSelectedComponentColors_eq_of_frozen_next χ s.choice U W x t hsupport
        have hpartitionFinal : ResidualSlotPartition χ t.choice U W := by
          have h := residualSlotPartition_of_admissibleChoice χ r U W hpartition original
          rw [horiginal] at h
          exact h
        have hmaxFinal : ResidualLexMaximum χ t.choice U W x :=
          residualLexMaximum_of_same_component_and_prefix χ s.choice t.choice U W x
            (fun c hc => t.prefix_eq c (Or.inl hc)) hmax hsupport hinternal
        have htail : ResidualGreedySequence χ t.choice
            (U ∪ residualSelectedComponentColors χ t.choice x)
            (W \ componentSupport χ t.choice x) xs := by
          rw [hcolors, hsupport]
          exact htailOld
        refine ⟨original, x :: xs, ?_⟩
        rw [horiginal]
        exact ⟨hx, hpartitionFinal, hmaxFinal, htail⟩
      · have hWempty : W = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr (fun v hv => hW ⟨v, hv⟩)
        let original : OriginalResidualChoice χ r U W :=
          { choice := r
            prefix_eq := fun _ _ => rfl
            eligible_inside := hpartition.eligible_inside }
        exact ⟨original, [], hWempty, hpartition⟩
  obtain ⟨s, roots, hsequence⟩ := hrec W.ncard r U W rfl hpartition
  exact ⟨s, roots, hsequence,
    residualGreedySequence_covers χ s.choice U W roots hsequence,
    residualGreedySequence_pairwise_disjoint χ s.choice U W roots hsequence⟩

/-- From ANY valid original full representative, derive one final full R
whose whole components cover ALL vertices and whose EVERY residual-prefix
stage is maximal in size, then internal edges. No positive n or nonempty
palette is imposed, and singleton empty-palette stages are retained. -/
theorem exists_full_original_residual_greedy_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n)),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  have hpartition : ResidualSlotPartition χ r ∅ Set.univ := by
    constructor
    · intro c hc
      exact hc.elim
    · intro _c _hc _v _hv
      trivial
  obtain ⟨s, roots, hsequence, hcover, hdisjoint⟩ :=
    exists_residual_greedy_sequence χ r ∅ Set.univ hpartition
  exact ⟨s.choice, roots, hsequence, fun v => (hcover v).mp (Set.mem_univ v),
    hdisjoint⟩

end ErdosProblems.PathUpperReduction
