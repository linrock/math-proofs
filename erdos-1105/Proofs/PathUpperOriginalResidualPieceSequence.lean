module

public import PathUpperOriginalResidualPiecesV2
public import PathUpperResidualGreedyRecursion

@[expose] public section

/-!
enrich the SAME-final-full-R residual greedy sequence
with the ENTIRE existing actual retained-piece certificate at every cons. No desired cuts, partitions, counts, connected R, blanket freshness, global
edge ledger or numerical upper bound is assumed or claimed. Empty cuts and
singleton empty-palette stages are retained.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- The entire exact existential conclusion of the existing one-stage API.
The actual original A/B owners, cut cover, outgoing boundary, zero-cut branch,
counts, component supports and all intrinsic/host size facts are retained. -/
def OriginalResidualStagePieceCertificate
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) : Prop :=
    ∃ (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
      (B : Finset (Sym2 (componentSupport χ r x))),
    let D := OriginalResidualRetainedGraph χ r (componentSupport χ r x) B
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ r x) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    B.card = A.card ∧
    (B : Set (Sym2 (componentSupport χ r x))) =
      OriginalResidualColorDeletion χ r U (componentSupport χ r x)
        (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))) ∧
    (B : Set (Sym2 (componentSupport χ r x))) ⊆
      ((selectedGraph χ r).induce (componentSupport χ r x)).edgeSet ∧
    (∀ b ∈ B, ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge b) ∧
    (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
      c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
    (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
      ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
      ¬ D.Reachable z w →
      ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
      χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
        ⟨χ e, hc⟩ ∈ A) ∧
    ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B.Nonempty) ∧
    (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B = ∅) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ r x) → B.Nonempty) ∧
    Nat.card D.ConnectedComponent = B.card + 1 ∧
    Nat.card D.ConnectedComponent = A.card + 1 ∧
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = componentSupport χ r x ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card (componentSupport χ r x)

/-- All original head premises and the actual existential stage certificate
at EVERY cons of ONE full R. Freeze the WHOLE component palette/support,
rather than merely its cut palette. Nil retains the original terminal facts. -/
def OriginalResidualPieceSequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) :
    Set (Fin q) → Set (Fin n) → List (Fin n) → Prop
  | U, W, [] => W = ∅ ∧ ResidualSlotPartition χ R U W
  | U, W, x :: xs =>
      x ∈ W ∧ ResidualSlotPartition χ R U W ∧
      ResidualLexMaximum χ R U W x ∧
      OriginalResidualStagePieceCertificate χ R U W x ∧
      OriginalResidualPieceSequence χ R
        (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) xs

/-- Every certified SAME-R greedy sequence admits
the full existing original retained-piece certificate at every stage. -/
theorem residualGreedySequence_original_piece_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W roots) :
    OriginalResidualPieceSequence χ R U W roots := by
  induction roots generalizing U W with
  | nil => exact hsequence
  | cons x xs ih =>
    rcases hsequence with ⟨hx, hpartition, hmax, htail⟩
    have hcomponent : componentSupport χ R x ⊆ W :=
      componentSupport_subset_of_residualSlotPartition χ R U W hpartition x hx
    have hstage : OriginalResidualStagePieceCertificate χ R U W x :=
      exists_original_residual_actual_retained_pieces
        χ R U W hpartition x hcomponent hmax
    exact ⟨hx, hpartition, hmax, hstage,
      ih (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) htail⟩

/-- From any valid original full representative,
derive a SAME-final-full-R enriched sequence. The existing actual whole
component coverage and disjointness conclusions are unchanged. -/
theorem exists_full_original_residual_piece_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n)),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  obtain ⟨R, roots, hsequence, hcover, hdisjoint⟩ :=
    exists_full_original_residual_greedy_sequence χ r
  exact ⟨R, roots, hsequence,
    residualGreedySequence_original_piece_sequence χ R ∅ Set.univ roots hsequence,
    hcover, hdisjoint⟩

end ErdosProblems.PathUpperReduction
