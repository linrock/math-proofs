module

public import PathUpperOriginalComponentLedger
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
Extracts simultaneous `A`/`B` witnesses from the all-stage certificate. An
indexed recursive data chain fixes every original prefix and whole support,
with piece carriers given by the deleted-component carriers (including isolates).
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- The complete existing one-stage payload, with its ACTUAL A/B exposed.
This is the body of OriginalResidualStagePieceCertificate after its two
existential binders, with every original field and both letI bindings retained. -/
def OriginalResidualCutStagePayload
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n)
    (A : Finset (EligibleInteriorColor χ U (componentSupport χ R x)))
    (B : Finset (Sym2 (componentSupport χ R x))) : Prop :=
    let D := OriginalResidualRetainedGraph χ R (componentSupport χ R x) B
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    B.card = A.card ∧
    (B : Set (Sym2 (componentSupport χ R x))) =
      OriginalResidualColorDeletion χ R U (componentSupport χ R x)
        (A : Set (EligibleInteriorColor χ U (componentSupport χ R x))) ∧
    (B : Set (Sym2 (componentSupport χ R x))) ⊆
      ((selectedGraph χ R).induce (componentSupport χ R x)).edgeSet ∧
    (∀ b ∈ B, ((selectedGraph χ R).induce (componentSupport χ R x)).IsBridge b) ∧
    (∀ c : EligibleInteriorColor χ U (componentSupport χ R x),
      c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ R x) → c ∈ A) ∧
    (∀ (f : HostEdge n), EdgeInside (componentSupport χ R x) f.val → χ f ∉ U →
      ∀ z w : componentSupport χ R x, f.val = s(z.val, w.val) →
      ¬ D.Reachable z w →
      ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ R x), ⟨χ f, hc⟩ ∈ A) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ R x → y ∈ W → y ∉ componentSupport χ R x →
      χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ R x),
        ⟨χ e, hc⟩ ∈ A) ∧
    ((commonEligibleInteriorColors χ U (componentSupport χ R x)).Nonempty → B.Nonempty) ∧
    (¬ (commonEligibleInteriorColors χ U (componentSupport χ R x)).Nonempty → B = ∅) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ R x) → B.Nonempty) ∧
    Nat.card D.ConnectedComponent = B.card + 1 ∧
    Nat.card D.ConnectedComponent = A.card + 1 ∧
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ componentSupport χ R x) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = componentSupport χ R x ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ R x) ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card (componentSupport χ R x)

/-- The exposed cut sets carry the whole existing certificate for THESE choices. -/
structure OriginalResidualCutStage
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) where
  root_mem : x ∈ W
  partition : ResidualSlotPartition χ R U W
  maximum : ResidualLexMaximum χ R U W x
  A : Finset (EligibleInteriorColor χ U (componentSupport χ R x))
  B : Finset (Sym2 (componentSupport χ R x))
  payload : OriginalResidualCutStagePayload χ R U W x A B

def OriginalResidualCutStage.root
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (_S : OriginalResidualCutStage χ R U W x) : Fin n := x

def OriginalResidualCutStage.rootSupport
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (_S : OriginalResidualCutStage χ R U W x) : Set (Fin n) := componentSupport χ R x

def OriginalResidualCutStage.retainedGraph
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) : SimpleGraph (componentSupport χ R x) :=
  OriginalResidualRetainedGraph χ R (componentSupport χ R x) S.B

/-- The next stage is indexed by the WHOLE frozen palette and support.
The exposed constructor permits a later literal lifted-cut recursion. -/
inductive OriginalResidualCutFamily
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) :
    Set (Fin q) → Set (Fin n) → List (Fin n) → Type
  | nil {U W} (empty : W = ∅) (partition : ResidualSlotPartition χ R U W) :
      OriginalResidualCutFamily χ R U W []
  | cons {U W x xs} (stage : OriginalResidualCutStage χ R U W x)
      (tail : OriginalResidualCutFamily χ R
        (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) xs) :
      OriginalResidualCutFamily χ R U W (x :: xs)

/-- Choose A/B recursively from the derived EXISTENTIAL
stage certificates. Classical.choose performs the Prop-to-data extraction;
no desired witnesses, counts or family are supplied. -/
noncomputable def originalCutFamilyOfPieceSequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : OriginalResidualPieceSequence χ R U W roots) :
    OriginalResidualCutFamily χ R U W roots := by
  classical
  induction roots generalizing U W with
  | nil => exact .nil hsequence.1 hsequence.2
  | cons x xs ih =>
    let hstage := hsequence.2.2.2.1
    let A := Classical.choose hstage
    let B := Classical.choose (Classical.choose_spec hstage)
    let stage : OriginalResidualCutStage χ R U W x :=
      { root_mem := hsequence.1
        partition := hsequence.2.1
        maximum := hsequence.2.2.1
        A := A
        B := B
        payload := Classical.choose_spec (Classical.choose_spec hstage) }
    exact .cons stage
      (ih (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) hsequence.2.2.2.2)

/-- Recover the FULL original all-stage certificate
for this exact data family; no stage's original payload is lost. -/
theorem originalCutFamily_piece_sequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalResidualPieceSequence χ R U W roots := by
  induction F with
  | nil empty partition => exact ⟨empty, partition⟩
  | cons stage tail ih =>
    exact ⟨stage.root_mem, stage.partition, stage.maximum,
      ⟨stage.A, stage.B, stage.payload⟩, ih⟩

/-- Public method spelling for recovery of the complete original piece sequence. -/
theorem OriginalResidualCutFamily.toPieceSequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalResidualPieceSequence χ R U W roots :=
  originalCutFamily_piece_sequence F

/-- Recover the actual greedy sequence directly from
the data chain's original head premises and exact whole-prefix tail. -/
theorem OriginalResidualCutFamily.toGreedySequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ResidualGreedySequence χ R U W roots := by
  induction F with
  | nil empty partition => exact ⟨empty, partition⟩
  | cons stage tail ih =>
    exact ⟨stage.root_mem, stage.partition, stage.maximum, ih⟩

/-- The ACTUAL retained-component index family, with no manufactured pieces.
At nil it is empty; at cons it contains every actual deleted-graph component. -/
def OriginalCutFamilyPieceIndex
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Type :=
  match F with
  | .nil _ _ => PEmpty
  | .cons stage tail => stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail

noncomputable instance originalCutFamilyPieceIndexFintype
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Fintype (OriginalCutFamilyPieceIndex F) := by
  classical
  induction F with
  | nil =>
    change Fintype PEmpty
    exact inferInstance
  | cons stage tail ih =>
    letI : Fintype (OriginalCutFamilyPieceIndex tail) := ih
    change Fintype (stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail)
    exact inferInstance

/-- Literal ACTUAL per-stage B.card sum; the genuine-prefix tail remains
exposed in F.cons for the later original host lifted-edge union. -/
def originalCutFamilyCutTotal
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : ℕ :=
  match F with
  | .nil _ _ => 0
  | .cons stage tail => stage.B.card + originalCutFamilyCutTotal tail

def originalCutFamilyPieceSupport
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalCutFamilyPieceIndex F → Set (Fin n) :=
  match F with
  | .nil _ _ => fun i => PEmpty.elim i
  | .cons _stage tail => Sum.elim (fun C => originalResidualHostPiece C)
      (originalCutFamilyPieceSupport tail)

noncomputable def originalCutFamilyPieceSize
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalCutFamilyPieceIndex F → ℕ :=
  match F with
  | .nil _ _ => fun i => PEmpty.elim i
  | .cons _stage tail => Sum.elim (fun C => Nat.card C.supp) (originalCutFamilyPieceSize tail)

noncomputable def originalCutFamilyTotalPieceSize
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : ℕ :=
  ∑ i : OriginalCutFamilyPieceIndex F, originalCutFamilyPieceSize F i

/-- Concise public data methods for the later literal lifted-cut recursion. -/
abbrev OriginalResidualCutFamily.PieceIndex
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Type := OriginalCutFamilyPieceIndex F

abbrev OriginalResidualCutFamily.cutCount
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : ℕ := originalCutFamilyCutTotal F

noncomputable abbrev OriginalResidualCutFamily.pieceSize
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : F.PieceIndex → ℕ :=
  originalCutFamilyPieceSize F

abbrev OriginalResidualCutFamily.pieceSupport
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : F.PieceIndex → Set (Fin n) :=
  originalCutFamilyPieceSupport F

theorem originalCutStage_component_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    Nat.card S.retainedGraph.ConnectedComponent = S.B.card + 1 := by
  have h := S.payload
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hcount, _⟩
  exact hcount

theorem originalCutStage_vertex_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel S.retainedGraph.Adj := Classical.decRel _
    (∑ C : S.retainedGraph.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ R x) := by
  have h := S.payload
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum, _⟩
  exact hsum

theorem OriginalResidualCutStage.actual_edges
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    (S.B : Set (Sym2 (componentSupport χ R x))) ⊆
      ((selectedGraph χ R).induce (componentSupport χ R x)).edgeSet := by
  have h := S.payload
  rcases h with ⟨_, _, hedges, _⟩
  exact hedges

theorem OriginalResidualCutStage.support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) : S.rootSupport ⊆ W :=
  componentSupport_subset_of_residualSlotPartition χ R U W S.partition x S.root_mem

theorem OriginalResidualCutStage.component_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    Nat.card S.retainedGraph.ConnectedComponent = S.B.card + 1 :=
  originalCutStage_component_count S

theorem OriginalResidualCutStage.intrinsic_size_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel S.retainedGraph.Adj := Classical.decRel _
    (∑ C : S.retainedGraph.ConnectedComponent, Nat.card C.supp) = Nat.card S.rootSupport :=
  originalCutStage_vertex_sum S

theorem OriginalResidualCutStage.host_size_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel S.retainedGraph.Adj := Classical.decRel _
    (∑ C : S.retainedGraph.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card S.rootSupport := by
  have h := S.payload
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum⟩
  exact hsum

/-- T is the cardinality of the ACTUAL dependent piece
carrier, not a supplied abstract counter. Every zero-cut stage contributes one. -/
theorem originalCutFamily_piece_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    Nat.card (OriginalCutFamilyPieceIndex F) = roots.length + originalCutFamilyCutTotal F := by
  induction F with
  | nil => simp [OriginalCutFamilyPieceIndex, originalCutFamilyCutTotal]
  | cons stage tail ih =>
    simp only [OriginalCutFamilyPieceIndex, Nat.card_sum, originalCutFamilyCutTotal,
      List.length_cons]
    rw [originalCutStage_component_count stage, ih]
    omega

theorem originalCutFamily_piece_size_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    originalCutFamilyTotalPieceSize F =
      (roots.map (fun x => Nat.card (componentSupport χ R x))).sum := by
  classical
  induction F with
  | nil =>
    change (∑ i : PEmpty, (PEmpty.elim i : ℕ)) = 0
    exact Finset.sum_eq_zero fun i _ => PEmpty.elim i
  | @cons U W x xs stage tail ih =>
    change
      (∑ i : stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail,
        Sum.elim (fun C => Nat.card C.supp) (originalCutFamilyPieceSize tail) i) =
        Nat.card (componentSupport χ R x) +
          (xs.map (fun y => Nat.card (componentSupport χ R y))).sum
    rw [Fintype.sum_sumElim]
    rw [originalCutStage_vertex_sum stage]
    change Nat.card (componentSupport χ R x) + originalCutFamilyTotalPieceSize tail = _
    rw [ih]

/-- Public existence starts only from original chi/full r. The SAME final R and full initial certificates are retained; the ACTUAL data
family, T=c+b and total retained size n are derived, not assumed. -/
theorem exists_full_original_cut_family
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n))
      (F : OriginalResidualCutFamily χ R ∅ Set.univ roots),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      roots.length = Nat.card (selectedGraph χ R).ConnectedComponent ∧
      Nat.card (OriginalCutFamilyPieceIndex F) =
        Nat.card (selectedGraph χ R).ConnectedComponent + originalCutFamilyCutTotal F ∧
      originalCutFamilyTotalPieceSize F = n ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  obtain ⟨R, roots, hgreedy, hpieces, hcount, hsize, hcover, hdisjoint⟩ :=
    exists_full_original_component_ledger χ r
  let F := originalCutFamilyOfPieceSequence χ R ∅ Set.univ roots hpieces
  have hT : Nat.card (OriginalCutFamilyPieceIndex F) =
      Nat.card (selectedGraph χ R).ConnectedComponent + originalCutFamilyCutTotal F := by
    rw [originalCutFamily_piece_count F, hcount]
  have hS : originalCutFamilyTotalPieceSize F = n :=
    (originalCutFamily_piece_size_sum F).trans hsize
  exact ⟨R, roots, F, hgreedy, hpieces, hcount, hT, hS, hcover, hdisjoint⟩

end ErdosProblems.PathUpperReduction
