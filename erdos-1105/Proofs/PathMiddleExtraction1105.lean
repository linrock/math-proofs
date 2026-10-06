module

public import PathActualAllShort
public import PathUpperOriginalLongFamilyInduction
public import Mathlib.Data.Nat.Find

@[expose] public section

/-!
This module removes a supplied
middle-component witness under the explicit actual NoLongRetainedPath premise. It preserves the original chi, SAME R, full empty/univ family and actual global
retained graph.

Controls: a residual nil family cannot support full global/stage equivalence. At k=8, a bounded maximum of order5 in K6 does not imply P6-freedom. Therefore
the final global exclusion retains full empty/univ and actual P(k-2) freedom.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q k : ℕ}

/-- A positive-order ordinary path copy lies in an actual graph component,
with exactly its original vertex images. No longest-path assumption is used. -/
theorem middle_path_copy_in_actual_component
    {V : Type*} (G : SimpleGraph V) {m : ℕ} (hm : 0 < m)
    (P : (pathGraph m).Copy G) :
    ∃ C : G.ConnectedComponent, Nonempty ((pathGraph m).Copy C.toSimpleGraph) := by
  let j0 : Fin m := ⟨0, hm⟩
  let C : G.ConnectedComponent := G.connectedComponentMk (P j0)
  have hmem (j : Fin m) : P j ∈ C.supp := by
    apply (C.mem_supp_iff (P j)).mpr
    exact ConnectedComponent.sound
      ((pathGraph_preconnected m j j0).map P.toHom)
  let Q : (pathGraph m).Copy C.toSimpleGraph := {
    toHom := {
      toFun := fun j => ⟨P j, hmem j⟩
      map_rel' := by
        intro i j hij
        exact P.toHom.map_rel' hij
    }
    injective' := by
      intro i j hij
      exact P.injective (congrArg (fun v : C.supp => (v : V)) hij)
  }
  exact ⟨C, ⟨Q⟩⟩

/-- The checked recursive P(k-2) exclusion is exactly the all-stage freedom
predicate at d=k-3, with subtraction justified in the original order range. -/
theorem OriginalResidualCutFamily.all_retained_path_free_of_no_long
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots)
    (hk : 3 ≤ k) (hlong : F.NoLongRetainedPath k) :
    F.AllRetainedPathFree (k - 3) := by
  have horder : (k - 3) + 1 = k - 2 := by omega
  revert hlong
  induction F with
  | nil =>
      intro _
      trivial
  | cons stage tail ih =>
      intro hlong
      change (∀ _P : (pathGraph (k - 2)).Copy stage.retainedGraph, False) ∧
        tail.NoLongRetainedPath k at hlong
      change (pathGraph ((k - 3) + 1)).Free stage.retainedGraph ∧
        tail.AllRetainedPathFree (k - 3)
      constructor
      · rintro ⟨P⟩
        rw [horder] at P
        exact hlong.1 P
      · exact ih hlong.2

/-- Failure of the recursive all-short predicate gives a copy in an actual
stored stage, identified by an actual piece index. All U/W updates stay literal. -/
theorem OriginalResidualCutFamily.exists_piece_stage_copy_of_not_all_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ)
    (hfail : ¬ F.AllRetainedPathFree d) :
    ∃ i : F.PieceIndex,
      Nonempty ((pathGraph (d + 1)).Copy
        (originalCutFamilyLocalPieceData F i).stage.retainedGraph) := by
  classical
  revert hfail
  induction F with
  | nil =>
      intro hfail
      exact (hfail trivial).elim
  | cons stage tail ih =>
      intro hfail
      change ¬ ((pathGraph (d + 1)).Free stage.retainedGraph ∧
        tail.AllRetainedPathFree d) at hfail
      by_cases hhead : (pathGraph (d + 1)).Free stage.retainedGraph
      · have htail : ¬ tail.AllRetainedPathFree d := fun ht => hfail ⟨hhead, ht⟩
        obtain ⟨i, ⟨P⟩⟩ := ih htail
        exact ⟨Sum.inr i, ⟨P⟩⟩
      · obtain ⟨P⟩ := SimpleGraph.not_free.mp hhead
        let j0 : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
        exact ⟨Sum.inl (stage.retainedGraph.connectedComponentMk (P j0)), ⟨P⟩⟩

/-- Every failing actual stage path survives in the literal global graph and
then lies in one of its actual components. This one-way seed implication also
holds for residual families; it asserts no converse for their global graphs. -/
theorem OriginalResidualCutFamily.exists_global_component_copy_of_not_all_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ)
    (hfail : ¬ F.AllRetainedPathFree d) :
    ∃ C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent,
      Nonempty ((pathGraph (d + 1)).Copy C.toSimpleGraph) := by
  obtain ⟨i, ⟨P⟩⟩ := F.exists_piece_stage_copy_of_not_all_free d hfail
  let L := originalCutFamilyLocalPieceData F i
  let H := originalCutFamilyGlobalRetainedGraph F
  have hgraph : H.induce L.stage.rootSupport = L.stage.retainedGraph :=
    originalCutFamily_global_piece_stage_induce F i
  let inc : L.stage.retainedGraph.Copy H := {
    toHom := {
      toFun := fun v => v.val
      map_rel' := by
        intro u v huv
        have hind : (H.induce L.stage.rootSupport).Adj u v := by
          rw [hgraph]
          exact huv
        exact hind
    }
    injective' := Subtype.val_injective
  }
  exact middle_path_copy_in_actual_component H (Nat.succ_pos d) (inc.comp P)

/-- Actual full-family case extraction: either every stage is all-short, or
an actual global component supplies precisely the middle interval, a real Pa
copy and next-order freedom. The maximum is constructed, never supplied. -/
theorem OriginalResidualCutFamily.all_short_or_middle_component_of_no_long
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ roots)
    (hk : 8 ≤ k) (hlong : F.NoLongRetainedPath k) :
    F.AllRetainedPathFree ((k - 2) / 2) ∨
      ∃ (C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent) (a : ℕ),
        (k - 2) / 2 + 1 ≤ a ∧ a ≤ k - 3 ∧
        Nonempty ((pathGraph a).Copy C.toSimpleGraph) ∧
        (pathGraph (a + 1)).Free C.toSimpleGraph := by
  classical
  by_cases hshort : F.AllRetainedPathFree ((k - 2) / 2)
  · exact Or.inl hshort
  · obtain ⟨C, hseed⟩ :=
      F.exists_global_component_copy_of_not_all_free ((k - 2) / 2) hshort
    let P : ℕ → Prop := fun t => Nonempty ((pathGraph t).Copy C.toSimpleGraph)
    let a : ℕ := Nat.findGreatest P (k - 3)
    have hseed' : P ((k - 2) / 2 + 1) := hseed
    have hseed_bound : (k - 2) / 2 + 1 ≤ k - 3 := by omega
    have hlower : (k - 2) / 2 + 1 ≤ a := Nat.le_findGreatest hseed_bound hseed'
    have hupper : a ≤ k - 3 := Nat.findGreatest_le (P := P) (k - 3)
    have hcopy : P a := Nat.findGreatest_spec hseed_bound hseed'
    have hboundary : (pathGraph ((k - 3) + 1)).Free C.toSimpleGraph :=
      F.global_component_path_free (k - 3)
        (F.all_retained_path_free_of_no_long (by omega) hlong) C
    have hfree : (pathGraph (a + 1)).Free C.toSimpleGraph := by
      intro hnext
      by_cases hlt : a < k - 3
      · exact Nat.findGreatest_is_greatest (P := P)
          (show Nat.findGreatest P (k - 3) < a + 1 from by change a < a + 1; omega)
          (by omega) hnext
      · have heq : a + 1 = (k - 3) + 1 := by omega
        rw [heq] at hnext
        exact hboundary hnext
    exact Or.inr ⟨C, a, hlower, hupper, hcopy, hfree⟩

end ErdosProblems.PathUpperReduction
