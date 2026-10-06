module

public import PathUpperOriginalGlobalComponentCouplingV4
public import PathOrdinaryComponentCharge
public import PathAllShortScalar

@[expose] public section

/-!
Actual all-short disconnected branch for the original
Fin q coloring and SAME full representative R. The all-short case below is a
structural predicate on every actual retained stage of the unchanged family;
it is stronger than the earlier no-P(k-2) result and is an explicit case input. The desired q bound, component counts, positive sizes, cut budget, stage/global
correspondence and vertex/edge totals are derived, not premises. Main endpoint
keeps n >= k >= 6; the k=5 branch is not claimed by this source.

First controls: b=0,T=1 satisfies Nat b <= T-2 but not b+2 <= T; therefore the
proper-first cover derives C0 >= 2 and T >= 2 before any subtraction conversion. Isolates contribute v=1,e=0 and charge one. A large star is P5-free but contains
P3, so at k=7 the no-P(k-2) theorem does not imply this all-short predicate.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- Ordinary P(d+1) freedom at every ACTUAL retained stage, with all literal
U/W/A/B and unchanged R preserved by the structural recursion. -/
def OriginalResidualCutFamily.AllRetainedPathFree
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ) : Prop :=
  match F with
  | .nil _ _ => True
  | .cons stage tail =>
      (pathGraph (d + 1)).Free stage.retainedGraph ∧ tail.AllRetainedPathFree d

/-- Each actual local piece retains its actual stage's all-short exclusion. -/
theorem OriginalResidualCutFamily.local_piece_path_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ)
    (hshort : F.AllRetainedPathFree d) (i : F.PieceIndex) :
    (pathGraph (d + 1)).Free (originalCutFamilyLocalPieceData F i).stage.retainedGraph := by
  revert hshort i
  induction F with
  | nil =>
      intro _ i
      exact PEmpty.elim i
  | cons stage tail ih =>
      intro hshort i
      change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
      change (pathGraph (d + 1)).Free stage.retainedGraph ∧
        tail.AllRetainedPathFree d at hshort
      cases i with
      | inl C => exact hshort.1
      | inr i => exact ih hshort.2 i

/-- Derive C0 >= 2,
then T >= 2 and b+2 <= T from the actual T=C0+b ledger, including zero cuts. -/
theorem OriginalResidualCutFamily.proper_first_cut_budget
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ) :
    2 ≤ Nat.card (selectedGraph χ R).ConnectedComponent ∧
      2 ≤ Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent ∧
      F.cutCount + 2 ≤
        Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent := by
  have hsequence := F.toGreedySequence
  have hxs : xs ≠ [] := by
    intro hempty
    subst xs
    have hnil : Set.univ \ componentSupport χ R x = ∅ := hsequence.2.2.2.1
    apply hproper
    ext v
    constructor
    · intro _
      exact Set.mem_univ v
    · intro _
      by_contra hv
      have houtside : v ∈ Set.univ \ componentSupport χ R x := ⟨Set.mem_univ v, hv⟩
      rw [hnil] at houtside
      exact houtside
  have hlength : 2 ≤ (x :: xs).length := by
    cases xs with
    | nil => exact (hxs rfl).elim
    | cons y ys => simp
  have hroots := residualGreedySequence_root_count χ R (x :: xs) hsequence
  have hcount := originalCutFamily_global_component_count F
  have hC0 : 2 ≤ Nat.card (selectedGraph χ R).ConnectedComponent := by omega
  exact ⟨hC0, by omega, by omega⟩

/-- Each ACTUAL global retained component inherits freedom by an injective
inclusion into its corresponding ACTUAL stage. Supports and graph restriction
are derived from the checked same-R coupling, rather than supplied. -/
theorem OriginalResidualCutFamily.global_component_path_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) (d : ℕ)
    (hshort : F.AllRetainedPathFree d)
    (C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent) :
    (pathGraph (d + 1)).Free C.toSimpleGraph := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  let i : F.PieceIndex := originalCutFamilyGlobalComponentCoupling F C
  let L := originalCutFamilyLocalPieceData F i
  have hsupp : C.supp = F.pieceSupport i := by
    have h := originalCutFamilyGlobalComponentCoupling_supp F i
    have hinv : (originalCutFamilyGlobalComponentCoupling F).symm i = C :=
      (originalCutFamilyGlobalComponentCoupling F).symm_apply_apply C
    rw [hinv] at h
    exact h
  have hinside : C.supp ⊆ L.stage.rootSupport := by
    intro v hv
    have hpiece : v ∈ F.pieceSupport i := hsupp ▸ hv
    rw [← originalCutFamily_local_piece_support F i] at hpiece
    obtain ⟨u, _hu, rfl⟩ := hpiece
    exact u.property
  let f : C.toSimpleGraph.Copy L.stage.retainedGraph := {
    toHom := {
      toFun := fun v => ⟨v.val, hinside v.property⟩
      map_rel' := by
        intro a b hab
        have hAdj : (H.induce L.stage.rootSupport).Adj
            ⟨a.val, hinside a.property⟩ ⟨b.val, hinside b.property⟩ := hab
        have hgraph : H.induce L.stage.rootSupport = L.stage.retainedGraph :=
          originalCutFamily_global_piece_stage_induce F i
        rw [hgraph] at hAdj
        exact hAdj
    }
    injective' := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun v : L.stage.rootSupport => (v : Fin n)) hab
  }
  rintro ⟨P⟩
  exact F.local_piece_path_free d hshort i ⟨f.comp P⟩

/-- Sum charges of the actual positive global components. The original q,
all isolated vertices, literal cuts, and actual T=C0+b budget are preserved. -/
theorem OriginalResidualCutFamily.original_all_short_charge
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (d : ℕ) (hd : 2 ≤ d) (hshort : F.AllRetainedPathFree d) :
    (q : ℝ) + 2 ≤ (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (n : ℝ) := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  let c : ℝ := ((d : ℝ) - 1) / 2 + 1 / (d : ℝ)
  have hpositive (C : H.ConnectedComponent) : 1 ≤ Nat.card C.supp := by
    obtain ⟨v, hv⟩ := C.nonempty_supp
    let _ : Nonempty C.supp := ⟨⟨v, hv⟩⟩
    have hpos : 0 < Nat.card C.supp := Nat.card_pos
    omega
  have hcharge (C : H.ConnectedComponent) :
      (Nat.card C.toSimpleGraph.edgeSet : ℝ) + 1 ≤ c * (Nat.card C.supp : ℝ) :=
    ordinary_component_charge_real C.toSimpleGraph d hd (hpositive C)
      (F.global_component_path_free d hshort C)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset H.ConnectedComponent))
    (fun C _ => hcharge C)
  have hsum' : ((∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet : ℕ) : ℝ) +
      (Nat.card H.ConnectedComponent : ℝ) ≤
      c * ((∑ C : H.ConnectedComponent, Nat.card C.supp : ℕ) : ℝ) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_sum, Nat.card_eq_fintype_card,
      Finset.mul_sum] using hsum
  have hvertices := originalCutFamily_global_component_vertex_sum F
  change (∑ C : H.ConnectedComponent, Nat.card C.supp) = n at hvertices
  rw [hvertices] at hsum'
  have hq := originalCutFamily_global_component_edge_sum F
  change q = (∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
    F.cutCount at hq
  have hqR : (q : ℝ) =
      ((∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet : ℕ) : ℝ) +
      (F.cutCount : ℝ) := by exact_mod_cast hq
  have hbudget := (F.proper_first_cut_budget hproper).2.2
  have hbudgetR : (F.cutCount : ℝ) + 2 ≤ (Nat.card H.ConnectedComponent : ℝ) := by
    exact_mod_cast hbudget
  change (q : ℝ) + 2 ≤ c * (n : ℝ)
  linarith

/-- Exact literal-formula bound on the ORIGINAL q in the actual all-short
disconnected case. No desired numeric bound or smaller-host IH is a premise. -/
theorem OriginalResidualCutFamily.original_color_count_le_formula_of_all_short
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)} {k : ℕ}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 6 ≤ k) (hkn : k ≤ n)
    (hshort : F.AllRetainedPathFree ((k - 2) / 2)) :
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  have hd : 2 ≤ (k - 2) / 2 := by omega
  exact all_short_color_count_le_pathFormula k n q hk hkn
    (F.original_all_short_charge hproper ((k - 2) / 2) hd hshort)

end ErdosProblems.PathUpperReduction
