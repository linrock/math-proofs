module

public import ConnectedComponentScalarCap1105
public import PathUpperOriginalPieceFreshness
public import PathActualAllShort
public import PathLemmaFourEnvelopeV2

@[expose] public section

/-!
Original SAME-R disconnected middle-component caller. The public endpoint retains arbitrary original chi/R, the actual full family,
proper first support, n >= k >= 8, original no-rainbow Pk, and ONE actual global
connected component containing Pa and excluding P(a+1) in the middle range. All tail path exclusions, positive component sizes including isolates, actual
edge/cut/vertex sums, cut budget and the original q+1 bound are derived.

K4 disjoint-union K2 remains
the falsifier against treating a whole disconnected retained stage as the head.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q k a : ℕ}

/-- Original-color disconnected middle case, on one ACTUAL retained
connected component. Tail exclusions, charges, counts and the original
palette bound are derived internally. No numerical IH is assumed. -/
theorem OriginalResidualCutFamily.original_color_count_le_formula_of_middle_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 8 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent)
    (A : (pathGraph a).Copy C.toSimpleGraph)
    (hheadFree : (pathGraph (a + 1)).Free C.toSimpleGraph)
    (hlower : (k - 2) / 2 + 1 ≤ a)
    (hupper : a ≤ k - 3) :
    q + 1 ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  let E := originalCutFamilyGlobalComponentCoupling F
  let S : Finset H.ConnectedComponent := Finset.univ.erase C
  let d : ℕ := k - a - 1
  let v : ℕ := Nat.card C.supp
  let u : ℕ := ∑ D ∈ S, Nat.card D.supp
  let eTail : ℕ := ∑ D ∈ S, Nat.card D.toSimpleGraph.edgeSet
  let c : ℝ := ((d : ℝ) - 1) / 2 + 1 / (d : ℝ)

  have ha4 : 4 ≤ a := by omega
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hda : d ≤ a := by dsimp [d]; omega
  have hak : a + d + 1 = k := by dsimp [d]; omega
  have hav : a ≤ v := by
    let f : Fin a → C.supp := fun j => ⟨(A j).val, (A j).property⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply A.injective
      apply Subtype.ext
      exact congrArg (fun z : C.supp => z.val) hij
    simpa only [v, Nat.card_fin] using
      Nat.card_le_card_of_injective f hf

  have hsupp (D : H.ConnectedComponent) :
      D.supp = F.pieceSupport (E D) := by
    have h := originalCutFamilyGlobalComponentCoupling_supp F (E D)
    change (E.symm (E D)).supp = F.pieceSupport (E D) at h
    simpa only [Equiv.symm_apply_apply] using h

  let includeC : C.toSimpleGraph.Copy H :=
    C.toSimpleGraph_hom.toCopy Subtype.val_injective
  let A0 : (pathGraph a).Copy H := includeC.comp A
  have hA0 : Set.range (fun j => A0 j) ⊆ F.pieceSupport (E C) := by
    rintro z ⟨j, rfl⟩
    rw [← hsupp C]
    exact (A j).property

  have hother (D : H.ConnectedComponent) (hDC : D ≠ C) :
      (pathGraph (d + 1)).Free D.toSimpleGraph := by
    rintro ⟨B⟩
    let includeD : D.toSimpleGraph.Copy H :=
      D.toSimpleGraph_hom.toCopy Subtype.val_injective
    let B0 : (pathGraph (d + 1)).Copy H := includeD.comp B
    have hB0 : Set.range (fun j => B0 j) ⊆ F.pieceSupport (E D) := by
      rintro z ⟨j, rfl⟩
      rw [← hsupp D]
      exact (B j).property
    have hij : E C ≠ E D := by
      intro h
      exact hDC (E.injective h).symm
    have hlt := originalCutFamily_two_piece_path_order_lt
      F hno (E C) (E D) hij (by omega) (by omega) A0 B0 hA0 hB0
    omega

  have hpositive (D : H.ConnectedComponent) : 1 ≤ Nat.card D.supp := by
    obtain ⟨z, hz⟩ := D.nonempty_supp
    let : Nonempty D.supp := ⟨⟨z, hz⟩⟩
    have hpos : 0 < Nat.card D.supp := Nat.card_pos
    omega

  have hcharge (D : H.ConnectedComponent) (hD : D ∈ S) :
      (Nat.card D.toSimpleGraph.edgeSet : ℝ) + 1 ≤
        c * (Nat.card D.supp : ℝ) := by
    have hDC : D ≠ C := (Finset.mem_erase.mp hD).1
    exact ordinary_component_charge_real D.toSimpleGraph d hd
      (hpositive D) (hother D hDC)

  have hsum := Finset.sum_le_sum (s := S) (fun D hD => hcharge D hD)
  have htail :
      (eTail : ℝ) + (S.card : ℝ) ≤ c * (u : ℝ) := by
    simpa only [eTail, u, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, Nat.cast_sum, Finset.mul_sum] using hsum

  have hhead :
      Nat.card C.toSimpleGraph.edgeSet ≤
        ErdosProblems.PathLemmaFourEnvelope.scalarCap a v :=
    ComponentScalarCap1105.connected_component_scalar_cap
      a ha4 C.toSimpleGraph A hheadFree C.connected_toSimpleGraph

  have heparts :
      Nat.card C.toSimpleGraph.edgeSet + eTail =
        ∑ D : H.ConnectedComponent, Nat.card D.toSimpleGraph.edgeSet := by
    dsimp [eTail, S]
    exact Finset.add_sum_erase Finset.univ
      (fun D : H.ConnectedComponent => Nat.card D.toSimpleGraph.edgeSet)
      (Finset.mem_univ C)

  have hvparts :
      v + u = ∑ D : H.ConnectedComponent, Nat.card D.supp := by
    dsimp [v, u, S]
    exact Finset.add_sum_erase Finset.univ
      (fun D : H.ConnectedComponent => Nat.card D.supp)
      (Finset.mem_univ C)

  have hvertices := originalCutFamily_global_component_vertex_sum F
  change (∑ D : H.ConnectedComponent, Nat.card D.supp) = n at hvertices
  have hvu : v + u = n := hvparts.trans hvertices

  have hq0 := originalCutFamily_global_component_edge_sum F
  change q =
    (∑ D : H.ConnectedComponent, Nat.card D.toSimpleGraph.edgeSet) +
      F.cutCount at hq0
  have hq :
      q = Nat.card C.toSimpleGraph.edgeSet + eTail + F.cutCount := by
    rw [← heparts] at hq0
    exact hq0

  have hcard :
      S.card + 1 = Nat.card H.ConnectedComponent := by
    simpa only [S, Finset.card_univ, Nat.card_eq_fintype_card] using
      (Finset.card_erase_add_one
        (s := (Finset.univ : Finset H.ConnectedComponent))
        (Finset.mem_univ C))
  have hbudget := (F.proper_first_cut_budget hproper).2.2
  change F.cutCount + 2 ≤ Nat.card H.ConnectedComponent at hbudget
  have hqNat :
      q + 1 ≤ Nat.card C.toSimpleGraph.edgeSet + eTail + S.card := by
    omega
  have hqReal :
      (q : ℝ) + 1 ≤
        (Nat.card C.toSimpleGraph.edgeSet : ℝ) +
          (eTail : ℝ) + (S.card : ℝ) := by
    exact_mod_cast hqNat
  have hheadReal :
      (Nat.card C.toSimpleGraph.edgeSet : ℝ) ≤
        (ErdosProblems.PathLemmaFourEnvelope.scalarCap a v : ℝ) := by
    exact_mod_cast hhead
  have hmiddle :
      (q : ℝ) + 1 ≤
        (ErdosProblems.PathLemmaFourEnvelope.scalarCap a v : ℝ) +
          c * (u : ℝ) := by
    linarith

  have henvelope :=
    ErdosProblems.PathLemmaFourEnvelope.scalar_affine_envelope
      a d v u hda hd hav (by omega)
  have hformula :
      ErdosProblems.PathLemmaFourEnvelope.pathFormula
          (v + u) (a + d + 1) =
        ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
    rw [hvu, hak]
    rfl
  rw [hformula] at henvelope
  have hfull :
      (q : ℝ) + 1 ≤
        (ErdosProblems.PathLemmaFourScalar.pathFormula n k : ℝ) :=
    hmiddle.trans henvelope
  exact_mod_cast hfull

end ErdosProblems.PathUpperReduction

