module

public import PathUpperOriginalBridgeEdgeCap
public import PathUpperOriginalPrefixInduction
public import PathUpperOriginalNumericalIH

@[expose] public section

/-!
Actual proper-FIRST-head full original palette restriction,
its literal smaller-host domain, and the long-retained-path contradiction under
the FULL smaller-complete-host numerical induction hypothesis.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open ErdosProblems.PathLemmaFourScalar

variable {n q : ℕ}

/-- Canonical inclusion of a finite nonempty actual support, indexed by its
literal Nat.card. Positivity will be derived by the actual first-head caller. -/
noncomputable def originalHeadCardEmbedding
    (X : Set (Fin n)) (hcard : Nat.card X ≠ 0) :
    Fin (Nat.card X) ↪ Fin n :=
  (Nat.equivFinOfCardPos hcard).symm.toEmbedding.trans
    (Function.Embedding.subtype (fun v : Fin n => v ∈ X))

/-- The indexing inclusion covers exactly the actual support. -/
theorem originalHeadCardEmbedding_range
    (X : Set (Fin n)) (hcard : Nat.card X ≠ 0) :
    Set.range (originalHeadCardEmbedding X hcard) = X := by
  classical
  let e : X ≃ Fin (Nat.card X) := Nat.equivFinOfCardPos hcard
  apply Set.ext
  intro v
  constructor
  · rintro ⟨j, rfl⟩
    exact (e.symm j).property
  · intro hv
    refine ⟨e ⟨v, hv⟩, ?_⟩
    change (e.symm (e ⟨v, hv⟩)).val = v
    exact congrArg Subtype.val (e.symm_apply_apply ⟨v, hv⟩)

/-- From an ACTUAL proper first retained P(k-2), derive
an actual support-indexing embedding, ALL original colors, original no-rainbow
copies, the literal anti-Ramsey witness, and BOTH full smaller-host domains. No embedding, restricted palette, desired count, or domain is a premise. -/
theorem OriginalResidualCutStage.first_head_full_palette_induction_bundle
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (hq : (k - 2).choose 2 + 1 < q) :
    ∃ i : Fin (Nat.card (componentSupport χ R x)) ↪ Fin n,
      Set.range i = componentSupport χ R x ∧
      Function.Surjective (originalPrefixRestrictedColoring χ i) ∧
      (∀ F : (pathGraph k).Copy
        (⊤ : SimpleGraph (Fin (Nat.card (componentSupport χ R x)))),
        ¬ IsRainbow F.toHom (originalPrefixRestrictedColoring χ i)) ∧
      q ≤ antiRamseyNum (pathGraph k) (Nat.card (componentSupport χ R x)) ∧
      k ≤ Nat.card (componentSupport χ R x) ∧
      Nat.card (componentSupport χ R x) < n := by
  classical
  have hdomain :=
    S.first_head_full_induction_domain_of_retained_path_order hproper hk P hno hq
  have hcard : Nat.card (componentSupport χ R x) ≠ 0 := by omega
  let i := originalHeadCardEmbedding (componentSupport χ R x) hcard
  have hrange : Set.range i = componentSupport χ R x :=
    originalHeadCardEmbedding_range (componentSupport χ R x) hcard
  have htail := S.uncut_tail_edgeless_of_retained_path_order hk P hno
  have howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val := by
    intro c
    rw [hrange]
    simpa only [Set.compl_univ, Set.empty_union] using
      S.owner_inside_processed_prefix htail c
  have hfull := originalPrefixRestrictedColoring_full_witness
    (pathGraph k) χ R i howners hno
  exact ⟨i, hrange, hfull.1, hfull.2.1, hfull.2.2, hdomain.1, hdomain.2⟩

/-- The original high-color numerical hypothesis excludes
an actual long path in a proper FIRST retained piece, under FULL smaller-host IH. -/
theorem OriginalResidualCutStage.false_of_proper_first_retained_path_and_full_IH
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : pathFormula n k < q) : False := by
  have hq : (k - 2).choose 2 + 1 < q :=
    lt_of_le_of_lt (pathFormula_first_term_le k n) hhigh
  obtain ⟨_, _, _, _, hcount, hkm, hmn⟩ :=
    S.first_head_full_palette_induction_bundle hproper hk P hno hq
  exact original_high_color_count_false_of_full_smaller_host_IH
    k n (Nat.card (componentSupport χ R x)) q hIH hkm hmn hcount hhigh

/-- No favorable first-head path is supplied: every actual
retained P(k-2) is impossible in the literal original high-color induction step. The later-family caller may derive first-head properness from its actual tail. -/
theorem OriginalResidualCutStage.no_retained_long_path_of_proper_first_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : pathFormula n k < q) :
    ∀ _P : (pathGraph (k - 2)).Copy S.retainedGraph, False := by
  intro P
  exact S.false_of_proper_first_retained_path_and_full_IH
    hproper hk P hno hIH hhigh

end ErdosProblems.PathUpperReduction
