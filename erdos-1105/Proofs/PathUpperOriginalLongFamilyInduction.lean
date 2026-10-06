module

public import PathUpperOriginalNumericalIH
public import PathUpperOriginalFirstInduction
public import PathUpperOriginalLeafDomain
public import PathUpperOriginalCutFamilyV2

@[expose] public section

/-!
Conditional original long-component branch under the
FULL smaller-complete-host numerical induction hypothesis. The recursive
predicate below visits every ACTUAL stage of the SAME-R family, preserving
its literal U/W/A/B. It does not replace the family by favorable component
data or supply per-stage order, cardinality, tree, leaf or freshness premises. The final first component is explicitly proper; connected full-host and
all-short/middle branches remain separate from this result.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q k : ℕ}

/-- Every ACTUAL retained stage graph of this unchanged original cut family
excludes a path with k-2 vertices. Isolates and zero-cut stages are retained. -/
def OriginalResidualCutFamily.NoLongRetainedPath
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (k : ℕ) : Prop :=
  match F with
  | .nil _ _ => True
  | .cons stage tail =>
      (∀ _P : (pathGraph (k - 2)).Copy stage.retainedGraph, False) ∧
        OriginalResidualCutFamily.NoLongRetainedPath tail k

/-- Any ACTUAL later stage in the fixed first stage's SAME-R greedy sequence
is excluded by the FULL numerical IH. -/
theorem OriginalResidualCutStage.no_long_retained_path_of_roots_in_later_sequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    (hk : 5 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : ErdosProblems.PathLemmaFourScalar.pathFormula n k < q)
    {V : Set (Fin q)} {Z : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R V Z roots)
    (hroots : ∀ y ∈ roots, y ∈ xs) : F.NoLongRetainedPath k := by
  cases n with
  | zero => omega
  | succ m =>
      revert hroots
      induction F with
      | nil =>
          intro _
          trivial
      | @cons V Z y ys T tail ih =>
          intro hroots
          change (∀ _P : (pathGraph (k - 2)).Copy T.retainedGraph, False) ∧
            tail.NoLongRetainedPath k
          constructor
          · intro P
            have hy : y ∈ xs := hroots y (by simp)
            have hrestricted := S.last_leaf_restriction_of_later_retained_long_path
              hsequence hy T hk P hno
            exact original_high_color_count_false_of_full_smaller_host_IH
              k (m + 1) m q hIH hrestricted.1 (by omega) hrestricted.2 hhigh
          · apply ih
            intro z hz
            exact hroots z (List.mem_cons_of_mem y hz)

/-- Under the FULL smaller-host numerical IH and original high q, a proper
first component excludes a retained P(k-2) at EVERY actual stage. The initial
whole-prefix family supplies all later-stage ordering/membership data. -/
theorem OriginalResidualCutFamily.no_long_retained_path_of_proper_first_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 5 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : ErdosProblems.PathLemmaFourScalar.pathFormula n k < q) :
    F.NoLongRetainedPath k := by
  cases F with
  | cons S tail =>
      change (∀ _P : (pathGraph (k - 2)).Copy S.retainedGraph, False) ∧
        tail.NoLongRetainedPath k
      constructor
      · exact S.no_retained_long_path_of_proper_first_component
          hproper (by omega) hno hIH hhigh
      · have hsequence := (OriginalResidualCutFamily.cons S tail).toGreedySequence
        exact S.no_long_retained_path_of_roots_in_later_sequence
          hsequence hk hkn hno hIH hhigh tail (fun _ hy => hy)

end ErdosProblems.PathUpperReduction

