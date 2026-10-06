module

public import PathPrefixMap
public import PathCliqueBridge

@[expose] public section

/-! The Erdős–Simonovits–Sós path lower construction, used in Yuan's formula:
a distinct color on each edge inside
the first `r` vertices, and one common fresh color on every other edge. -/

namespace ErdosProblems.PathCliqueLower

open SimpleGraph

abbrev RawColors (r : ℕ) : Type := ((⊤ : SimpleGraph (Fin r)).edgeSet) ⊕ PUnit

noncomputable def rawCliqueColor {r n : ℕ} (h : r ≤ n) :
    TopEdgeLabeling (Fin n) (RawColors r) :=
  fun e => if he : ∃ x : (⊤ : SimpleGraph (Fin r)).edgeSet,
      (prefixCopy h).mapEdgeSet x = e then
    Sum.inl (Classical.choose he) else Sum.inr PUnit.unit

theorem rawCliqueColor_on_prefix {r n : ℕ} (h : r ≤ n)
    (x : (⊤ : SimpleGraph (Fin r)).edgeSet) :
    rawCliqueColor h ((prefixCopy h).mapEdgeSet x) = Sum.inl x := by
  classical
  unfold rawCliqueColor
  split_ifs with he
  · have hx : Classical.choose he = x :=
      (prefixCopy h).mapEdgeSet.injective (Classical.choose_spec he)
    exact congrArg Sum.inl hx
  · exact False.elim (he ⟨x, rfl⟩)

theorem rawCliqueColor_get_outside {r n : ℕ} (h : r ≤ n)
    (a b : Fin n) (hab : a ≠ b) (hout : r ≤ a.val ∨ r ≤ b.val) :
    (rawCliqueColor h).get a b ((top_adj a b).2 hab) = Sum.inr PUnit.unit := by
  have hnot := prefix_edge_not_range h a b hab hout
  simp [EdgeLabeling.get, rawCliqueColor, hnot]

theorem rawCliqueColor_surjective {r n : ℕ} (h : r + 2 ≤ n) :
    Function.Surjective (rawCliqueColor (by omega : r ≤ n)) := by
  intro c
  cases c with
  | inl x =>
      exact ⟨(prefixCopy (by omega : r ≤ n)).mapEdgeSet x,
        rawCliqueColor_on_prefix (by omega : r ≤ n) x⟩
  | inr u =>
      let a : Fin n := ⟨r, by omega⟩
      let b : Fin n := ⟨r + 1, by omega⟩
      have hab : a ≠ b := by
        intro he
        have hv := congrArg Fin.val he
        dsimp [a, b] at hv
        omega
      refine ⟨⟨s(a, b), ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
        ((top_adj a b).2 hab)⟩, ?_⟩
      have hout : r ≤ a.val ∨ r ≤ b.val := Or.inl (by simp [a])
      simpa [EdgeLabeling.get, a, b] using
        rawCliqueColor_get_outside (by omega : r ≤ n) a b hab hout

theorem rawColors_card (r : ℕ) :
    Fintype.card (RawColors r) = r.choose 2 + 1 := by
  classical
  have hcard : Fintype.card ((⊤ : SimpleGraph (Fin r)).edgeSet) = r.choose 2 := by
    calc
      Fintype.card ((⊤ : SimpleGraph (Fin r)).edgeSet) =
          ((⊤ : SimpleGraph (Fin r)).edgeFinset).card := SimpleGraph.card_edgeSet
      _ = (Fintype.card (Fin r)).choose 2 :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
      _ = r.choose 2 := by simp
  change Fintype.card (((⊤ : SimpleGraph (Fin r)).edgeSet) ⊕ PUnit) =
    r.choose 2 + 1
  rw [Fintype.card_sum, hcard]
  simp

noncomputable def pathCliqueColor {r n : ℕ} (h : r ≤ n) :
    TopEdgeLabeling (Fin n) (Fin (r.choose 2 + 1)) :=
  fun e => Fin.cast (rawColors_card r)
    ((Fintype.equivFin (RawColors r)) (rawCliqueColor h e))

theorem pathCliqueColor_surjective {r n : ℕ} (h : r + 2 ≤ n) :
    Function.Surjective (pathCliqueColor (by omega : r ≤ n)) := by
  intro c
  let d : RawColors r := (Fintype.equivFin (RawColors r)).symm
    (Fin.cast (rawColors_card r).symm c)
  obtain ⟨e, he⟩ := rawCliqueColor_surjective h d
  refine ⟨e, ?_⟩
  change Fin.cast (rawColors_card r)
    ((Fintype.equivFin (RawColors r)) (rawCliqueColor (by omega : r ≤ n) e)) = c
  rw [he]
  simp [d]

noncomputable def freshFinColor (r : ℕ) : Fin (r.choose 2 + 1) :=
  Fin.cast (rawColors_card r)
    ((Fintype.equivFin (RawColors r)) (Sum.inr PUnit.unit))

theorem pathCliqueColor_get_outside {r n : ℕ} (h : r ≤ n)
    (a b : Fin n) (hab : a ≠ b) (hout : r ≤ a.val ∨ r ≤ b.val) :
    (pathCliqueColor h).get a b ((top_adj a b).2 hab) = freshFinColor r := by
  have hfresh := rawCliqueColor_get_outside h a b hab hout
  simpa [pathCliqueColor, freshFinColor, EdgeLabeling.get] using
    congrArg (fun c : RawColors r =>
      Fin.cast (rawColors_card r) ((Fintype.equivFin (RawColors r)) c)) hfresh

def admissiblePathCounts (r n : ℕ) : Set ℕ :=
  {m | ∃ χ : TopEdgeLabeling (Fin n) (Fin m), Function.Surjective χ ∧
    ∀ f : (pathGraph (r + 2)).Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ}

theorem admissiblePathCounts_bddAbove (r n : ℕ) :
    BddAbove (admissiblePathCounts r n) := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
  intro m hm
  obtain ⟨χ, hχ, _⟩ := hm
  simpa using Fintype.card_le_of_surjective χ hχ

/-- The clique construction gives the first term of the path lower bound
for every `r ≥ 3` and `n ≥ r + 2`. -/
theorem pathCliqueLower_r {r n : ℕ} (hr : 3 ≤ r) (h : r + 2 ≤ n) :
    r.choose 2 + 1 ≤ antiRamseyNum (pathGraph (r + 2)) n := by
  change r.choose 2 + 1 ≤ sSup (admissiblePathCounts r n)
  apply le_csSup (admissiblePathCounts_bddAbove r n)
  refine ⟨pathCliqueColor (by omega : r ≤ n), pathCliqueColor_surjective h, ?_⟩
  exact noRainbowPath_of_commonOutsideColor (by omega : 1 ≤ r)
    (pathCliqueColor (by omega : r ≤ n)) (freshFinColor r)
    (pathCliqueColor_get_outside (by omega : r ≤ n))

/-- The first term of the proposed exact `P_k` formula is a uniform lower bound
in the original quantified range `n ≥ k ≥ 5`. -/
theorem pathCliqueLower {k n : ℕ} (hk : 5 ≤ k) (hkn : k ≤ n) :
    (k - 2).choose 2 + 1 ≤ antiRamseyNum (pathGraph k) n := by
  let r := k - 2
  have hr : 3 ≤ r := by dsimp [r]; omega
  have h : r + 2 ≤ n := by dsimp [r]; omega
  have heq : r + 2 = k := by dsimp [r]; omega
  have hres := pathCliqueLower_r hr h
  dsimp [r] at hres
  rw [show k - 2 + 2 = k by omega] at hres
  exact hres

end ErdosProblems.PathCliqueLower
