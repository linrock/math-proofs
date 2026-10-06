module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic

@[expose] public section

/-!
The edges of the complete graph that meet an initial set of `t` vertices
form the private-edge palette in the fixed-set rainbow-path lower coloring.
-/

namespace ErdosProblems.PathSetLower

/-- The first `t` vertices, truncated at `n`. -/
def hostVertices (t n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val < t)

/-- Complete-graph edges meeting at least one of the first `t` vertices. -/
def incidentEdgeFinset (t n : ℕ) :
    Finset ((⊤ : SimpleGraph (Fin n)).edgeSet) :=
  Finset.univ.filter (fun e =>
    ∃ v ∈ (e.1 : Sym2 (Fin n)).toFinset, v ∈ hostVertices t n)

@[simp]
theorem mem_incidentEdgeFinset (t n : ℕ)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    e ∈ incidentEdgeFinset t n ↔
      ∃ v ∈ (e.1 : Sym2 (Fin n)).toFinset, v.val < t := by
  simp [incidentEdgeFinset, hostVertices]

@[simp]
theorem mem_incidentEdgeFinset_mk (t n : ℕ) (u v : Fin n)
    (h : s(u, v) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet) :
    (⟨s(u, v), h⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ incidentEdgeFinset t n ↔
      u.val < t ∨ v.val < t := by
  simp [mem_incidentEdgeFinset, Sym2.toFinset_mk_eq]

theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.succ_add, Nat.choose_succ_succ' (a + b) 1,
        Nat.choose_succ_succ' a 1, ih]
      simp only [Nat.reduceAdd, Nat.choose_one_right, Nat.succ_mul]
      omega

/-- The incident-edge palette has `t.choose 2 + t * (n - t)` colors. -/
theorem incidentEdgeFinset_card (t n : ℕ) (h : t ≤ n) :
    (incidentEdgeFinset t n).card = t.choose 2 + t * (n - t) := by
  classical
  let S : Finset (Fin n) := hostVertices t n
  have hS : S.card = t := by
    simpa [S, hostVertices, Nat.min_eq_right h] using
      (Fin.card_filter_val_lt (n := n) (m := t))
  have hSc : Sᶜ.card = n - t := by
    rw [Finset.card_compl, Fintype.card_fin, hS]
  let E : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset
  let P : Sym2 (Fin n) → Prop := fun e => ∃ v ∈ e.toFinset, v ∈ S
  have hMap : (incidentEdgeFinset t n).image Subtype.val = E.filter P := by
    ext e
    simp [incidentEdgeFinset, E, P, S, hostVertices, and_comm]
  have hInc : (incidentEdgeFinset t n).card = (E.filter P).card := by
    rw [← hMap, Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hAvoid : (E.filter (fun e => ¬ P e)).card = (n - t).choose 2 := by
    have hEq : E.filter (fun e => ¬ P e) =
        E.filter (fun e => e.toFinset ⊆ Sᶜ) := by
      ext e
      simp [P, Finset.subset_iff]
    rw [hEq]
    have hOffDiag : E.filter (fun e => e.toFinset ⊆ Sᶜ) =
        Sᶜ.offDiag.image Sym2.mk.uncurry := by
      calc
        E.filter (fun e => e.toFinset ⊆ Sᶜ) = E ∩ Sᶜ.sym2 := by
          simpa [E] using
            (SimpleGraph.filter_edgeFinset_toFinset_subset
              (G := (⊤ : SimpleGraph (Fin n))) (s := Sᶜ))
        _ = Sᶜ.sym2.filter (fun e => ¬ e.IsDiag) := by
          ext e
          simp [E, SimpleGraph.edgeFinset_top, and_comm]
        _ = Sᶜ.offDiag.image Sym2.mk.uncurry := by
          rw [Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag]
    rw [hOffDiag, Sym2.card_image_offDiag, hSc]
  have hTotal : E.card = n.choose 2 := by
    simpa [E] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))
  have hPartition : (E.filter P).card + (E.filter (fun e => ¬ P e)).card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) P
  rw [hInc]
  have hN : n = t + (n - t) := by omega
  have hChoose : n.choose 2 = t.choose 2 + t * (n - t) + (n - t).choose 2 := by
    calc
      n.choose 2 = (t + (n - t)).choose 2 := congrArg (·.choose 2) hN
      _ = t.choose 2 + t * (n - t) + (n - t).choose 2 := choose_two_add _ _
  rw [hAvoid, hTotal, hChoose] at hPartition
  omega

end ErdosProblems.PathSetLower
