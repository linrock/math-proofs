module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic


@[expose] public section

/-!
# Monochromatic pairs for Sudakov's graph Ramsey argument

An integer version of Lemma 2.2 of Benny Sudakov,
*A conjecture of Erdős on graph Ramsey numbers*, arXiv:1002.0095.
The explicit size hypothesis avoids the vacuous negative reservoir bound
when a host is too small to contain either requested clique.
-/

namespace Erdos546

open Finset

variable {V : Type*} [DecidableEq V]

/-- All edges within `X` and from `X` to its disjoint reservoir `Y` belong to `H`. -/
def MonoPair (H : SimpleGraph V) (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ H.IsClique (X : Set V) ∧ ∀ x ∈ X, ∀ y ∈ Y, H.Adj x y

omit [DecidableEq V] in
theorem monoPair_empty (H : SimpleGraph V) (Y : Finset V) : MonoPair H ∅ Y := by
  simp [MonoPair, SimpleGraph.IsClique]

omit [DecidableEq V] in
theorem monoPair_mono {H : SimpleGraph V} {X Y X' Y' : Finset V}
    (h : MonoPair H X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : MonoPair H X' Y' := by
  rcases h with ⟨hd, hc, he⟩
  refine ⟨hd.mono hX hY, ?_, ?_⟩
  · exact hc.subset (by simpa using hX)
  · exact fun x hx y hy => he x (hX hx) y (hY hy)

theorem monoPair_insert {H : SimpleGraph V} {v : V} {X Y : Finset V}
    (h : MonoPair H X Y) (hvX : v ∉ X) (hvY : v ∉ Y)
    (hX : ∀ x ∈ X, H.Adj v x) (hY : ∀ y ∈ Y, H.Adj v y) :
    MonoPair H (insert v X) Y := by
  rcases h with ⟨hd, hc, he⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using (Finset.disjoint_insert_left.mpr ⟨hvY, hd⟩)
  · intro a ha b hb hab
    simp only [Finset.mem_coe, mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact hX b hb
    · rcases hb with rfl | hb
      · exact (hX a ha).symm
      · exact hc ha hb hab
  · intro a ha b hb
    rcases mem_insert.mp ha with rfl | ha
    · exact hY b hb
    · exact he a ha b hb

/-- Exact cardinality recurrence for the two neighbor colors of a vertex. -/
theorem neighbor_partition_card (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : Finset V) {v : V} (hv : v ∈ s) :
    (s.filter (H.Adj v)).card + (s.filter (Hᶜ.Adj v)).card = s.card - 1 := by
  have hp : s.filter (Hᶜ.Adj v) = (s.erase v).filter (fun w => ¬ H.Adj v w) := by
    ext w
    simp [SimpleGraph.compl_adj, and_left_comm, and_assoc, eq_comm]
  have hr : s.filter (H.Adj v) = (s.erase v).filter (H.Adj v) := by
    ext w
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hw, he⟩
      exact ⟨⟨he.ne.symm, hw⟩, he⟩
    · tauto
  rw [hp, hr, Finset.card_filter_add_card_filter_not, card_erase_of_mem hv]

/-- A recurrence with an explicit integer reservoir target. It supplies the
monochromatic-pair initialization used in the sparse graph argument. -/
theorem exists_monoPair (H : SimpleGraph V) [DecidableRel H.Adj]
    (k l r : ℕ) (s : Finset V)
    (hs : (k + l).choose k * (r + 1) ≤ s.card) :
    (∃ X Y, X ⊆ s ∧ Y ⊆ s ∧ MonoPair H X Y ∧ X.card = k ∧ r ≤ Y.card) ∨
    (∃ X Y, X ⊆ s ∧ Y ⊆ s ∧ MonoPair Hᶜ X Y ∧ X.card = l ∧ r ≤ Y.card) := by
  induction k generalizing l s with
  | zero =>
    left
    refine ⟨∅, s, empty_subset _, Subset.rfl, monoPair_empty H s, rfl, ?_⟩
    simpa using (show r ≤ s.card by simpa using (le_trans (by simp) hs))
  | succ k ihk =>
    induction l generalizing s with
    | zero =>
      right
      refine ⟨∅, s, empty_subset _, Subset.rfl, monoPair_empty Hᶜ s, rfl, ?_⟩
      simpa using (show r ≤ s.card by simpa using (le_trans (by simp) hs))
    | succ l ihl =>
      have hchoose :
          (k + 1 + (l + 1)).choose (k + 1) =
          (k + (l + 1)).choose k + (k + 1 + l).choose (k + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.choose_succ_succ (k + l + 1) k)
      have hpos : 0 < (k + 1 + (l + 1)).choose (k + 1) :=
        Nat.choose_pos (by omega)
      have hnonempty : s.Nonempty := by
        apply card_pos.mp
        have : 0 < (k + 1 + (l + 1)).choose (k + 1) * (r + 1) :=
          Nat.mul_pos hpos (by omega)
        omega
      obtain ⟨v, hv⟩ := hnonempty
      let sr := s.filter (H.Adj v)
      let sb := s.filter (Hᶜ.Adj v)
      have hcard : sr.card + sb.card = s.card - 1 := neighbor_partition_card H s hv
      have hbranch :
          (k + (l + 1)).choose k * (r + 1) ≤ sr.card ∨
          (k + 1 + l).choose (k + 1) * (r + 1) ≤ sb.card := by
        rw [hchoose] at hs
        by_contra hn
        push Not at hn
        have hvcard : 0 < s.card := card_pos.mpr ⟨v, hv⟩
        rw [Nat.add_mul] at hs
        omega
      rcases hbranch with hr | hb
      · rcases ihk (l + 1) sr hr with hred | hblue
        · rcases hred with ⟨X, Y, hXs, hYs, hp, hX, hY⟩
          left
          refine ⟨insert v X, Y, ?_, ?_, ?_, ?_, hY⟩
          · exact insert_subset hv (hXs.trans (filter_subset _ _))
          · exact hYs.trans (filter_subset _ _)
          · apply monoPair_insert hp
            · intro hv'
              exact H.irrefl ((mem_filter.mp (hXs hv')).2)
            · intro hv'
              exact H.irrefl ((mem_filter.mp (hYs hv')).2)
            · exact fun x hx => (mem_filter.mp (hXs hx)).2
            · exact fun y hy => (mem_filter.mp (hYs hy)).2
          · rw [card_insert_of_notMem, hX]
            intro hv'
            exact H.irrefl ((mem_filter.mp (hXs hv')).2)
        · right
          rcases hblue with ⟨X, Y, hXs, hYs, hp, hX, hY⟩
          exact ⟨X, Y, hXs.trans (filter_subset _ _), hYs.trans (filter_subset _ _), hp, hX, hY⟩
      · rcases ihl sb hb with hred | hblue
        · left
          rcases hred with ⟨X, Y, hXs, hYs, hp, hX, hY⟩
          exact ⟨X, Y, hXs.trans (filter_subset _ _), hYs.trans (filter_subset _ _), hp, hX, hY⟩
        · rcases hblue with ⟨X, Y, hXs, hYs, hp, hX, hY⟩
          right
          refine ⟨insert v X, Y, ?_, ?_, ?_, ?_, hY⟩
          · exact insert_subset hv (hXs.trans (filter_subset _ _))
          · exact hYs.trans (filter_subset _ _)
          · apply monoPair_insert hp
            · intro hv'
              exact Hᶜ.irrefl ((mem_filter.mp (hXs hv')).2)
            · intro hv'
              exact Hᶜ.irrefl ((mem_filter.mp (hYs hv')).2)
            · exact fun x hx => (mem_filter.mp (hXs hx)).2
            · exact fun y hy => (mem_filter.mp (hYs hy)).2
          · rw [card_insert_of_notMem, hX]
            intro hv'
            exact Hᶜ.irrefl ((mem_filter.mp (hXs hv')).2)

#print axioms monoPair_empty
#print axioms monoPair_mono
#print axioms monoPair_insert
#print axioms neighbor_partition_card
#print axioms exists_monoPair

end Erdos546
