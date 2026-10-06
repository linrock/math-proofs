module

public import PathUpperRainbowBridge
public import UniformRectangularCycle1105
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-! Cycle-cut path extraction and uniform Sell transfer helpers. -/

namespace ErdosProblems.CycleCutPath1105

open SimpleGraph

theorem no_wrap_path_edge (n : ℕ) :
    ¬(pathGraph (n + 3)).Adj (-1) 0 ∧ ¬(pathGraph (n + 3)).Adj 0 (-1) := by
  constructor <;> intro h <;> rcases pathGraph_adj.mp h with h | h <;>
    simp only [Fin.coe_neg_one, Fin.val_zero] at h <;> omega

def path_copy_avoiding {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (old : Sym2 V) (q : Fin (n + 3) → V) (hq : Function.Injective q)
    (hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j))
    (ha : ∀ i j, (pathGraph (n + 3)).Adj i j → s(q i, q j) ≠ old) :
    (pathGraph (n + 3)).Copy (G.deleteEdges {old}) :=
  ⟨⟨q, by
    intro i j hij
    exact deleteEdges_adj.mpr
      ⟨hm i j hij, by simpa only [Set.mem_singleton_iff] using ha i j hij⟩⟩, hq⟩

theorem shift_cycle_adj (n : ℕ) (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (i + r) (j + r) := by
  rw [cycleGraph_adj'] at h ⊢
  simpa only [add_sub_add_right_eq_sub] using h

theorem reverse_cycle_adj (n : ℕ) (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (r - i) (r - j) := by
  have h₁ : (r - i) - (r - j) = j - i := by abel
  have h₂ : (r - j) - (r - i) = i - j := by abel
  rw [cycleGraph_adj'] at h ⊢
  simpa only [h₁, h₂, or_comm] using h

/-- Forward cyclic order rooted at r drops exactly the predecessor-r edge. -/
theorem path_of_cycle_cut_predecessor {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (c : (cycleGraph (n + 3)).Copy G) (r : Fin (n + 3)) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c (r - 1), c r)}),
      p 0 = c r ∧ Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (i + r)
  have hq : Function.Injective q := by
    intro i j h
    exact add_right_cancel (c.injective h)
  have hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    exact c.toHom.map_rel' (shift_cycle_adj n r i j (pathGraph_le_cycleGraph hij))
  have ha : ∀ i j, (pathGraph (n + 3)).Adj i j →
      s(q i, q j) ≠ s(c (r - 1), c r) := by
    intro i j hij he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = -1 := by
        have h := c.injective hi
        calc i = (i + r) - r := by abel
             _ = (r - 1) - r := by rw [h]
             _ = -1 := by abel
      have hj' : j = 0 := by
        have h := c.injective hj
        calc j = (j + r) - r := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      exact (no_wrap_path_edge n).1 (by simpa only [hi', hj'] using hij)
    · have hi' : i = 0 := by
        have h := c.injective hi
        calc i = (i + r) - r := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      have hj' : j = -1 := by
        have h := c.injective hj
        calc j = (j + r) - r := by abel
             _ = (r - 1) - r := by rw [h]
             _ = -1 := by abel
      exact (no_wrap_path_edge n).2 (by simpa only [hi', hj'] using hij)
  refine ⟨path_copy_avoiding G _ q hq hm ha, ?_, ?_⟩
  · change c (0 + r) = c r
    rw [zero_add]
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i + r, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i - r, ?_⟩
      change c (i - r + r) = c i
      rw [sub_add_cancel]

/-- Reverse cyclic order rooted at r drops exactly the r-successor edge. -/
theorem path_of_cycle_cut_successor {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (c : (cycleGraph (n + 3)).Copy G) (r : Fin (n + 3)) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c r, c (r + 1))}),
      p 0 = c r ∧ Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (r - i)
  have hq : Function.Injective q := by
    intro i j h
    have he := c.injective h
    calc i = r - (r - i) := by abel
         _ = r - (r - j) := by rw [he]
         _ = j := by abel
  have hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    exact c.toHom.map_rel' (reverse_cycle_adj n r i j (pathGraph_le_cycleGraph hij))
  have ha : ∀ i j, (pathGraph (n + 3)).Adj i j →
      s(q i, q j) ≠ s(c r, c (r + 1)) := by
    intro i j hij he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 0 := by
        have h := c.injective hi
        calc i = r - (r - i) := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      have hj' : j = -1 := by
        have h := c.injective hj
        calc j = r - (r - j) := by abel
             _ = r - (r + 1) := by rw [h]
             _ = -1 := by abel
      exact (no_wrap_path_edge n).2 (by simpa only [hi', hj'] using hij)
    · have hi' : i = -1 := by
        have h := c.injective hi
        calc i = r - (r - i) := by abel
             _ = r - (r + 1) := by rw [h]
             _ = -1 := by abel
      have hj' : j = 0 := by
        have h := c.injective hj
        calc j = r - (r - j) := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      exact (no_wrap_path_edge n).1 (by simpa only [hi', hj'] using hij)
  refine ⟨path_copy_avoiding G _ q hq hm ha, ?_, ?_⟩
  · change c (r - 0) = c r
    rw [sub_zero]
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨r - i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨r - i, ?_⟩
      change c (r - (r - i)) = c i
      congr 1
      abel

/-- Cut an arbitrary actual cycle edge at either prescribed endpoint u. -/
theorem path_of_cycle_cut_edge_at_endpoint {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (c : (cycleGraph (n + 3)).Copy G) (u v : Fin (n + 3))
    (huv : (cycleGraph (n + 3)).Adj u v) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c u, c v)}),
      p 0 = c u ∧ Set.range p = Set.range c := by
  classical
  rcases cycleGraph_adj'.mp huv with h | h
  · have hdiff : u - v = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simpa only [Fin.val_one] using h
    have hv : v = u - 1 := by
      have he := sub_eq_iff_eq_add.mp hdiff
      calc v = (1 + v) - 1 := by abel
           _ = u - 1 := by rw [← he]
    have he : s(c (u - 1), c u) = s(c u, c v) := by rw [hv]; exact Sym2.eq_swap
    rw [← he]
    exact path_of_cycle_cut_predecessor G c u
  · have hdiff : v - u = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simpa only [Fin.val_one] using h
    have hv : v = u + 1 := by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp hdiff)
    rw [hv]
    exact path_of_cycle_cut_successor G c u

theorem path_of_cycle_prescribed_root_of_owner_absent {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G) (old : Sym2 V)
    (r : Fin (n + 3))
    (habsent : ∀ i j, (cycleGraph (n + 3)).Adj i j → s(c i, c j) ≠ old) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {old}),
      p 0 = c r ∧ Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (i + r)
  have hq : Function.Injective q := by
    intro i j h
    exact add_right_cancel (c.injective h)
  have hcy : ∀ i j, (pathGraph (n + 3)).Adj i j →
      (cycleGraph (n + 3)).Adj (i + r) (j + r) := by
    intro i j hij
    exact shift_cycle_adj n r i j (pathGraph_le_cycleGraph hij)
  refine ⟨path_copy_avoiding G old q hq
    (fun i j hij => c.toHom.map_rel' (hcy i j hij))
    (fun i j hij => habsent _ _ (hcy i j hij)), ?_, ?_⟩
  · change c (0 + r) = c r
    rw [zero_add]
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i + r, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i - r, ?_⟩
      change c (i - r + r) = c i
      rw [sub_add_cancel]

end ErdosProblems.CycleCutPath1105

/-! Uniform actual relation defects for the Sell colored-container application. The selected right embedding and all exceptional vertices are conclusions. The supplied relation is never completed or replaced by a surrogate relation. -/

namespace ErdosProblems.UniformSellDefects1105

open SimpleGraph
open scoped BigOperators

def relationHoles {a t : ℕ} (R : Fin a → Fin t → Prop) [DecidableRel R] :
    Finset (Fin a × Fin t) :=
  Finset.univ.filter (fun ij => ¬ R ij.1 ij.2)

/-- The exact bipartite graph of the original crossing relation. -/
def relationGraph {a t : ℕ} (R : Fin a → Fin t → Prop) :
    SimpleGraph (Fin a ⊕ Fin t) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inr j => R i j
    | Sum.inr j, Sum.inl i => R i j
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> exact h⟩
  loopless := ⟨by
    intro x
    cases x <;> exact not_false⟩

/-- Total original defects below t force an actual universal right vertex. -/
theorem exists_universal_right_of_defects_le {a t : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (R : Fin a → Fin t → Prop) [DecidableRel R]
    (hmissing : (relationHoles R).card ≤ t - 3) :
    ∃ y : Fin t, ∀ i : Fin a, R i y := by
  classical
  let w : Fin t → ℕ := fun j => (Finset.univ.filter fun i : Fin a => ¬ R i j).card
  have htotal : ∑ j : Fin t, w j ≤ t - 3 := by
    rw [← ErdosProblems.RectangularCycleBridge1105.filter_pairs_card_eq_sum_columns
      (fun i j => ¬ R i j)]
    exact hmissing
  by_contra hnone
  push Not at hnone
  have hweight : ∀ j : Fin t, 1 ≤ w j := by
    intro j
    obtain ⟨i, hi⟩ := hnone j
    have hmem : i ∈ Finset.univ.filter (fun i : Fin a => ¬ R i j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    exact Finset.card_pos.mpr ⟨i, hmem⟩
  have hlow : t ≤ ∑ j : Fin t, w j := by
    calc
      t = ∑ _j : Fin t, (1 : ℕ) := by simp
      _ ≤ ∑ j : Fin t, w j := Finset.sum_le_sum (fun j _ => hweight j)
  omega

/-- Remove an actual universal column and choose actual distinct right
vertices with the balanced defect cap; avoidance of y is proved, not assumed. -/
theorem exists_universal_and_thinned_embedding {a t : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (R : Fin a → Fin t → Prop) [DecidableRel R]
    (hmissing : (relationHoles R).card ≤ t - 3) :
    ∃ y : Fin t, ∃ g : Fin a ↪ Fin t,
      (∀ i : Fin a, R i y) ∧
      (∀ j : Fin a, g j ≠ y) ∧
      (relationHoles (fun i j : Fin a => R i (g j))).card ≤ a - 2 := by
  classical
  obtain ⟨y, hy⟩ := exists_universal_right_of_defects_le ha hat R hmissing
  let w : Fin t → ℕ := fun j => (Finset.univ.filter fun i : Fin a => ¬ R i j).card
  let S : Finset (Fin t) := Finset.univ.erase y
  have hScard : S.card = t - 1 := by
    simpa only [S, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_erase_of_mem (Finset.mem_univ y))
  have hwy : w y = 0 := by
    have hempty : (Finset.univ.filter fun i : Fin a => ¬ R i y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (Finset.mem_filter.mp hi).2 (hy i)
    simp only [w, hempty, Finset.card_empty]
  have htotal : ∑ j : Fin t, w j ≤ t - 3 := by
    rw [← ErdosProblems.RectangularCycleBridge1105.filter_pairs_card_eq_sum_columns
      (fun i j => ¬ R i j)]
    exact hmissing
  have hsumErase : (∑ j ∈ S, w j) + w y = ∑ j : Fin t, w j :=
    Finset.sum_erase_add Finset.univ w (Finset.mem_univ y)
  have hScap : ∑ j ∈ S, w j ≤ S.card - 2 := by omega
  obtain ⟨Z, hZS, hcardZ, hcapZ⟩ :=
    ErdosProblems.UniformDefectThinning1105.exists_subset_card_eq_with_sum_le
      a S w ha (by omega) hScap
  let e : Z ≃ Fin a := Fintype.equivFinOfCardEq
    ((Fintype.card_coe Z).trans hcardZ)
  let g : Fin a ↪ Fin t :=
    ⟨fun j => (e.symm j).val, by
      intro i j hij
      apply e.symm.injective
      exact Subtype.ext hij⟩
  have havoid : ∀ j : Fin a, g j ≠ y := by
    intro j
    exact (Finset.mem_erase.mp (hZS (e.symm j).property)).1
  have hsumSelected : (∑ j : Fin a, w (g j)) = ∑ j ∈ Z, w j := by
    calc
      (∑ j : Fin a, w (g j)) = ∑ z : Z, w z.val :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ = ∑ j ∈ Z, w j := Finset.sum_coe_sort Z w
  have hledger : (relationHoles (fun i j : Fin a => R i (g j))).card =
      ∑ j : Fin a, w (g j) := by
    simpa only [relationHoles, w] using
      ErdosProblems.RectangularCycleBridge1105.filter_pairs_card_eq_sum_columns
        (fun i j : Fin a => ¬ R i (g j))
  refine ⟨y, g, hy, havoid, ?_⟩
  rw [hledger, hsumSelected]
  exact hcapZ

/-- The universal vertex, owner-independent selected cycle, exact range,
balanced defect cap and a second outside right vertex are all derived from
the original relation. This contains no coloring or structural premise. -/
theorem exists_sell_cycle_and_two_outside_right {a t : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (R : Fin a → Fin t → Prop) [DecidableRel R]
    (hmissing : (relationHoles R).card ≤ t - 3) :
    ∃ y : Fin t, ∃ g : Fin a ↪ Fin t,
      ∃ p : (cycleGraph (2 * a)).Copy (relationGraph R),
        (∀ i : Fin a, R i y) ∧
        (∀ j : Fin a, g j ≠ y) ∧
        (relationHoles (fun i j : Fin a => R i (g j))).card ≤ a - 2 ∧
        Set.range p = Set.range
          (Function.Embedding.sumMap (Function.Embedding.refl (Fin a)) g) ∧
        ∃ y' : Fin t, y' ≠ y ∧ ∀ j : Fin a, g j ≠ y' := by
  classical
  obtain ⟨y, g, hy, havoid, hbalanced⟩ :=
    exists_universal_and_thinned_embedding ha hat R hmissing
  let f : (Fin a ⊕ Fin a) ↪ (Fin a ⊕ Fin t) :=
    Function.Embedding.sumMap (Function.Embedding.refl (Fin a)) g
  have hholes :
      (ErdosProblems.UniformBipartiteCycle1105.crossingHoles (relationGraph R) f).card
        ≤ a - 2 := by
    simpa [ErdosProblems.UniformBipartiteCycle1105.crossingHoles,
      relationHoles, relationGraph, f] using hbalanced
  obtain ⟨p, hp⟩ :=
    ErdosProblems.UniformBipartiteCycle1105.alternating_cycle_of_missing_cross_edges_le
      ha (relationGraph R) f hholes
  let U : Finset (Fin t) := Finset.univ.image g
  have hUcard : U.card = a := by
    simp only [U, Finset.card_image_of_injective _ g.injective,
      Finset.card_univ, Fintype.card_fin]
  have hyU : y ∉ U := by
    intro hmem
    obtain ⟨j, _hj, hgj⟩ := Finset.mem_image.mp hmem
    exact havoid j hgj
  have hcap : (insert y U).card < (Finset.univ : Finset (Fin t)).card := by
    rw [Finset.card_insert_of_notMem hyU, hUcard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨y', _hy', hy'outside⟩ := Finset.exists_mem_notMem_of_card_lt_card hcap
  have hy'ne : y' ≠ y := by
    intro heq
    apply hy'outside
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hgoutside : ∀ j : Fin a, g j ≠ y' := by
    intro j heq
    apply hy'outside
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩
  exact ⟨y, g, p, hy, havoid, hbalanced, hp, y', hy'ne, hgoutside⟩

end ErdosProblems.UniformSellDefects1105

/-!
Original-color assembly for the Sell exit: prepends two outside vertices to an
ordinary path, deletes the owner of the inserted original color, and applies
the full-representative rainbow bridge.
-/

namespace ErdosProblems.UniformSellOriginalColor1105

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Prefix two distinct outside vertices to an ordinary actual path. -/
theorem prepend_two_to_pathCopy {V : Type*} {m : ℕ} (hm : 0 < m)
    (G : SimpleGraph V) (P : (pathGraph m).Copy G) (y yprime : V)
    (hy : y ∉ Set.range P) (hyprime : yprime ∉ Set.range P)
    (hne : yprime ≠ y) (hjoin : G.Adj yprime y)
    (hspoke : G.Adj y (P ⟨0, hm⟩)) :
    Nonempty ((pathGraph (m + 2)).Copy G) := by
  let Q : Fin (m + 1) → V := Fin.cons y P
  let W : Fin (m + 2) → V := Fin.cons yprime Q
  have hQinj : Function.Injective Q :=
    Fin.cons_injective_of_injective hy P.injective
  have hyprimeQ : yprime ∉ Set.range Q := by
    rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero =>
        apply hne
        simpa only [Q, Fin.cons_zero] using hi.symm
    | succ j =>
        apply hyprime
        exact ⟨j, by simpa only [Q, Fin.cons_succ] using hi⟩
  have hWinj : Function.Injective W :=
    Fin.cons_injective_of_injective hyprimeQ hQinj
  have hforward (i j : Fin (m + 2)) (hij : i.val + 1 = j.val) :
      G.Adj (W i) (W j) := by
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      have hj : j = (0 : Fin (m + 1)).succ := Fin.ext (by simp; omega)
      rw [hi, hj]
      simpa only [W, Q, Fin.cons_zero, Fin.cons_succ] using hjoin
    · by_cases hi1 : i.val = 1
      · have hi : i = (0 : Fin (m + 1)).succ := Fin.ext (by simp; omega)
        have hj : j = (⟨0, hm⟩ : Fin m).succ.succ := Fin.ext (by simp; omega)
        rw [hi, hj]
        simpa only [W, Q, Fin.cons_zero, Fin.cons_succ] using hspoke
      · have hi2 : 2 ≤ i.val := by omega
        have hj2 : 2 ≤ j.val := by omega
        let ii : Fin m := ⟨i.val - 2, by have hi := i.isLt; omega⟩
        let jj : Fin m := ⟨j.val - 2, by have hj := j.isLt; omega⟩
        have hi : i = ii.succ.succ := Fin.ext (by dsimp [ii]; omega)
        have hj : j = jj.succ.succ := Fin.ext (by dsimp [jj]; omega)
        have hadj : (pathGraph m).Adj ii jj :=
          pathGraph_adj.mpr (Or.inl (by dsimp [ii, jj]; omega))
        rw [hi, hj]
        simpa only [W, Q, Fin.cons_succ, Copy.toHom_apply] using P.toHom.map_adj hadj
  let phi : (pathGraph (m + 2)) →g G := ⟨W, by
    intro i j hij
    rcases pathGraph_adj.mp hij with h | h
    · exact hforward i j h
    · exact (hforward j i h).symm⟩
  exact ⟨⟨phi, hWinj⟩⟩

/-- The actual complete-host edge inserted at the two outside vertices. -/
def insertedOutsideEdge {n : ℕ} (y yprime : Fin n) (hne : yprime ≠ y) :
    HostEdge n :=
  ⟨s(yprime, y), (top_adj _ _).mpr hne⟩

/-- The actual full representative owner of the inserted edge's original color. -/
def insertedOwner {n q : ℕ} (chi : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice chi) (y yprime : Fin n) (hne : yprime ≠ y) :
    Sym2 (Fin n) :=
  (r.edge (chi (insertedOutsideEdge y yprime hne))).val

/-- A path avoiding the actual owner and a surviving actual attachment spoke
give a rainbow original-host path after same-color replacement. -/
theorem rainbow_path_of_owner_deleted_path_and_two_outside
    {a n q : ℕ} (ha : 2 ≤ a)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (y yprime : Fin n) (hne : yprime ≠ y)
    (P : (pathGraph (2 * a)).Copy
      ((selectedGraph chi r).deleteEdges {insertedOwner chi r y yprime hne}))
    (hy : y ∉ Set.range P) (hyprime : yprime ∉ Set.range P)
    (hspoke : (selectedGraph chi r).Adj y (P ⟨0, by omega⟩))
    (hspoke_owner : s(y, P ⟨0, by omega⟩) ≠ insertedOwner chi r y yprime hne) :
    ∃ f : (pathGraph (2 * a + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom chi := by
  classical
  let e : HostEdge n := insertedOutsideEdge y yprime hne
  let D := (selectedGraph chi r).deleteEdges {insertedOwner chi r y yprime hne}
  let R := selectedGraph chi (r.replace e)
  have hle : D ≤ R := delete_selectedEdge_le_replace chi r e
  let P' : (pathGraph (2 * a)).Copy R :=
    ⟨⟨P, by intro i j hij; exact hle (P.toHom.map_adj hij)⟩, P.injective⟩
  have hy' : y ∉ Set.range P' := hy
  have hyprime' : yprime ∉ Set.range P' := hyprime
  have hjoin : R.Adj yprime y := by
    have he := replacedEdge_mem chi r e
    change s(yprime, y) ∈ (selectedGraph chi (r.replace e)).edgeSet
    exact he
  have hspoke' : R.Adj y (P' ⟨0, by omega⟩) := by
    change R.Adj y (P ⟨0, by omega⟩)
    apply hle
    exact deleteEdges_adj.mpr ⟨hspoke, by simpa only [Set.mem_singleton_iff] using hspoke_owner⟩
  obtain ⟨f⟩ := prepend_two_to_pathCopy (by omega : 0 < 2 * a)
    R P' y yprime hy' hyprime' hne hjoin hspoke'
  exact ⟨(Copy.ofLE R (⊤ : SimpleGraph (Fin n)) le_top).comp f,
    copy_in_selectedGraph_isRainbow chi (r.replace e) f⟩

/-- For EVERY possible old selected
edge, retain an ordinary spanning path in the owner-deleted graph, rooted
in the actual left side, with an attachment spoke distinct from that owner. This helper has an explicit input proposition; the final deficit theorem proves it. -/
def CycleRootPathInterface {V : Type*} (a : ℕ) (ha : 2 ≤ a)
    (G : SimpleGraph V) (C : (cycleGraph (2 * a)).Copy G)
    (X : Set V) (y : V) : Prop :=
  ∀ old : Sym2 V, ∃ P : (pathGraph (2 * a)).Copy (G.deleteEdges {old}),
    Set.range P = Set.range C ∧ P ⟨0, by omega⟩ ∈ X ∧
      s(y, P ⟨0, by omega⟩) ≠ old

/-- Transparent conditional cycle-to-original-color assembly. -/
theorem rainbow_path_of_cycle_root_interface
    {a n q : ℕ} (ha : 2 ≤ a)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (C : (cycleGraph (2 * a)).Copy (selectedGraph chi r)) (X : Set (Fin n))
    (y yprime : Fin n) (hne : yprime ≠ y)
    (hy : y ∉ Set.range C) (hyprime : yprime ∉ Set.range C)
    (hy_universal : ∀ x ∈ X, (selectedGraph chi r).Adj y x)
    (hcut : CycleRootPathInterface a ha (selectedGraph chi r) C X y) :
    ∃ f : (pathGraph (2 * a + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom chi := by
  obtain ⟨P, hrange, hroot, havoid⟩ :=
    hcut (insertedOwner chi r y yprime hne)
  have hyP : y ∉ Set.range P := by simpa only [hrange] using hy
  have hyprimeP : yprime ∉ Set.range P := by simpa only [hrange] using hyprime
  exact rainbow_path_of_owner_deleted_path_and_two_outside ha chi r y yprime hne
    P hyP hyprimeP (hy_universal _ hroot) havoid

end ErdosProblems.UniformSellOriginalColor1105

/-! body; composed-file verification is recorded separately assembly fragment. -/

namespace ErdosProblems.CycleOwnerRootInterface1105

open SimpleGraph
open ErdosProblems.CycleCutPath1105

/-- An actual cycle whose every edge has an X endpoint admits an owner-deleted
spanning path rooted in X. Two distinct X cycle vertices guarantee a usable
attachment spoke even when the arbitrary owner is absent from the cycle. -/
theorem cycle_owner_deleted_path_with_left_root {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (C : (cycleGraph (n + 3)).Copy G) (X : Set V) (y : V)
    (hy : y ∉ Set.range C)
    (hcross : ∀ i j, (cycleGraph (n + 3)).Adj i j → C i ∈ X ∨ C j ∈ X)
    (r1 r2 : Fin (n + 3)) (h1 : C r1 ∈ X) (h2 : C r2 ∈ X)
    (hne : C r1 ≠ C r2) :
    ∀ old : Sym2 V, ∃ P : (pathGraph (n + 3)).Copy (G.deleteEdges {old}),
      Set.range P = Set.range C ∧ P 0 ∈ X ∧ s(y, P 0) ≠ old := by
  classical
  intro old
  by_cases howner : ∃ u v : Fin (n + 3),
      (cycleGraph (n + 3)).Adj u v ∧ s(C u, C v) = old
  · obtain ⟨u, v, huv, heold⟩ := howner
    have hspoke : ∀ x : V, s(y, x) ≠ old := by
      intro x he
      have he' : s(y, x) = s(C u, C v) := he.trans heold.symm
      rcases Sym2.eq_iff.mp he' with h | h
      · exact hy ⟨u, h.1.symm⟩
      · exact hy ⟨v, h.1.symm⟩
    rcases hcross u v huv with hu | hv
    · have hcut := path_of_cycle_cut_edge_at_endpoint G C u v huv
      rw [heold] at hcut
      obtain ⟨P, hroot, hrange⟩ := hcut
      refine ⟨P, hrange, ?_, hspoke (P 0)⟩
      simpa only [hroot] using hu
    · have heold' : s(C v, C u) = old := Sym2.eq_swap.trans heold
      have hcut := path_of_cycle_cut_edge_at_endpoint G C v u huv.symm
      rw [heold'] at hcut
      obtain ⟨P, hroot, hrange⟩ := hcut
      refine ⟨P, hrange, ?_, hspoke (P 0)⟩
      simpa only [hroot] using hv
  · have habsent : ∀ i j : Fin (n + 3),
        (cycleGraph (n + 3)).Adj i j → s(C i, C j) ≠ old := by
      intro i j hij he
      exact howner ⟨i, j, hij, he⟩
    by_cases hspoke1 : s(y, C r1) ≠ old
    · obtain ⟨P, hroot, hrange⟩ :=
        path_of_cycle_prescribed_root_of_owner_absent G C old r1 habsent
      refine ⟨P, hrange, ?_, ?_⟩
      · simpa only [hroot] using h1
      · simpa only [hroot] using hspoke1
    · have he1 : s(y, C r1) = old := by simpa only [not_ne_iff] using hspoke1
      have hspoke2 : s(y, C r2) ≠ old := by
        intro he2
        apply hne
        exact Sym2.congr_right.mp (he1.trans he2.symm)
      obtain ⟨P, hroot, hrange⟩ :=
        path_of_cycle_prescribed_root_of_owner_absent G C old r2 habsent
      refine ⟨P, hrange, ?_, ?_⟩
      · simpa only [hroot] using h2
      · simpa only [hroot] using hspoke2

/-- Same interface at the caller's literal cycle length m>=3. -/
theorem cycle_owner_deleted_path_with_left_root_general {V : Type*} {m : ℕ}
    (hm : 3 ≤ m) (G : SimpleGraph V) (C : (cycleGraph m).Copy G)
    (X : Set V) (y : V) (hy : y ∉ Set.range C)
    (hcross : ∀ i j, (cycleGraph m).Adj i j → C i ∈ X ∨ C j ∈ X)
    (r1 r2 : Fin m) (h1 : C r1 ∈ X) (h2 : C r2 ∈ X)
    (hne : C r1 ≠ C r2) :
    ∀ old : Sym2 V, ∃ P : (pathGraph m).Copy (G.deleteEdges {old}),
      Set.range P = Set.range C ∧ P ⟨0, by omega⟩ ∈ X ∧
        s(y, P ⟨0, by omega⟩) ≠ old := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 3 := ⟨m - 3, by omega⟩
  simpa using cycle_owner_deleted_path_with_left_root G C X y hy hcross r1 r2 h1 h2 hne

end ErdosProblems.CycleOwnerRootInterface1105

namespace ErdosProblems.UniformSellApplication1105
open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.UniformSellDefects1105
open ErdosProblems.UniformSellOriginalColor1105

theorem right_outside_selected_sum_range {a t : ℕ} {V : Type*}
    (f : (Fin a ⊕ Fin t) ↪ V) (g : Fin a ↪ Fin t) (y : Fin t)
    (hy : ∀ j, g j ≠ y) :
    f (Sum.inr y) ∉ Set.range (fun z : Fin a ⊕ Fin a =>
      f ((Function.Embedding.sumMap (Function.Embedding.refl (Fin a)) g) z)) := by
  rintro ⟨z, hz⟩
  have he := f.injective hz
  cases z with
  | inl i => cases he
  | inr j => exact hy j (Sum.inr.inj he)

noncomputable def selectedCrossingHoles {a t n q : ℕ}
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (f : (Fin a ⊕ Fin t) ↪ Fin n) : Finset (Fin a × Fin t) := by
  classical
  exact relationHoles (fun i j =>
    (selectedGraph chi r).Adj (f (Sum.inl i)) (f (Sum.inr j)))

/-- Missing actual selected crossing edges, with unrestricted other edges,
force a rainbow path in the SAME original coloring. -/
theorem rainbow_path_of_missing_selected_cross_edges
    {a t n q : ℕ} (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (f : (Fin a ⊕ Fin t) ↪ Fin n)
    (hmissing : (selectedCrossingHoles chi r f).card ≤ t - 3) :
    ∃ p : (pathGraph (2 * a + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom chi := by
  classical
  let G := selectedGraph chi r
  let R : Fin a → Fin t → Prop := fun i j => G.Adj (f (Sum.inl i)) (f (Sum.inr j))
  obtain ⟨y, g, C0, huniversal, hgy, _hbalanced, hrange, yprime, hypy, hgyp⟩ :=
    exists_sell_cycle_and_two_outside_right ha hat R hmissing
  let e : (Fin a ⊕ Fin a) ↪ (Fin a ⊕ Fin t) :=
    Function.Embedding.sumMap (Function.Embedding.refl (Fin a)) g
  let F : (relationGraph R).Copy G :=
    ⟨⟨f, by
      intro u v huv
      cases u with
      | inl i =>
        cases v with
        | inl j => exact huv.elim
        | inr j => exact huv
      | inr j =>
        cases v with
        | inl i =>
          have h : G.Adj (f (Sum.inl i)) (f (Sum.inr j)) := huv
          exact h.symm
        | inr k => exact huv.elim⟩, f.injective⟩
  let C : (cycleGraph (2 * a)).Copy G := F.comp C0
  have hCrange : Set.range C = Set.range (fun z : Fin a ⊕ Fin a => f (e z)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      have hi : C0 i ∈ Set.range e := by rw [← hrange]; exact ⟨i, rfl⟩
      obtain ⟨z, hz⟩ := hi
      exact ⟨z, congrArg f hz⟩
    · rintro ⟨z, rfl⟩
      have hz : e z ∈ Set.range C0 := by rw [hrange]; exact ⟨z, rfl⟩
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, congrArg f hi⟩
  let Y : Fin n := f (Sum.inr y)
  let Yprime : Fin n := f (Sum.inr yprime)
  have hyC : Y ∉ Set.range C := by
    rw [hCrange]
    exact right_outside_selected_sum_range f g y hgy
  have hypC : Yprime ∉ Set.range C := by
    rw [hCrange]
    exact right_outside_selected_sum_range f g yprime hgyp
  have hYY : Yprime ≠ Y := by
    intro h
    exact hypy (Sum.inr.inj (f.injective h))
  let X : Set (Fin n) := Set.range (fun i : Fin a => f (Sum.inl i))
  have hcross (i j : Fin (2 * a)) (hij : (cycleGraph (2 * a)).Adj i j) :
      C i ∈ X ∨ C j ∈ X := by
    have hadj := C0.toHom.map_adj hij
    cases hi : C0 i with
    | inl x =>
      left
      refine ⟨x, ?_⟩
      change f (Sum.inl x) = f (C0 i)
      rw [hi]
    | inr z =>
      cases hj : C0 j with
      | inl x =>
        right
        refine ⟨x, ?_⟩
        change f (Sum.inl x) = f (C0 j)
        rw [hj]
      | inr w =>
        change (relationGraph R).Adj (C0 i) (C0 j) at hadj
        rw [hi, hj] at hadj
        exact hadj.elim
  let x0 : Fin a := ⟨0, by omega⟩
  let x1 : Fin a := ⟨1, by omega⟩
  have hx0 : f (Sum.inl x0) ∈ Set.range C := by
    rw [hCrange]
    exact ⟨Sum.inl x0, rfl⟩
  have hx1 : f (Sum.inl x1) ∈ Set.range C := by
    rw [hCrange]
    exact ⟨Sum.inl x1, rfl⟩
  obtain ⟨i0, hi0⟩ := hx0
  obtain ⟨i1, hi1⟩ := hx1
  have hroot0 : C i0 ∈ X := ⟨x0, hi0.symm⟩
  have hroot1 : C i1 ∈ X := ⟨x1, hi1.symm⟩
  have hdistinct : C i0 ≠ C i1 := by
    intro h
    have he := Sum.inl.inj (f.injective (hi0.symm.trans (h.trans hi1)))
    have hv := congrArg Fin.val he
    change 0 = 1 at hv
    omega
  have hcut : CycleRootPathInterface a ha G C X Y := by
    exact ErdosProblems.CycleOwnerRootInterface1105.cycle_owner_deleted_path_with_left_root_general
      (by omega : 3 ≤ 2 * a) G C X Y hyC hcross i0 i1 hroot0 hroot1 hdistinct
  have hspokes : ∀ x ∈ X, G.Adj Y x := by
    rintro x ⟨i, rfl⟩
    exact (huniversal i).symm
  exact rainbow_path_of_cycle_root_interface ha chi r C X Y Yprime hYY
    hyC hypC hspokes hcut

end ErdosProblems.UniformSellApplication1105
