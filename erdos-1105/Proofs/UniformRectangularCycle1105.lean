module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
Generalizes the checked RootedK55FilterTransport matching proof to arbitrary
equal finite sides. The output uses the SAME input relation R. This alone
asserts neither a cyclic order nor a rainbow path or graph classification.
-/

namespace ErdosProblems.UniformCrossingMatching1105

def missingCrossingPairs {a : ℕ} (R : Fin a → Fin a → Prop) [DecidableRel R] :
    Finset (Fin a × Fin a) :=
  Finset.univ.filter (fun ij => ¬ R ij.1 ij.2)

/-- A Hall-failure rectangle has at least a entries; no finite a cases. -/
theorem hall_failure_rectangle_bound (a s t : ℕ)
    (hspos : 1 ≤ s) (hsle : s ≤ a) (ht : a - s + 1 ≤ t) :
    a ≤ s * t := by
  have hpred : (s - 1) + 1 = s := by omega
  have hrest : (a - s) + s = a := by omega
  have hproduct : s * (a - s + 1) = a + (s - 1) * (a - s) := by
    calc
      s * (a - s + 1) = ((s - 1) + 1) * (a - s + 1) := by rw [hpred]
      _ = (s - 1) * (a - s) + ((a - s) + ((s - 1) + 1)) := by ring
      _ = (s - 1) * (a - s) + a := by rw [hpred, hrest]
      _ = a + (s - 1) * (a - s) := by omega
  have hbase : a ≤ s * (a - s + 1) := by rw [hproduct]; omega
  exact hbase.trans (Nat.mul_le_mul_left s ht)

/-- Fewer than a missing entries force an actual permutation matching in
the ORIGINAL relation. The a=0 input premise is false; no positivity premise
or hidden nonempty-side condition is needed. -/
theorem crossing_perfect_matching_of_missing_lt {a : ℕ}
    (R : Fin a → Fin a → Prop) [DecidableRel R]
    (hmissing : (missingCrossingPairs R).card < a) :
    ∃ m : Equiv.Perm (Fin a), ∀ i : Fin a, R i (m i) := by
  classical
  let t : Fin a → Finset (Fin a) := fun i =>
    Finset.univ.filter (fun j => R i j)
  have hhall : ∀ s : Finset (Fin a), s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra h
    let N := s.biUnion t
    let T : Finset (Fin a) := Finset.univ \ N
    have hlt : N.card < s.card := Nat.lt_of_not_ge h
    have hsub : s ×ˢ T ⊆ missingCrossingPairs R := by
      rintro ⟨i, j⟩ hij
      have hi := (Finset.mem_product.mp hij).1
      have hj := (Finset.mem_product.mp hij).2
      have hjN : j ∉ N := (Finset.mem_sdiff.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hR
      apply hjN
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩⟩
    have hblock := Finset.card_le_card hsub
    rw [Finset.card_product] at hblock
    have hT : T.card + N.card = a := by
      simpa only [T, Finset.card_univ, Fintype.card_fin] using
        (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N))
    have hsle : s.card ≤ a := by
      simpa only [Fintype.card_fin] using s.card_le_univ
    have hspos : 1 ≤ s.card := by omega
    have hTlower : a - s.card + 1 ≤ T.card := by omega
    have hrectangle : a ≤ s.card * T.card :=
      hall_failure_rectangle_bound a s.card T.card hspos hsle hTlower
    omega
  obtain ⟨g, hg, hgt⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, rfl⟩
  refine ⟨Equiv.ofBijective g hbij, ?_⟩
  intro i
  exact (Finset.mem_filter.mp (hgt i)).2

end ErdosProblems.UniformCrossingMatching1105

/-! Uniform full-order counting for the alternating-cycle bridge in Erdős #1105 Part (ii). -/

set_option autoImplicit false

namespace ErdosProblems.UniformCyclicOrders1105

theorem decompose_first_value (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
  have h := Equiv.Perm.decomposeFin_symm_apply_zero
    (Equiv.Perm.decomposeFin σ).1 (Equiv.Perm.decomposeFin σ).2
  change (Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin σ)) 0 =
    (Equiv.Perm.decomposeFin σ).1 at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

def firstValueFiberEquiv (n : ℕ) (p : Fin (n + 1)) :
    {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = p} ≃ Equiv.Perm (Fin n) := by
  let e₁ : {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = p} ≃
      {t : Fin (n + 1) × Equiv.Perm (Fin n) // t.1 = p} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeFin (fun σ => by
      rw [decompose_first_value])
  let e₂ : {t : Fin (n + 1) × Equiv.Perm (Fin n) // t.1 = p} ≃
      Equiv.Perm (Fin n) := {
    toFun := fun t => t.val.2
    invFun := fun τ => ⟨(p, τ), rfl⟩
    left_inv := fun t => Subtype.ext (Prod.ext t.property.symm rfl)
    right_inv := fun _ => rfl }
  exact e₁.trans e₂

theorem first_value_fiber_card (n : ℕ) (p : Fin (n + 1)) :
    Fintype.card {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = p} = n.factorial := by
  classical
  calc
    _ = Fintype.card (Equiv.Perm (Fin n)) :=
      Fintype.card_congr (firstValueFiberEquiv n p)
    _ = (Fintype.card (Fin n)).factorial := Fintype.card_perm
    _ = n.factorial := by rw [Fintype.card_fin]

theorem zero_one_decompose_iff (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    (σ 0 = 0 ∧ σ 1 = 1) ↔
      ((Equiv.Perm.decomposeFin σ).1 = 0 ∧
       (Equiv.Perm.decomposeFin σ).2 0 = 0) := by
  have hzero := decompose_first_value (n + 1) σ
  have hone := Equiv.Perm.decomposeFin_symm_apply_one
    (Equiv.Perm.decomposeFin σ).2 (Equiv.Perm.decomposeFin σ).1
  rw [Equiv.symm_apply_apply] at hone
  constructor
  · intro h
    have ht := hzero.trans h.1
    refine ⟨ht, ?_⟩
    simp only [ht, Equiv.swap_self, Equiv.refl_apply] at hone
    have hv := congrArg Fin.val (hone.symm.trans h.2)
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_one, Fin.val_zero] at hv ⊢
    omega
  · intro h
    refine ⟨hzero.symm.trans h.1, ?_⟩
    simpa [h.1, h.2] using hone

def zeroOneFiberEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin (n + 2)) // σ 0 = 0 ∧ σ 1 = 1} ≃
      Equiv.Perm (Fin n) := by
  let e₁ : {σ : Equiv.Perm (Fin (n + 2)) // σ 0 = 0 ∧ σ 1 = 1} ≃
      {t : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) // t.1 = 0 ∧ t.2 0 = 0} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeFin (zero_one_decompose_iff n)
  let e₂ : {t : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) // t.1 = 0 ∧ t.2 0 = 0} ≃
      {τ : Equiv.Perm (Fin (n + 1)) // τ 0 = 0} := {
    toFun := fun t => ⟨t.val.2, t.property.2⟩
    invFun := fun τ => ⟨(0, τ.val), rfl, τ.property⟩
    left_inv := fun t => Subtype.ext (Prod.ext t.property.1.symm rfl)
    right_inv := fun τ => Subtype.ext rfl }
  exact e₁.trans (e₂.trans (firstValueFiberEquiv n 0))

theorem zero_one_fiber_card (n : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin (n + 2)) // σ 0 = 0 ∧ σ 1 = 1} =
      n.factorial := by
  classical
  calc
    _ = Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_congr (zeroOneFiberEquiv n)
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

/-- An actual permutation with two prescribed, distinct first values. -/
def pairOrder (n : ℕ) (x y : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (Equiv.swap 0 x).trans (Equiv.swap ((Equiv.swap 0 x) 1) y)

theorem pairOrder_zero (n : ℕ) (x y : Fin (n + 2)) (hxy : x ≠ y) :
    pairOrder n x y 0 = x := by
  have h10 : (1 : Fin (n + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hxz : x ≠ Equiv.swap 0 x 1 := by
    intro h
    have hh := (Equiv.swap 0 x).injective
      ((Equiv.swap_apply_left 0 x).trans h)
    exact h10 hh.symm
  simp only [pairOrder, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hxz hxy

theorem pairOrder_one (n : ℕ) (x y : Fin (n + 2)) :
    pairOrder n x y 1 = y := by
  simp only [pairOrder, Equiv.trans_apply, Equiv.swap_apply_left]

theorem two_value_fiber_card (n : ℕ) (i j x y : Fin (n + 2))
    (hij : i ≠ j) (hxy : x ≠ y) :
    Fintype.card {σ : Equiv.Perm (Fin (n + 2)) // σ i = x ∧ σ j = y} =
      n.factorial := by
  classical
  let p := pairOrder n i j
  let q := pairOrder n x y
  let e : Equiv.Perm (Fin (n + 2)) ≃ Equiv.Perm (Fin (n + 2)) :=
    Equiv.equivCongr p.symm q.symm
  have he (σ : Equiv.Perm (Fin (n + 2))) :
      (σ i = x ∧ σ j = y) ↔ (e σ 0 = 0 ∧ e σ 1 = 1) := by
    simp only [e, Equiv.equivCongr_apply_apply, Equiv.symm_symm,
      p, q, pairOrder_zero n i j hij, pairOrder_one,
      Equiv.symm_apply_eq, pairOrder_zero n x y hxy]
  calc
    _ = Fintype.card {σ : Equiv.Perm (Fin (n + 2)) // σ 0 = 0 ∧ σ 1 = 1} :=
      Fintype.card_congr (Equiv.subtypeEquiv e he)
    _ = n.factorial := zero_one_fiber_card n

noncomputable def positionEvent (n : ℕ) (i x y : Fin (n + 2)) :
    Finset (Equiv.Perm (Fin (n + 2))) := by
  classical
  exact Finset.univ.filter fun σ => σ i = x ∧ σ (finRotate (n + 2) i) = y

noncomputable def cyclicPairEvent (n : ℕ) (x y : Fin (n + 2)) :
    Finset (Equiv.Perm (Fin (n + 2))) := by
  classical
  exact Finset.univ.biUnion fun i => positionEvent n i x y

theorem position_event_card (n : ℕ) (i x y : Fin (n + 2)) (hxy : x ≠ y) :
    (positionEvent n i x y).card = n.factorial := by
  classical
  have hi : i ≠ finRotate (n + 2) i := by
    have hmem : i ∈ (finRotate (n + 2)).support := by
      rw [support_finRotate]
      exact Finset.mem_univ i
    exact (Equiv.Perm.mem_support.mp hmem).symm
  rw [positionEvent, ← Fintype.card_subtype]
  exact two_value_fiber_card n i (finRotate (n + 2) i) x y hi hxy

theorem cyclic_pair_event_card_le (n : ℕ) (x y : Fin (n + 2)) (hxy : x ≠ y) :
    (cyclicPairEvent n x y).card ≤ (n + 2) * n.factorial := by
  classical
  unfold cyclicPairEvent
  have h := Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset (Fin (n + 2)))
    (fun i => positionEvent n i x y) n.factorial
    (fun i _ => (position_event_card n i x y hxy).le)
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- A uniform CYCLIC ordering avoids every forbidden off-diagonal transition. Full orders and all cyclic positions are counted, including the last-to-first
position. -/
theorem exists_cyclic_order_avoiding (n : ℕ)
    (D : Finset (Fin (n + 2) × Fin (n + 2)))
    (hdiag : ∀ xy ∈ D, xy.1 ≠ xy.2) (hcard : D.card ≤ n) :
    ∃ σ : Equiv.Perm (Fin (n + 2)),
      ∀ i : Fin (n + 2), (σ i, σ (finRotate (n + 2) i)) ∉ D := by
  classical
  let bad := D.biUnion fun xy => cyclicPairEvent n xy.1 xy.2
  have hbad : bad.card ≤ D.card * ((n + 2) * n.factorial) :=
    Finset.card_biUnion_le_card_mul D
      (fun xy => cyclicPairEvent n xy.1 xy.2) ((n + 2) * n.factorial)
      (fun xy hxy => cyclic_pair_event_card_le n xy.1 xy.2 (hdiag xy hxy))
  have hbound : bad.card ≤ n * ((n + 2) * n.factorial) :=
    hbad.trans (Nat.mul_le_mul_right _ hcard)
  have hpositive : 0 < (n + 2) * n.factorial :=
    Nat.mul_pos (by omega) (Nat.factorial_pos n)
  have hstrict : n * ((n + 2) * n.factorial) <
      (n + 1) * ((n + 2) * n.factorial) :=
    Nat.mul_lt_mul_of_pos_right (by omega) hpositive
  have hfactorial : (n + 2).factorial = (n + 1) * ((n + 2) * n.factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hlt : bad.card < (Finset.univ : Finset (Equiv.Perm (Fin (n + 2)))).card := by
    simpa only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hfactorial] using
      hbound.trans_lt hstrict
  obtain ⟨σ, _hσuniv, hσbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, ?_⟩
  intro i hi
  apply hσbad
  apply Finset.mem_biUnion.mpr
  refine ⟨(σ i, σ (finRotate (n + 2) i)), hi, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, rfl, rfl⟩

end ErdosProblems.UniformCyclicOrders1105

/-! Generic assembly from an actual matching and an actual cyclic order of its pairs. The graph need not be complete, and no supplied cycle is assumed. -/

namespace ErdosProblems.UniformAlternatingCycleAssembly1105

open SimpleGraph

def pairIndex (a : ℕ) (i : Fin (2 * a)) : Fin a :=
  ⟨i.val / 2, by have hi := i.isLt; omega⟩

def zig (a : ℕ) (i : Fin (2 * a)) : Fin a ⊕ Fin a :=
  if i.val % 2 = 0 then Sum.inl (pairIndex a i) else Sum.inr (pairIndex a i)

theorem zig_injective (a : ℕ) : Function.Injective (zig a) := by
  intro i j h
  by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
  · have he : pairIndex a i = pairIndex a j := Sum.inl.inj (by
      simpa only [zig, ite_eq_left hi, ite_eq_left hj] using h)
    have hv := congrArg Fin.val he
    dsimp only [pairIndex] at hv
    apply Fin.ext
    omega
  · simp only [zig, ite_eq_left hi, ite_eq_right hj, Sum.inl_ne_inr] at h
  · simp only [zig, ite_eq_right hi, ite_eq_left hj, Sum.inr_ne_inl] at h
  · have he : pairIndex a i = pairIndex a j := Sum.inr.inj (by
      simpa only [zig, ite_eq_right hi, ite_eq_right hj] using h)
    have hv := congrArg Fin.val he
    dsimp only [pairIndex] at hv
    apply Fin.ext
    omega

theorem zig_surjective (a : ℕ) : Function.Surjective (zig a) := by
  intro u
  rcases u with u | u
  · let i : Fin (2 * a) := ⟨2 * u.val, by have hu := u.isLt; omega⟩
    have hi : i.val % 2 = 0 := by dsimp only [i]; omega
    have hp : pairIndex a i = u := by
      apply Fin.ext
      dsimp only [pairIndex, i]
      omega
    refine ⟨i, ?_⟩
    simp only [zig, ite_eq_left hi, hp]
  · let i : Fin (2 * a) := ⟨2 * u.val + 1, by have hu := u.isLt; omega⟩
    have hi : i.val % 2 ≠ 0 := by dsimp only [i]; omega
    have hp : pairIndex a i = u := by
      apply Fin.ext
      dsimp only [pairIndex, i]
      omega
    refine ⟨i, ?_⟩
    simp only [zig, ite_eq_right hi, hp]

theorem rotate_val {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  let : NeZero n := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : i.val + 1 = n := by have hi := i.isLt; omega
    rw [he, Nat.mod_self]

theorem zig_rotate_even {a : ℕ} (ha : 2 ≤ a) (i : Fin (2 * a))
    (hi : i.val % 2 = 0) :
    zig a (finRotate (2 * a) i) = Sum.inr (pairIndex a i) := by
  have hlt : i.val + 1 < 2 * a := by have hi' := i.isLt; omega
  have hr := rotate_val (show 2 ≤ 2 * a by omega) i
  rw [ite_eq_left hlt] at hr
  have hm : (finRotate (2 * a) i).val % 2 ≠ 0 := by omega
  have hp : pairIndex a (finRotate (2 * a) i) = pairIndex a i := by
    apply Fin.ext
    dsimp only [pairIndex]
    omega
  simp only [zig, ite_eq_right hm, hp]

theorem zig_rotate_odd {a : ℕ} (ha : 2 ≤ a) (i : Fin (2 * a))
    (hi : i.val % 2 ≠ 0) :
    zig a (finRotate (2 * a) i) = Sum.inl (finRotate a (pairIndex a i)) := by
  have hr := rotate_val (show 2 ≤ 2 * a by omega) i
  have hm : (finRotate (2 * a) i).val % 2 = 0 := by
    split_ifs at hr <;> omega
  have hp : pairIndex a (finRotate (2 * a) i) = finRotate a (pairIndex a i) := by
    apply Fin.ext
    have hs := rotate_val ha (pairIndex a i)
    have hb := i.isLt
    by_cases hlt : i.val + 1 < 2 * a
    · have hpq : (pairIndex a i).val + 1 < a := by dsimp only [pairIndex]; omega
      rw [ite_eq_left hlt] at hr
      rw [ite_eq_left hpq] at hs
      dsimp only [pairIndex] at hs ⊢
      omega
    · have hpq : ¬ (pairIndex a i).val + 1 < a := by dsimp only [pairIndex]; omega
      rw [ite_eq_right hlt] at hr
      rw [ite_eq_right hpq] at hs
      dsimp only [pairIndex] at hs ⊢
      omega
  simp only [zig, ite_eq_left hm, hp]

/-- An actual pair matching and every cyclic transition (including the last
pair back to the first) assemble a literal non-induced cycle Copy on all 2a
embedded vertices. This theorem is uniform in a and in the ambient graph. -/
theorem copy_of_matching_cyclic_order {V : Type*} {a : ℕ} (ha : 2 ≤ a)
    (G : SimpleGraph V) (f : (Fin a ⊕ Fin a) ↪ V)
    (m o : Equiv.Perm (Fin a))
    (hm : ∀ i : Fin a, G.Adj (f (Sum.inl i)) (f (Sum.inr (m i))))
    (ht : ∀ i : Fin a,
      G.Adj (f (Sum.inr (m (o i)))) (f (Sum.inl (o (finRotate a i))))) :
    ∃ p : (cycleGraph (2 * a)).Copy G, Set.range p = Set.range f := by
  classical
  let : NeZero (2 * a) := ⟨by omega⟩
  let e : (Fin a ⊕ Fin a) ≃ (Fin a ⊕ Fin a) :=
    Equiv.sumCongr o (o.trans m)
  let q : Fin (2 * a) → V := fun i => f (e (zig a i))
  have hq : Function.Injective q := by
    intro i j h
    exact zig_injective a (e.injective (f.injective h))
  have hnext : ∀ i : Fin (2 * a), G.Adj (q i) (q (finRotate (2 * a) i)) := by
    intro i
    by_cases hi : i.val % 2 = 0
    · have hz := zig_rotate_even ha i hi
      change G.Adj (f (e (zig a i))) (f (e (zig a (finRotate (2 * a) i))))
      rw [hz]
      simpa [e, zig, hi] using hm (o (pairIndex a i))
    · have hz := zig_rotate_odd ha i hi
      change G.Adj (f (e (zig a i))) (f (e (zig a (finRotate (2 * a) i))))
      rw [hz]
      simpa [e, zig, hi] using ht (pairIndex a i)
  have hmap : ∀ i j : Fin (2 * a), (cycleGraph (2 * a)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    rcases cycleGraph_adj'.mp hij with h | h
    · have he : i - j = (1 : Fin (2 * a)) := by
        apply Fin.ext
        simpa only [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 * a by omega)] using h
      have he' : i = finRotate (2 * a) j := by
        rw [finRotate_apply]
        have he'' : i = 1 + j := sub_eq_iff_eq_add.mp he
        simpa only [add_comm] using he''
      rw [he']
      exact (hnext j).symm
    · have he : j - i = (1 : Fin (2 * a)) := by
        apply Fin.ext
        simpa only [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 * a by omega)] using h
      have he' : j = finRotate (2 * a) i := by
        rw [finRotate_apply]
        have he'' : j = 1 + i := sub_eq_iff_eq_add.mp he
        simpa only [add_comm] using he''
      rw [he']
      exact hnext i
  let φ : (cycleGraph (2 * a)) →g G :=
    { toFun := q, map_rel' := fun {i j} hij => hmap i j hij }
  refine ⟨φ.toCopy hq, ?_⟩
  change Set.range q = Set.range f
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e (zig a i), rfl⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨i, hi⟩ := zig_surjective a (e.symm u)
    refine ⟨i, ?_⟩
    change f (e (zig a i)) = f u
    rw [hi, e.apply_symm_apply]

end ErdosProblems.UniformAlternatingCycleAssembly1105

namespace ErdosProblems.UniformBipartiteCycle1105

open SimpleGraph
open ErdosProblems.UniformCrossingMatching1105
open ErdosProblems.UniformCyclicOrders1105
open ErdosProblems.UniformAlternatingCycleAssembly1105

noncomputable def crossingHoles {V : Type*} {a : ℕ} (G : SimpleGraph V)
    (f : (Fin a ⊕ Fin a) ↪ V) : Finset (Fin a × Fin a) := by
  classical
  exact Finset.univ.filter fun ij =>
    ¬G.Adj (f (Sum.inl ij.1)) (f (Sum.inr ij.2))

/-- Few ACTUAL missing cross edges give a spanning alternating ordinary cycle. The range is exactly the two originally embedded disjoint sides. -/
theorem alternating_cycle_of_missing_cross_edges_le {V : Type*} {a : ℕ}
    (ha : 2 ≤ a) (G : SimpleGraph V) (f : (Fin a ⊕ Fin a) ↪ V)
    (hmissing : (crossingHoles G f).card ≤ a - 2) :
    ∃ p : (cycleGraph (2 * a)).Copy G, Set.range p = Set.range f := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n + 2 := ⟨a - 2, by omega⟩
  let R : Fin (n + 2) → Fin (n + 2) → Prop := fun i j =>
    G.Adj (f (Sum.inl i)) (f (Sum.inr j))
  have hmissingR : (missingCrossingPairs R).card ≤ n := by
    simpa only [crossingHoles, missingCrossingPairs, R, Nat.add_sub_cancel] using hmissing
  obtain ⟨m, hm⟩ := crossing_perfect_matching_of_missing_lt R
    (hmissingR.trans_lt (by omega))
  let D : Finset (Fin (n + 2) × Fin (n + 2)) :=
    Finset.univ.filter fun ij => ¬R ij.2 (m ij.1)
  have hDcard : D.card = (missingCrossingPairs R).card := by
    let e : (Fin (n + 2) × Fin (n + 2)) ≃ (Fin (n + 2) × Fin (n + 2)) :=
      (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) m)
    have he : ∀ ij : Fin (n + 2) × Fin (n + 2),
        (¬R ij.2 (m ij.1)) ↔ (¬R (e ij).1 (e ij).2) := by
      intro ij
      rfl
    let es : {ij : Fin (n + 2) × Fin (n + 2) // ¬R ij.2 (m ij.1)} ≃
        {ij : Fin (n + 2) × Fin (n + 2) // ¬R ij.1 ij.2} :=
      Equiv.subtypeEquiv e he
    have hc := Fintype.card_congr es
    simpa only [Fintype.card_subtype, D, missingCrossingPairs] using hc
  have hdiag : ∀ ij ∈ D, ij.1 ≠ ij.2 := by
    intro ij hij heq
    have hnot := (Finset.mem_filter.mp hij).2
    apply hnot
    rw [← heq]
    exact hm ij.1
  obtain ⟨o, ho⟩ := exists_cyclic_order_avoiding n D hdiag
    (hDcard.trans_le hmissingR)
  have ht : ∀ i : Fin (n + 2), R (o (finRotate (n + 2) i)) (m (o i)) := by
    intro i
    by_contra hi
    exact ho i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  exact copy_of_matching_cyclic_order (by omega) G f m o hm (fun i => (ht i).symm)

end ErdosProblems.UniformBipartiteCycle1105

/-!
The finite weights are arbitrary original column defects; the conclusion
selects an ACTUAL subset rather than replacing or completing a relation. This is only the weight-thinning bridge, not a graph/cycle/path theorem.
-/

namespace ErdosProblems.UniformDefectThinning1105

open scoped BigOperators

/-- A finite carrier whose total defect is at most card-2 contains an actual
a-element subset with total defect at most a-2, with the explicit a>=2 guard. -/
theorem exists_subset_card_eq_with_sum_le
    {β : Type*} [DecidableEq β] (a : ℕ) (S : Finset β) (w : β → ℕ)
    (ha : 2 ≤ a) (hcard : a ≤ S.card)
    (hsum : ∑ x ∈ S, w x ≤ S.card - 2) :
    ∃ Z : Finset β, Z ⊆ S ∧ Z.card = a ∧ ∑ x ∈ Z, w x ≤ a - 2 := by
  classical
  revert hcard hsum
  refine Finset.strongInductionOn S ?_
  intro T ih hcard hsum
  by_cases hsize : T.card = a
  · refine ⟨T, Finset.Subset.refl _, hsize, ?_⟩
    simpa only [hsize] using hsum
  · by_cases hzero : ∀ x ∈ T, w x = 0
    · obtain ⟨Z, hZT, hZa⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨Z, hZT, hZa, ?_⟩
      have hZzero : ∑ x ∈ Z, w x = 0 :=
        Finset.sum_eq_zero (fun x hx => hzero x (hZT hx))
      rw [hZzero]
      exact Nat.zero_le _
    · push Not at hzero
      obtain ⟨x, hxT, hxweight⟩ := hzero
      have hxpositive : 1 ≤ w x := by omega
      have hstrictSize : a < T.card := by omega
      have heraseCard : (T.erase x).card = T.card - 1 :=
        Finset.card_erase_of_mem hxT
      have heraseEnough : a ≤ (T.erase x).card := by omega
      have hsumErase : (∑ y ∈ T.erase x, w y) + w x = ∑ y ∈ T, w y :=
        Finset.sum_erase_add T w hxT
      have heraseCap : ∑ y ∈ T.erase x, w y ≤ (T.erase x).card - 2 := by
        omega
      obtain ⟨Z, hZerase, hZa, hZcap⟩ :=
        ih (T.erase x) (Finset.erase_ssubset hxT) heraseEnough heraseCap
      exact ⟨Z, hZerase.trans (Finset.erase_subset _ _), hZa, hZcap⟩

end ErdosProblems.UniformDefectThinning1105

/-! Actual rectangular crossing defects, actual subset
thinning, and the separately checked balanced-cycle API. No graph completion. -/

namespace ErdosProblems.RectangularCycleBridge1105

open SimpleGraph
open scoped BigOperators

noncomputable def rectangularCrossingHoles {V : Type*} {a t : ℕ}
    (G : SimpleGraph V) (f : (Fin a ⊕ Fin t) ↪ V) : Finset (Fin a × Fin t) := by
  classical
  exact Finset.univ.filter fun ij =>
    ¬G.Adj (f (Sum.inl ij.1)) (f (Sum.inr ij.2))

/-- Exact actual-pair ledger, without any graph or symmetry assumption. -/
theorem filter_pairs_card_eq_sum_columns {a t : ℕ} (R : Fin a → Fin t → Prop)
    [DecidableRel R] :
    (Finset.univ.filter fun ij : Fin a × Fin t => R ij.1 ij.2).card =
      ∑ j : Fin t, (Finset.univ.filter fun i : Fin a => R i j).card := by
  classical
  let S := Finset.univ.filter fun ij : Fin a × Fin t => R ij.1 ij.2
  have hf : S.card = ∑ j : Fin t, (S.filter fun ij => ij.2 = j).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  change S.card = _
  rw [hf]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.card_bij (fun ij _ => ij.1)
  · intro ij hij
    have hmem := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hR := (Finset.mem_filter.mp hmem.1).2
      simpa only [hmem.2] using hR⟩
  · intro x hx y hy he
    apply Prod.ext he
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  · intro i hi
    refine ⟨(i, j), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, rfl⟩

/-- An actual rectangular bipartite embedding with at most t-2 missing cross
edges contains an alternating 2a-cycle after selecting exactly a right vertices.
The selected right embedding and exact cycle range are both returned. -/
theorem alternating_cycle_of_rectangular_missing_le {V : Type*} {a t : ℕ}
    (ha : 2 ≤ a) (hat : a ≤ t) (G : SimpleGraph V)
    (f : (Fin a ⊕ Fin t) ↪ V)
    (hmissing : (rectangularCrossingHoles G f).card ≤ t - 2) :
    ∃ g : Fin a ↪ Fin t, ∃ p : (cycleGraph (2 * a)).Copy G,
      Set.range p = Set.range
        ((Function.Embedding.sumMap (Function.Embedding.refl (Fin a)) g).trans f) := by
  classical
  let R : Fin a → Fin t → Prop := fun i j =>
    ¬G.Adj (f (Sum.inl i)) (f (Sum.inr j))
  let w : Fin t → ℕ := fun j => (Finset.univ.filter fun i : Fin a => R i j).card
  have hsum : ∑ j : Fin t, w j ≤ t - 2 := by
    rw [← filter_pairs_card_eq_sum_columns R]
    exact hmissing
  obtain ⟨Z, _hZ, hcardZ, hcapZ⟩ :=
    ErdosProblems.UniformDefectThinning1105.exists_subset_card_eq_with_sum_le
      a (Finset.univ : Finset (Fin t)) w ha (by simpa using hat) (by simpa using hsum)
  let e : Z ≃ Fin a := Fintype.equivFinOfCardEq
    ((Fintype.card_coe Z).trans hcardZ)
  let g : Fin a ↪ Fin t :=
    ⟨fun i => (e.symm i).val, by
      intro i j hij
      apply e.symm.injective
      exact Subtype.ext hij⟩
  let fb : (Fin a ⊕ Fin a) ↪ V :=
    (Function.Embedding.sumMap (Function.Embedding.refl (Fin a)) g).trans f
  have hsumSelected : (∑ j : Fin a, w (g j)) = ∑ j ∈ Z, w j := by
    calc
      (∑ j : Fin a, w (g j)) = ∑ z : Z, w z.val :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ = ∑ j ∈ Z, w j := Finset.sum_coe_sort Z w
  have hbalanced : (ErdosProblems.UniformBipartiteCycle1105.crossingHoles G fb).card ≤ a - 2 := by
    have hledger := filter_pairs_card_eq_sum_columns
      (fun i j : Fin a => ¬G.Adj (fb (Sum.inl i)) (fb (Sum.inr j)))
    have hledger' : (ErdosProblems.UniformBipartiteCycle1105.crossingHoles G fb).card =
        ∑ j : Fin a, w (g j) := by
      simpa [ErdosProblems.UniformBipartiteCycle1105.crossingHoles,
        fb, g, w, R] using hledger
    rw [hledger', hsumSelected]
    exact hcapZ
  obtain ⟨p, hp⟩ :=
    ErdosProblems.UniformBipartiteCycle1105.alternating_cycle_of_missing_cross_edges_le
      ha G fb hbalanced
  exact ⟨g, p, hp⟩

end ErdosProblems.RectangularCycleBridge1105
