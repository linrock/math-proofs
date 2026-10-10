module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import PathResidualDecomposition

@[expose] public section

/-!
# PathConeAndVineCycles

Uniform cone containers, rectangular and vine cycle splices, crossing/boundary endpoints, and saturated even `H`-order embeddings for Erdős Problem 1105.
-/

section

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

end

section

open SimpleGraph
open ErdosProblems.PathUpperReduction

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

end

namespace ErdosProblems.UniformSellContainerCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.UniformSellDefects1105
open ErdosProblems.UniformSellApplication1105

/-- Every actual edge belongs either to the actual left core or an actual
crossing pair. The deficit is counted without natural subtraction. -/
theorem edge_count_add_crossing_defects_le {a t : ℕ}
    (G : SimpleGraph (Fin a ⊕ Fin t)) [DecidableRel G.Adj]
    (hYY : ∀ j j' : Fin t, ¬ G.Adj (Sum.inr j) (Sum.inr j')) :
    G.edgeFinset.card +
      (relationHoles (fun i j => G.Adj (Sum.inl i) (Sum.inr j))).card ≤
        a.choose 2 + a * t := by
  classical
  let C : SimpleGraph (Fin a) := G.comap Sum.inl
  let emb : Fin a ↪ (Fin a ⊕ Fin t) :=
    ⟨Sum.inl, by intro i j h; exact Sum.inl.inj h⟩
  let T : Finset (Fin a × Fin t) := Finset.univ.filter
    (fun ij => G.Adj (Sum.inl ij.1) (Sum.inr ij.2))
  let A := C.edgeFinset.map emb.sym2Map
  let B := T.image (fun ij => s(Sum.inl ij.1, Sum.inr ij.2))
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨ij, _hij, hje⟩ := Finset.mem_image.mp heB
    obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp heA
    revert hd hde
    refine Sym2.inductionOn d ?_
    intro x y _hd hde
    have heq : s(Sum.inl x, Sum.inl y) = s(Sum.inl ij.1, Sum.inr ij.2) := by
      change s(Sum.inl x, Sum.inl y) = e at hde
      exact hde.trans hje.symm
    rcases Sym2.eq_iff.mp heq with ⟨_, hy⟩ | ⟨hx, _⟩
    · cases hy
    · cases hx
  have hE : G.edgeFinset = A ∪ B := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    constructor
    · intro he
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
      cases x with
      | inl i =>
        cases y with
        | inl i' =>
          apply Finset.mem_union_left
          apply Finset.mem_map.mpr
          refine ⟨s(i, i'), SimpleGraph.mem_edgeFinset.mpr hxy, ?_⟩
          rfl
        | inr j =>
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩
      | inr j =>
        cases y with
        | inl i =>
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.symm⟩,
              Sym2.eq_swap⟩
        | inr j' => exact (hYY j j' hxy).elim
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp he
        revert hd hde
        refine Sym2.inductionOn d ?_
        intro i j hd hde
        change s(Sum.inl i, Sum.inl j) = s(x, y) at hde
        rw [← hde]
        have hij : C.Adj i j := SimpleGraph.mem_edgeFinset.mp hd
        have hG : G.Adj (Sum.inl i) (Sum.inl j) := hij
        exact SimpleGraph.mem_edgeFinset.mpr hG
      · obtain ⟨ij, hij, hje⟩ := Finset.mem_image.mp he
        rw [← hje]
        exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hij).2
  have hBcard : B.card = T.card := by
    apply Finset.card_image_of_injective
    intro ij kl he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, _hj⟩
    · exact Prod.ext (Sum.inl.inj hi) (Sum.inr.inj hj)
    · cases hi
  have hcount : G.edgeFinset.card = C.edgeFinset.card + T.card := by
    have h := congrArg Finset.card hE
    rw [Finset.card_union_of_disjoint hAB, Finset.card_map, hBcard] at h
    exact h
  have hpartition : T.card +
      (relationHoles (fun i j => G.Adj (Sum.inl i) (Sum.inr j))).card = a * t := by
    simpa only [T, relationHoles, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin a × Fin t)))
        (fun ij => G.Adj (Sum.inl ij.1) (Sum.inr ij.2)))
  have hcore : C.edgeFinset.card ≤ a.choose 2 := by
    simpa only [Fintype.card_fin] using C.card_edgeFinset_le_card_choose_two
  omega

/-- The strict palette threshold forces the original crossing defect cap. -/
theorem crossing_defects_le_of_edge_count {a t : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (G : SimpleGraph (Fin a ⊕ Fin t)) [DecidableRel G.Adj]
    (hYY : ∀ j j' : Fin t, ¬ G.Adj (Sum.inr j) (Sum.inr j'))
    (he : a.choose 2 + (a - 1) * t + 2 < G.edgeFinset.card) :
    (relationHoles (fun i j => G.Adj (Sum.inl i) (Sum.inr j))).card ≤ t - 3 := by
  classical
  have hcount := edge_count_add_crossing_defects_le G hYY
  have hprod : a * t = (a - 1) * t + t := by
    calc
      a * t = ((a - 1) + 1) * t := by congr 1; omega
      _ = (a - 1) * t + t := by ring
  rw [hprod] at hcount
  omega

/-- Count the entire palette through an actual spanning equivalence. -/
theorem selected_crossing_defects_le_of_spanning_container {a t n q : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (f : (Fin a ⊕ Fin t) ≃ Fin n)
    (hYY : ∀ j j' : Fin t,
      ¬ (selectedGraph chi r).Adj (f (Sum.inr j)) (f (Sum.inr j')))
    (hq : a.choose 2 + (a - 1) * t + 2 < q) :
    (selectedCrossingHoles chi r f.toEmbedding).card ≤ t - 3 := by
  classical
  let G := selectedGraph chi r
  have hcard : (G.comap f).edgeFinset.card = q := by
    rw [(SimpleGraph.Iso.comap f G).card_edgeFinset_eq]
    exact selectedGraph_card_edgeFinset chi r
  have he : a.choose 2 + (a - 1) * t + 2 < (G.comap f).edgeFinset.card := by
    rw [hcard]
    exact hq
  simpa only [selectedCrossingHoles, G, SimpleGraph.comap_adj, Equiv.coe_toEmbedding] using
    crossing_defects_le_of_edge_count ha hat (G.comap f) hYY he

/-- Unconditional original-color Sell container exit. The core may omit
edges; arbitrary original color owners are handled by the verified transfer. -/
theorem rainbow_path_of_spanning_sell_container {a t n q : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (f : (Fin a ⊕ Fin t) ≃ Fin n)
    (hYY : ∀ j j' : Fin t,
      ¬ (selectedGraph chi r).Adj (f (Sum.inr j)) (f (Sum.inr j')))
    (hq : a.choose 2 + (a - 1) * t + 2 < q) :
    ∃ p : (pathGraph (2 * a + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom chi := by
  exact rainbow_path_of_missing_selected_cross_edges ha hat chi r f.toEmbedding
    (selected_crossing_defects_le_of_spanning_container ha hat chi r f hYY hq)

end ErdosProblems.UniformSellContainerCount1105

section

open SimpleGraph
open ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.ActualVertexCoverSellExit1105

/-- An actual d-vertex cover and a palette above the literal even linear
branch force a rainbow P_(2*d+2) in the original complete-host coloring.
All selected edges and their arbitrary original owners are unchanged. -/
theorem rainbow_path_of_actual_vertex_cover {d n q : ℕ}
    (hd : 2 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Finset (Fin n)) (hX : X.card = d)
    (hcover : ∀ u v : Fin n, (selectedGraph χ r).Adj u v → u ∈ X ∨ v ∈ X)
    (hq : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q) :
    ∃ p : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  classical
  let S : Set (Fin n) := ↑X
  have hS : Fintype.card S = d := by
    exact (Fintype.card_of_finset' (p := S) X (fun _ => Iff.rfl)).trans hX
  have hSc : Fintype.card (Sᶜ : Set (Fin n)) = n - d := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hS]
  let eL : Fin d ≃ S := (Finset.equivFinOfCardEq (s := X) hX).symm
  let eR : Fin (n - d) ≃ (Sᶜ : Set (Fin n)) :=
    (Fintype.equivFinOfCardEq hSc).symm
  let f : (Fin d ⊕ Fin (n - d)) ≃ Fin n :=
    (Equiv.sumCongr eL eR).trans (Equiv.Set.sumCompl S)
  have hright (j : Fin (n - d)) : f (Sum.inr j) ∉ X := by
    change (eR j).val ∉ X
    exact (eR j).property
  have hYY : ∀ j j' : Fin (n - d),
      ¬ (selectedGraph χ r).Adj (f (Sum.inr j)) (f (Sum.inr j')) := by
    intro j j' hjj'
    rcases hcover _ _ hjj' with hx | hx
    · exact hright j hx
    · exact hright j' hx
  have hdt : d + 2 ≤ n - d := by omega
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using
      (Nat.choose_succ_succ' (d - 1) 1)
  have hthreshold : d.choose 2 + (d - 1) * (n - d) + 2 =
      (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 := by
    rw [hchoose]
    ring
  apply ErdosProblems.UniformSellContainerCount1105.rainbow_path_of_spanning_sell_container
    hd hdt χ r f hYY
  rwa [hthreshold]

end ErdosProblems.PathUpperReduction.ActualVertexCoverSellExit1105

end

section

namespace ErdosProblems.PathUpperReduction.FixedContactEar1105
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Two fixed distinct contacts in one actual outside component give a simple
ear with all internal vertices outside S and at least three actual edges. -/
theorem exists_fixed_contact_ear
    (C : (G.induce Sᶜ).ConnectedComponent)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (v w : ↥(Sᶜ)) (hvC : v ∈ C.supp) (hwC : w ∈ C.supp)
    (hvw : v ≠ w) (hxv : G.Adj x v.val) (hwy : G.Adj w.val y) :
    ∃ q : G.Walk x y, q.IsPath ∧ 3 ≤ q.length ∧
      (∀ z, z ∈ q.support → z ≠ x → z ≠ y →
        z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp) ∧
      (∀ z, z ∈ q.support → z ≠ x → z ≠ y → z ∉ S) ∧
      (∀ z, z ∈ q.support → z ∈ S → z = x ∨ z = y) ∧
      ∃ middle : G.Walk v.val w.val, middle.IsPath ∧
        (∀ z, z ∈ middle.support →
          z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp) ∧
        q = (Walk.cons hxv middle).concat hwy ∧
        (∀ z, z ∈ q.support ↔ z = x ∨ z = y ∨ z ∈ middle.support) := by
  classical
  obtain ⟨inside, hinside⟩ :=
    C.connected_toSimpleGraph.exists_isPath ⟨v, hvC⟩ ⟨w, hwC⟩
  let middle : G.Walk v.val w.val :=
    (inside.map C.toSimpleGraph_hom).map (Embedding.induce Sᶜ).toHom
  have hmiddle : middle.IsPath :=
    Walk.IsPath.map (f := (Embedding.induce Sᶜ).toHom) Subtype.val_injective
      (Walk.IsPath.map (f := C.toSimpleGraph_hom) Subtype.val_injective hinside)
  have hcomponent : ∀ z, z ∈ middle.support →
      z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp := by
    intro z hz
    change z ∈ ((inside.map C.toSimpleGraph_hom).map
      (Embedding.induce Sᶜ).toHom).support at hz
    rw [Walk.support_map, Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hu
    exact ⟨t.val, t.property, rfl⟩
  have havoids : ∀ z, z ∈ middle.support → z ∉ S := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := hcomponent z hz
    exact u.property
  have hxnot : x ∉ middle.support := fun hz => havoids x hz hx
  let left : G.Walk x w.val := Walk.cons hxv middle
  have hleft : left.IsPath := hmiddle.cons hxnot
  have hynot : y ∉ left.support := by
    intro hz
    have hcases : y = x ∨ y ∈ middle.support := by
      simpa only [left, Walk.support_cons, List.mem_cons] using hz
    rcases hcases with h | h
    · exact hxy h.symm
    · exact havoids y h hy
  let q : G.Walk x y := left.concat hwy
  have hq : q.IsPath := hleft.concat hynot hwy
  have hpositive : 0 < middle.length := Nat.pos_of_ne_zero (by
    intro hzero
    exact hvw (Subtype.ext (Walk.eq_of_length_eq_zero hzero)))
  have hsupport : ∀ z, z ∈ q.support ↔
      z = x ∨ z = y ∨ z ∈ middle.support := by
    intro z
    simp only [q, left, Walk.support_concat, Walk.support_cons,
      List.mem_append, List.mem_cons]
    aesop
  have hcomponentInternal : ∀ z, z ∈ q.support → z ≠ x → z ≠ y →
      z ∈ (Subtype.val : ↥(Sᶜ) → V) '' C.supp := by
    intro z hz hzx hzy
    rcases (hsupport z).mp hz with h | h | h
    · exact (hzx h).elim
    · exact (hzy h).elim
    · exact hcomponent z h
  refine ⟨q, hq, ?_, hcomponentInternal, ?_, ?_, middle, hmiddle,
    hcomponent, ?_, hsupport⟩
  · simp only [q, left, Walk.length_concat, Walk.length_cons]
    omega
  · intro z hz hzx hzy
    obtain ⟨u, _, rfl⟩ := hcomponentInternal z hz hzx hzy
    exact u.property
  · intro z hz hzS
    rcases (hsupport z).mp hz with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (havoids z h hzS).elim
  · rfl

end ErdosProblems.PathUpperReduction.FixedContactEar1105
namespace ErdosProblems.PathUpperReduction.CliqueSpanningPath1105

open SimpleGraph

theorem exists_clique_spanning_path {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hclique : G.IsClique (S : Set V))
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ P : G.Walk a b, P.IsPath ∧ P.length = S.card - 1 ∧
      (∀ z, z ∈ P.support ↔ z ∈ S) := by
  classical
  let T : Finset V := (S.erase a).erase b
  let L : List V := a :: (T.toList ++ [b])
  have haT : a ∉ T := by simp [T]
  have hbT : b ∉ T := by simp [T]
  have hTsub : T ⊆ S := by
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have happ : (T.toList ++ [b]).Nodup := by
    apply List.Nodup.append T.nodup_toList (by simp)
    rw [List.disjoint_left]
    intro z hz hz'
    have hzb : z = b := List.mem_singleton.mp hz'
    subst z
    exact hbT (Finset.mem_toList.mp hz)
  have hLnodup : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, happ⟩
    intro hz
    rcases List.mem_append.mp hz with h | h
    · exact haT (Finset.mem_toList.mp h)
    · exact hab (List.mem_singleton.mp h)
  have hmem (z : V) : z ∈ L ↔ z ∈ S := by
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with h | h
      · exact h.symm ▸ ha
      · rcases List.mem_append.mp h with h | h
        · exact hTsub (Finset.mem_toList.mp h)
        · exact (List.mem_singleton.mp h).symm ▸ hb
    · intro hz
      by_cases hza : z = a
      · exact List.mem_cons.mpr (Or.inl hza)
      by_cases hzb : z = b
      · exact List.mem_cons.mpr
          (Or.inr (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hzb))))
      have hzT : z ∈ T := by
        exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
      exact List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl (Finset.mem_toList.mpr hzT))))
  have hchain : L.IsChain G.Adj := by
    apply List.Pairwise.isChain
    exact hLnodup.pairwise_of_forall_ne
      (fun x hx y hy hxy => hclique ((hmem x).mp hx) ((hmem y).mp hy) hxy)
  have hne : L ≠ [] := by simp [L]
  have hhead : L.head hne = a := by simp [L]
  have hlast : L.getLast hne = b := by
    change ((a :: T.toList) ++ [b]).getLast _ = b
    exact List.getLast_append_singleton (a :: T.toList)
  have hbErase : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hTcard : T.card + 1 = (S.erase a).card :=
    Finset.card_erase_add_one hbErase
  have hScard : (S.erase a).card + 1 = S.card :=
    Finset.card_erase_add_one ha
  have hLlength : L.length = S.card := by
    have hTL : T.toList.length = T.card := Finset.length_toList T
    simp only [L, List.length_cons, List.length_append, List.length_nil, hTL]
    omega
  let P : G.Walk a b := (Walk.ofSupport L hne hchain).copy hhead hlast
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [Walk.isPath_def]
    simpa only [P, Walk.support_copy, Walk.support_ofSupport]
      using hLnodup
  · simp only [P, Walk.length_copy, Walk.length_ofSupport, hLlength]
  · intro z
    simpa only [P, Walk.support_copy, Walk.support_ofSupport] using hmem z

end ErdosProblems.PathUpperReduction.CliqueSpanningPath1105

namespace ErdosProblems.PathUpperReduction.LargeCoreStructure1105
open SimpleGraph

/-- The first vertex of a simple path does not recur in its support tail. -/
theorem path_start_notMem_tail {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) : a ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

/-- An actual clique-spanning path and an outside ear yield an actual long cycle.
The ear is an auxiliary input here; the component caller constructs it internally. -/
theorem long_cycle_of_clique_ear {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} {a b : V}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (Q : G.Walk a b) (hQ : Q.IsPath) (hQL : 3 ≤ Q.length)
    (hcontact : ∀ z, z ∈ Q.support → z ∈ S → z = a ∨ z = b) :
    ∃ m : ℕ, K ≤ m ∧ cycleGraph m ⊑ G := by
  classical
  obtain ⟨P, hP, hPlength, hPsupport⟩ :=
    ErdosProblems.PathUpperReduction.CliqueSpanningPath1105.exists_clique_spanning_path
      G S hclique ha hb hab
  have hcycle : (P.append Q.reverse).IsCycle := by
    apply hP.isCycle_append hQ.reverse
    · intro z hzP hzQ
      have hzPs : z ∈ P.support := List.mem_of_mem_tail hzP
      have hzQs : z ∈ Q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hzQ
      rcases hcontact z hzQs ((hPsupport z).mp hzPs) with hza | hzb
      · exact path_start_notMem_tail P hP (hza ▸ hzP)
      · exact path_start_notMem_tail Q.reverse hQ.reverse (hzb ▸ hzQ)
    · right
      simp only [Walk.length_reverse]
      omega
  have hlength : K ≤ (P.append Q.reverse).length := by
    simp only [Walk.length_append, Walk.length_reverse]
    omega
  refine ⟨(P.append Q.reverse).length, hlength, ?_⟩
  exact (cycleGraph_isContained_iff (by omega)).mpr
    ⟨a, P.append Q.reverse, hcycle, rfl⟩

/-- Under actual ALL-long-cycle freedom, two distinct contacts of one actual
outside component cannot attach to distinct clique anchors. The ear and the
clique-spanning path are constructed from the SAME graph, not supplied. -/
theorem distinct_component_contacts_have_same_anchor {V : Type*}
    (G : SimpleGraph V) (S : Finset V) {K : ℕ}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (C : (G.induce (S : Set V)ᶜ).ConnectedComponent)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (v w : ↥((S : Set V)ᶜ)) (hvC : v ∈ C.supp) (hwC : w ∈ C.supp)
    (hvw : v ≠ w) (hav : G.Adj a v.val) (hwb : G.Adj w.val b) : a = b := by
  by_contra hab
  obtain ⟨Q, hQ, hQL, _, _, hcontact, _⟩ :=
    ErdosProblems.PathUpperReduction.FixedContactEar1105.exists_fixed_contact_ear
      C ha hb hab v w hvC hwC hvw hav hwb
  obtain ⟨m, hm, hcycle⟩ :=
    long_cycle_of_clique_ear G S hK hcard hclique ha hb hab Q hQ hQL hcontact
  exact hfree m hm hcycle

end ErdosProblems.PathUpperReduction.LargeCoreStructure1105

namespace ErdosProblems.PathUpperReduction.LargeCoreStructure1105
open SimpleGraph

/-- An actual connected deletion graph crosses the actual boundary of T. -/
theorem deletion_connected_boundary {V : Type*} (G : SimpleGraph V)
    (T : Set V) {a u v : V}
    (hdelete : (G.induce {z : V | z ≠ a}).Connected)
    (hu : u ∈ T) (hua : u ≠ a) (hv : v ∉ T) (hva : v ≠ a) :
    ∃ x : V, x ∈ T ∧ x ≠ a ∧
      ∃ y : V, y ∉ T ∧ y ≠ a ∧ G.Adj x y := by
  let u' : {z : V // z ≠ a} := ⟨u, hua⟩
  let v' : {z : V // z ≠ a} := ⟨v, hva⟩
  obtain ⟨p, _⟩ := hdelete.exists_isPath u' v'
  obtain ⟨d, _, hdx, hdy⟩ :=
    p.exists_boundary_dart {z | z.val ∈ T} hu hv
  exact ⟨d.fst.val, hdx, d.fst.property,
    d.snd.val, hdy, d.snd.property, d.adj⟩

/-- An edge leaving a whole outside component must end in the actual core. -/
theorem component_boundary_lands_in_core {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (C : (G.induce (S : Set V)ᶜ).ConnectedComponent)
    {x y : V}
    (hx : x ∈ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
    (hy : y ∉ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
    (hxy : G.Adj x y) : y ∈ S := by
  classical
  by_contra hyS
  obtain ⟨v, hvC, rfl⟩ := hx
  let w : ↥((S : Set V)ᶜ) := ⟨y, hyS⟩
  have hwC : w ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp hvC
      (show (G.induce (S : Set V)ᶜ).Adj v w from hxy)
  exact hy ⟨w, hwC, rfl⟩

/-- Delete any actual core vertex: the whole outside component still has an
actual core contact whose anchor avoids that deleted vertex. -/
theorem component_contact_avoiding_core_vertex {V : Type*}
    (G : SimpleGraph V) (S : Finset V) (hcard : 1 < S.card)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    (C : (G.induce (S : Set V)ᶜ).ConnectedComponent)
    {a : V} (ha : a ∈ S) :
    ∃ w : ↥((S : Set V)ᶜ), w ∈ C.supp ∧
      ∃ b : V, b ∈ S ∧ b ≠ a ∧ G.Adj w.val b := by
  classical
  obtain ⟨u, huC⟩ := C.nonempty_supp
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
  have hua : u.val ≠ a := by
    intro h
    exact u.property (h.symm ▸ ha)
  have hboutside : b ∉ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp := by
    rintro ⟨z, _, hz⟩
    exact z.property (hz.symm ▸ hb)
  obtain ⟨x, hx, _, y, hy, hya, hxy⟩ :=
    deletion_connected_boundary G
      ((Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
      (hdelete a) ⟨u, huC, rfl⟩ hua hboutside hba
  have hyS := component_boundary_lands_in_core G S C hx hy hxy
  obtain ⟨w, hwC, rfl⟩ := hx
  exact ⟨w, hwC, y, hyS, hya, hxy⟩

/-- Actual deletion connectivity and ALL-long-cycle freedom force every
outside component of the actual (K-2)-clique to contain one vertex. -/
theorem outside_component_subsingleton {V : Type*}
    (G : SimpleGraph V) (S : Finset V) {K : ℕ}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    (C : (G.induce (S : Set V)ᶜ).ConnectedComponent) :
    ∀ v w : ↥((S : Set V)ᶜ), v ∈ C.supp → w ∈ C.supp → v = w := by
  classical
  have hScard : 1 < S.card := by omega
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨w₁, hw₁C, a₁, ha₁, _, hw₁a₁⟩ :=
    component_contact_avoiding_core_vertex G S hScard hdelete C ha₀
  obtain ⟨w₂, hw₂C, a₂, ha₂, ha₂a₁, hw₂a₂⟩ :=
    component_contact_avoiding_core_vertex G S hScard hdelete C ha₁
  have hw₁₂ : w₁ = w₂ := by
    by_contra hne
    have ha₁₂ := distinct_component_contacts_have_same_anchor
      G S hK hcard hclique hfree C ha₁ ha₂
      w₁ w₂ hw₁C hw₂C hne hw₁a₁.symm hw₂a₂
    exact ha₂a₁ ha₁₂.symm
  subst w₂
  have hno_other_contact : ∀ u : ↥((S : Set V)ᶜ), u ∈ C.supp →
      u ≠ w₁ → ∀ b : V, b ∈ S → ¬G.Adj u.val b := by
    intro u huC huw b hb hub
    have hb₁ := distinct_component_contacts_have_same_anchor
      G S hK hcard hclique hfree C hb ha₁
      u w₁ huC hw₁C huw hub.symm hw₁a₁
    have hb₂ := distinct_component_contacts_have_same_anchor
      G S hK hcard hclique hfree C hb ha₂
      u w₁ huC hw₁C huw hub.symm hw₂a₂
    exact ha₂a₁ (hb₂.symm.trans hb₁)
  have hevery : ∀ u : ↥((S : Set V)ᶜ), u ∈ C.supp → u = w₁ := by
    intro u huC
    by_contra huw
    have huwVal : u.val ≠ w₁.val := fun h => huw (Subtype.ext h)
    have ha₁w : a₁ ≠ w₁.val := by
      intro h
      exact w₁.property (h ▸ ha₁)
    have ha₁outside :
        a₁ ∉ (Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp := by
      rintro ⟨z, _, hz⟩
      exact z.property (hz.symm ▸ ha₁)
    obtain ⟨x, hx, hxw, y, hy, _, hxy⟩ :=
      deletion_connected_boundary G
        ((Subtype.val : ↥((S : Set V)ᶜ) → V) '' C.supp)
        (hdelete w₁.val) ⟨u, huC, rfl⟩ huwVal ha₁outside ha₁w
    have hyS := component_boundary_lands_in_core G S C hx hy hxy
    obtain ⟨z, hzC, rfl⟩ := hx
    have hzw : z ≠ w₁ := by
      intro h
      exact hxw (congrArg Subtype.val h)
    exact hno_other_contact z hzC hzw y hyS hxy
  intro v w hvC hwC
  exact (hevery v hvC).trans (hevery w hwC).symm

/-- The actual graph outside the (K-2)-clique is edgeless. This is an ordinary
structural theorem; no original coloring or anti-Ramsey conclusion is asserted. -/
theorem outside_independent {V : Type*}
    (G : SimpleGraph V) (S : Finset V) {K : ℕ}
    (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected) :
    G.induce (S : Set V)ᶜ = ⊥ := by
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro v w hvw
  let C := (G.induce (S : Set V)ᶜ).connectedComponentMk v
  have hvC : v ∈ C.supp := rfl
  have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hvw
  have heq := outside_component_subsingleton
    G S hK hcard hclique hfree hdelete C v w hvC hwC
  exact hvw.ne heq

end ErdosProblems.PathUpperReduction.LargeCoreStructure1105

namespace ErdosProblems.PathUpperReduction.CommonAnchors1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CliqueSpanningPath1105
open ErdosProblems.PathUpperReduction.LargeCoreStructure1105

theorem exact_cycle_of_clique_ear {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {a b : V} (hclique : G.IsClique (S : Set V))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (Q : G.Walk a b) (hQ : Q.IsPath) (hQL : 3 ≤ Q.length)
    (hcontact : ∀ z, z ∈ Q.support → z ∈ S → z = a ∨ z = b) :
    cycleGraph (Q.length + (S.card - 1)) ⊑ G := by
  classical
  obtain ⟨P, hP, hPlength, hPsupport⟩ :=
    exists_clique_spanning_path G S hclique ha hb hab
  have hcycle : (P.append Q.reverse).IsCycle := by
    apply hP.isCycle_append hQ.reverse
    · intro z hzP hzQ
      have hzPs : z ∈ P.support := List.mem_of_mem_tail hzP
      have hzQs : z ∈ Q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hzQ
      rcases hcontact z hzQs ((hPsupport z).mp hzPs) with hza | hzb
      · exact path_start_notMem_tail P hP (hza ▸ hzP)
      · exact path_start_notMem_tail Q.reverse hQ.reverse (hzb ▸ hzQ)
    · right
      simp only [Walk.length_reverse]
      omega
  apply (cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨a, P.append Q.reverse, hcycle, ?_⟩
  simp only [Walk.length_append, Walk.length_reverse, hPlength, Nat.add_comm]

theorem cycle_of_shared_neighbor_pairs {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    {u v a b c : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hau : G.Adj a u) (hub : G.Adj u b)
    (hbv : G.Adj b v) (hvc : G.Adj v c) :
    cycleGraph K ⊑ G := by
  classical
  let R : Finset V := S.erase b
  have hRclique : G.IsClique (R : Set V) :=
    SimpleGraph.IsClique.subset (by
      intro z hz
      exact Finset.mem_of_mem_erase hz) hclique
  have haR : a ∈ R := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hcR : c ∈ R := Finset.mem_erase.mpr ⟨hbc.symm, hc⟩
  have hxu (x : V) (hx : x ∈ S) : x ≠ u := fun h => hu (h ▸ hx)
  have hxv (x : V) (hx : x ∈ S) : x ≠ v := fun h => hv (h ▸ hx)
  let Q : G.Walk a c := Walk.cons hau
    (Walk.cons hub (Walk.cons hbv (Walk.cons hvc Walk.nil)))
  have hQ : Q.IsPath := by
    rw [Walk.isPath_def]
    change [a, u, b, v, c].Nodup
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_false_eq_true]
    grind
  have hQL : Q.length = 4 := by simp [Q]
  have hcontact : ∀ z, z ∈ Q.support → z ∈ R → z = a ∨ z = c := by
    intro z hzQ hzR
    have hzCases : z = a ∨ z = u ∨ z = b ∨ z = v ∨ z = c := by
      simpa only [Q, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] using hzQ
    rcases hzCases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hu (Finset.mem_of_mem_erase hzR)).elim
    · exact ((Finset.mem_erase.mp hzR).1 rfl).elim
    · exact (hv (Finset.mem_of_mem_erase hzR)).elim
    · exact Or.inr rfl
  have hRcard : R.card + 1 = S.card := Finset.card_erase_add_one hb
  have horder : Q.length + (R.card - 1) = K := by omega
  have hcopy := exact_cycle_of_clique_ear G R hRclique haR hcR hac
    Q hQ (by omega) hcontact
  rw [horder] at hcopy
  exact hcopy

theorem cycle_of_disjoint_neighbor_pairs {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    {u v a b c d : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hau : G.Adj a u) (hub : G.Adj u b)
    (hcv : G.Adj c v) (hvd : G.Adj v d) :
    cycleGraph K ⊑ G := by
  classical
  let R : Finset V := (S.erase b).erase c
  have hRclique : G.IsClique (R : Set V) :=
    SimpleGraph.IsClique.subset (by
      intro z hz
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)) hclique
  have haR : a ∈ R :=
    Finset.mem_erase.mpr ⟨hac, Finset.mem_erase.mpr ⟨hab, ha⟩⟩
  have hdR : d ∈ R :=
    Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_erase.mpr ⟨hbd.symm, hd⟩⟩
  have hxu (x : V) (hx : x ∈ S) : x ≠ u := fun h => hu (h ▸ hx)
  have hxv (x : V) (hx : x ∈ S) : x ≠ v := fun h => hv (h ▸ hx)
  have hbcAdj : G.Adj b c := hclique hb hc hbc
  let Q : G.Walk a d := Walk.cons hau
    (Walk.cons hub (Walk.cons hbcAdj (Walk.cons hcv (Walk.cons hvd Walk.nil))))
  have hQ : Q.IsPath := by
    rw [Walk.isPath_def]
    change [a, u, b, c, v, d].Nodup
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_false_eq_true]
    grind
  have hQL : Q.length = 5 := by simp [Q]
  have hcontact : ∀ z, z ∈ Q.support → z ∈ R → z = a ∨ z = d := by
    intro z hzQ hzR
    have hzCases : z = a ∨ z = u ∨ z = b ∨ z = c ∨ z = v ∨ z = d := by
      simpa only [Q, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] using hzQ
    rcases hzCases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hu (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzR))).elim
    · exact ((Finset.mem_erase.mp (Finset.mem_of_mem_erase hzR)).1 rfl).elim
    · exact ((Finset.mem_erase.mp hzR).1 rfl).elim
    · exact (hv (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzR))).elim
    · exact Or.inr rfl
  have hcErase : c ∈ S.erase b := Finset.mem_erase.mpr ⟨hbc.symm, hc⟩
  have hRcard : R.card + 1 = (S.erase b).card := Finset.card_erase_add_one hcErase
  have hScard : (S.erase b).card + 1 = S.card := Finset.card_erase_add_one hb
  have horder : Q.length + (R.card - 1) = K := by omega
  have hcopy := exact_cycle_of_clique_ear G R hRclique haR hdR had
    Q hQ (by omega) hcontact
  rw [horder] at hcopy
  exact hcopy

end ErdosProblems.PathUpperReduction.CommonAnchors1105

namespace ErdosProblems.PathUpperReduction.CommonAnchors1105
open SimpleGraph
open ErdosProblems.PathUpperReduction.LargeCoreStructure1105

theorem outside_contact_avoiding {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hcard : 1 < S.card)
    (hind : G.induce (S : Set V)ᶜ = ⊥)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    {u a : V} (hu : u ∉ S) (ha : a ∈ S) :
    ∃ b : V, b ∈ S ∧ b ≠ a ∧ G.Adj u b := by
  classical
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne hcard a
  have hua : u ≠ a := fun h => hu (h.symm ▸ ha)
  have hcu : c ∉ ({u} : Set V) := by
    intro h
    have hcu : c = u := h
    exact hu (hcu ▸ hc)
  obtain ⟨x, hx, _, y, _, hya, hxy⟩ :=
    deletion_connected_boundary G ({u} : Set V)
      (hdelete a) (by simp) hua hcu hca
  have hxu : x = u := hx
  subst x
  have hyS : y ∈ S := by
    by_contra hyS
    have hbad : (G.induce (S : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨y, hyS⟩ := hxy
    rw [hind] at hbad
    exact hbad
  exact ⟨y, hyS, hya, hxy⟩

theorem outside_two_core_neighbors {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hcard : 1 < S.card)
    (hind : G.induce (S : Set V)ᶜ = ⊥)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    {u : V} (hu : u ∉ S) :
    ∃ a b : V, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨a, ha, _, hua⟩ := outside_contact_avoiding G S hcard hind hdelete hu hc
  obtain ⟨b, hb, hba, hub⟩ := outside_contact_avoiding G S hcard hind hdelete hu ha
  exact ⟨a, b, ha, hb, hba.symm, hua, hub⟩

/-- One anchor from a second actual neighbor pair lies in the first pair:
otherwise an explicit shared or disjoint pair cycle has forbidden order K. -/
theorem neighbor_pair_member {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    {u v a b c d : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hau : G.Adj a u) (hub : G.Adj u b)
    (hcv : G.Adj c v) (hvd : G.Adj v d) : c = a ∨ c = b := by
  classical
  by_contra hnot
  have hac : a ≠ c := fun h => hnot (Or.inl h.symm)
  have hbc : b ≠ c := fun h => hnot (Or.inr h.symm)
  by_cases had : a = d
  · subst d
    exact hfree K le_rfl (cycle_of_shared_neighbor_pairs G S hK hcard hclique
      hu hv huv hb ha hc hab.symm hbc hac
      hub.symm hau.symm hvd.symm hcv.symm)
  by_cases hbd : b = d
  · subst d
    exact hfree K le_rfl (cycle_of_shared_neighbor_pairs G S hK hcard hclique
      hu hv huv ha hb hc hab hac hbc
      hau hub hvd.symm hcv.symm)
  exact hfree K le_rfl (cycle_of_disjoint_neighbor_pairs G S hK hcard hclique
    hu hv huv ha hb hc hd hab hac had hbc hbd hcd hau hub hcv hvd)

/-- Every actual neighbor of u belongs to the distinct actual neighbor pair
at v. The extra distinct neighbor at u is constructed, not supplied. -/
theorem neighbors_covered_by_other_pair {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hind : G.induce (S : Set V)ᶜ = ⊥)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    {u v a b : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hva : G.Adj v a) (hvb : G.Adj v b) :
    ∀ z : V, G.Adj u z → z = a ∨ z = b := by
  classical
  have hScard : 1 < S.card := by omega
  intro z huz
  have hzS : z ∈ S := by
    by_contra hzS
    have hbad : (G.induce (S : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨z, hzS⟩ := huz
    rw [hind] at hbad
    exact hbad
  obtain ⟨t, ht, htz, hut⟩ := outside_contact_avoiding G S hScard hind hdelete hu hzS
  exact neighbor_pair_member G S hK hcard hclique hfree
    hv hu huv.symm ha hb hzS ht hab htz.symm hva.symm hvb huz.symm hut

/-- Under the literal large-core and ALL-cycle hypotheses, two distinct actual
outside vertices force one COMMON exact two-anchor neighborhood for every
outside vertex. In particular all outside vertices are independent. -/
theorem exists_common_exact_two_anchors {V : Type*} (G : SimpleGraph V)
    (S : Finset V) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : G.IsClique (S : Set V))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free G)
    (hdelete : ∀ a : V, (G.induce {z : V | z ≠ a}).Connected)
    (houtside : ∃ u v : V, u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    G.induce (S : Set V)ᶜ = ⊥ ∧
      ∃ a b : V, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
        ∀ u : V, u ∉ S → ∀ z : V, G.Adj u z ↔ z = a ∨ z = b := by
  classical
  have hind := outside_independent G S hK hcard hclique hfree hdelete
  have hScard : 1 < S.card := by omega
  obtain ⟨u₀, v₀, hu₀, hv₀, hu₀v₀⟩ := houtside
  obtain ⟨a, b, ha, hb, hab, hu₀a, hu₀b⟩ :=
    outside_two_core_neighbors G S hScard hind hdelete hu₀
  obtain ⟨c, d, hc, hd, hcd, hv₀c, hv₀d⟩ :=
    outside_two_core_neighbors G S hScard hind hdelete hv₀
  have hcoverV := neighbors_covered_by_other_pair G S hK hcard hclique hfree
    hind hdelete hv₀ hu₀ hu₀v₀.symm ha hb hab hu₀a hu₀b
  have hcAB : c = a ∨ c = b := hcoverV c hv₀c
  have hdAB : d = a ∨ d = b := hcoverV d hv₀d
  have hsubset : ∀ u : V, u ∉ S → ∀ z : V, G.Adj u z → z = a ∨ z = b := by
    intro u hu z huz
    by_cases huu₀ : u = u₀
    · subst u
      have hzCD := neighbors_covered_by_other_pair G S hK hcard hclique hfree
        hind hdelete hu₀ hv₀ hu₀v₀ hc hd hcd hv₀c hv₀d z huz
      rcases hzCD with rfl | rfl
      · exact hcAB
      · exact hdAB
    · exact neighbors_covered_by_other_pair G S hK hcard hclique hfree
        hind hdelete hu hu₀ huu₀ ha hb hab hu₀a hu₀b z huz
  refine ⟨hind, a, b, ha, hb, hab, ?_⟩
  intro u hu z
  have hboth : G.Adj u a ∧ G.Adj u b := by
    obtain ⟨e, f, _, _, hef, hue, huf⟩ :=
      outside_two_core_neighbors G S hScard hind hdelete hu
    have he := hsubset u hu e hue
    have hf := hsubset u hu f huf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact (hef rfl).elim
    · exact ⟨hue, huf⟩
    · exact ⟨huf, hue⟩
    · exact (hef rfl).elim
  constructor
  · exact hsubset u hu z
  · rintro (rfl | rfl)
    · exact hboth.1
    · exact hboth.2

end ErdosProblems.PathUpperReduction.CommonAnchors1105

namespace ErdosProblems.PathUpperReduction.ConeCoreApplication1105
open SimpleGraph
open ErdosProblems.PathUpperReduction.CommonAnchors1105

/-- Literal `Option` cone adding a universal apex `none`. -/
def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a
    · exact id
    · exact G.loopless.irrefl _⟩

/-- The universal apex is forced INTO the actual core and is one of the two
common anchors. The other actual anchor is an original vertex. -/
theorem cone_common_anchor {V : Type*} (G : SimpleGraph V)
    (S : Finset (Option V)) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : (cone G).IsClique (S : Set (Option V)))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free (cone G))
    (hdelete : ∀ a : Option V,
      ((cone G).induce {z : Option V | z ≠ a}).Connected)
    (houtside : ∃ u v : Option V, u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    none ∈ S ∧ ∃ b : V, some b ∈ S ∧
      ∀ u : Option V, u ∉ S → ∀ z : Option V,
        (cone G).Adj u z ↔ z = none ∨ z = some b := by
  classical
  obtain ⟨_, a, b, ha, hb, hab, hneighbors⟩ :=
    exists_common_exact_two_anchors (cone G) S hK hcard hclique hfree hdelete houtside
  have hnoneS : (none : Option V) ∈ S := by
    by_contra hnoneS
    have hsubset : S ⊆ ({a, b} : Finset (Option V)) := by
      intro z hz
      have hadj : (cone G).Adj none z := by
        cases z with
        | none => exact (hnoneS hz).elim
        | some z => trivial
      have hcases := (hneighbors none hnoneS z).mp hadj
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
    have hsmall : S.card ≤ 2 := (Finset.card_le_card hsubset).trans Finset.card_le_two
    omega
  have hnonePair : (none : Option V) = a ∨ none = b := by
    obtain ⟨u, _, hu, _, _⟩ := houtside
    cases u with
    | none => exact (hu hnoneS).elim
    | some u => exact (hneighbors (some u) hu none).mp (by trivial)
  refine ⟨hnoneS, ?_⟩
  rcases hnonePair with hna | hnb
  · subst a
    cases b with
    | none => exact (hab rfl).elim
    | some b =>
      exact ⟨b, hb, hneighbors⟩
  · subst b
    cases a with
    | none => exact (hab rfl).elim
    | some a =>
      refine ⟨a, ha, ?_⟩
      intro u hu z
      exact (hneighbors u hu z).trans or_comm

/-- Pull the actual cone core back to original vertices. It is an actual
clique, and every original outside vertex has exactly the ONE original anchor
as its full neighborhood. No finite count or graph isomorphism is supplied. -/
theorem cone_core_partition {V : Type*} (G : SimpleGraph V)
    (S : Finset (Option V)) {K : ℕ} (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : (cone G).IsClique (S : Set (Option V)))
    (hfree : ∀ m : ℕ, K ≤ m → (cycleGraph m).Free (cone G))
    (hdelete : ∀ a : Option V,
      ((cone G).induce {z : Option V | z ≠ a}).Connected)
    (houtside : ∃ u v : Option V, u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    let T : Set V := {v : V | some v ∈ S}
    none ∈ S ∧ G.IsClique T ∧
      ∃ b : V, b ∈ T ∧ ∀ u : V, u ∉ T → ∀ z : V, G.Adj u z ↔ z = b := by
  classical
  dsimp only
  obtain ⟨hnoneS, b, hb, hneighbors⟩ :=
    cone_common_anchor G S hK hcard hclique hfree hdelete houtside
  have hTclique : G.IsClique {v : V | some v ∈ S} := by
    intro u hu v hv huv
    exact hclique hu hv (fun h => huv (Option.some.inj h))
  refine ⟨hnoneS, hTclique, b, hb, ?_⟩
  intro u hu z
  have h := hneighbors (some u) hu (some z)
  change G.Adj u z ↔ some z = none ∨ some z = some b at h
  simpa only [Option.some_ne_none, false_or, Option.some.injEq] using h

end ErdosProblems.PathUpperReduction.ConeCoreApplication1105

namespace ErdosProblems.PathUpperReduction.ConeFiniteContainer1105
open SimpleGraph
open ErdosProblems.PathUpperReduction.ConeCoreApplication1105

theorem finite_pullback_cardinality {n K : ℕ} (S : Finset (Option (Fin n)))
    (hK : 5 ≤ K) (hcard : S.card = K - 2) (hnone : none ∈ S)
    (houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    let T : Set (Fin n) := {v | some v ∈ S}
    Fintype.card T = K - 3 ∧
      Fintype.card (Tᶜ : Set (Fin n)) = n - (K - 3) ∧
      2 ≤ K - 3 ∧ 2 ≤ n - (K - 3) ∧
      (K - 3) + (n - (K - 3)) = n := by
  classical
  dsimp only
  let A : Finset (Fin n) := Finset.univ.filter (fun v => some v ∈ S)
  have hS : S = insert none (A.image some) := by
    ext z
    cases z <;> simp [A, hnone]
  have hnoneImage : (none : Option (Fin n)) ∉ A.image some := by simp
  have himageCard : (A.image some).card = A.card :=
    Finset.card_image_of_injective A (fun _ _ h => Option.some.inj h)
  have hAcard : A.card = K - 3 := by
    have hScard := congrArg Finset.card hS
    rw [Finset.card_insert_of_notMem hnoneImage, himageCard] at hScard
    omega
  have hTcard : Fintype.card {v : Fin n | some v ∈ S} = K - 3 := by
    exact (Fintype.card_of_subtype A (by intro v; simp [A])).trans hAcard
  have hTcCard : Fintype.card ({v : Fin n | some v ∈ S}ᶜ : Set (Fin n)) =
      n - (K - 3) := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hTcard]
  have hAcCard : Aᶜ.card = n - (K - 3) := by
    rw [Finset.card_compl, Fintype.card_fin, hAcard]
  have hlargeOutside : 2 ≤ n - (K - 3) := by
    obtain ⟨u, v, hu, hv, huv⟩ := houtside
    cases u with
    | none => exact (hu hnone).elim
    | some u =>
      cases v with
      | none => exact (hv hnone).elim
      | some v =>
        have huv' : u ≠ v := fun h => huv (congrArg some h)
        have hpair : ({u, v} : Finset (Fin n)) ⊆ Aᶜ := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · simp [A, hu]
          · have hzv : z = v := Finset.mem_singleton.mp hz
            subst z
            simp [A, hv]
        have hle := Finset.card_le_card hpair
        rw [Finset.card_pair huv', hAcCard] at hle
        exact hle
  have hAn : K - 3 ≤ n := by
    have hle := Finset.card_le_card (Finset.subset_univ A)
    simpa only [hAcard, Finset.card_univ, Fintype.card_fin] using hle
  exact ⟨hTcard, hTcCard, by omega, hlargeOutside, by omega⟩

/-- A finite actual clique/hub partition has a full spanning enumeration whose
first core vertex is the actual hub and whose full adjacency is exact. -/
theorem finite_clique_hub_enumeration {n m l : ℕ}
    (G : SimpleGraph (Fin n)) (T : Set (Fin n)) [DecidablePred (· ∈ T)] (hm : 0 < m)
    (hTcard : Fintype.card T = m)
    (hTcCard : Fintype.card (Tᶜ : Set (Fin n)) = l)
    (hclique : G.IsClique T) (b : Fin n) (hb : b ∈ T)
    (hneighbors : ∀ u : Fin n, u ∉ T → ∀ z : Fin n, G.Adj u z ↔ z = b) :
    ∃ e : (Fin m ⊕ Fin l) ≃ Fin n,
      e (Sum.inl ⟨0, hm⟩) = b ∧
      Set.range (fun i : Fin m => e (Sum.inl i)) = T ∧
      Set.range (fun j : Fin l => e (Sum.inr j)) = Tᶜ ∧
      ∀ x y : Fin m ⊕ Fin l, G.Adj (e x) (e y) ↔
        match x, y with
        | Sum.inl i, Sum.inl j => i ≠ j
        | Sum.inl i, Sum.inr _ => i.val = 0
        | Sum.inr _, Sum.inl j => j.val = 0
        | Sum.inr _, Sum.inr _ => False := by
  classical
  let e₀ : Fin m ≃ T := (Fintype.equivFinOfCardEq hTcard).symm
  let eL : Fin m ≃ T :=
    (Equiv.swap ⟨0, hm⟩ (e₀.symm ⟨b, hb⟩)).trans e₀
  let eR : Fin l ≃ (Tᶜ : Set (Fin n)) := (Fintype.equivFinOfCardEq hTcCard).symm
  let e : (Fin m ⊕ Fin l) ≃ Fin n :=
    (Equiv.sumCongr eL eR).trans (Equiv.Set.sumCompl T)
  have hzero : (eL ⟨0, hm⟩).val = b := by
    dsimp only [eL, Equiv.trans_apply]
    rw [Equiv.swap_apply_left]
    simp only [Equiv.apply_symm_apply]
  have hhub (i : Fin m) : (eL i).val = b ↔ i.val = 0 := by
    constructor
    · intro h
      have hi : i = ⟨0, hm⟩ :=
        eL.injective (Subtype.ext (h.trans hzero.symm))
      exact congrArg Fin.val hi
    · intro hi
      have hiz : i = ⟨0, hm⟩ := Fin.ext hi
      simpa only [hiz] using hzero
  have hleft (i : Fin m) : e (Sum.inl i) = (eL i).val := rfl
  have hright (j : Fin l) : e (Sum.inr j) = (eR j).val := rfl
  have hleftRange : Set.range (fun i : Fin m => e (Sum.inl i)) = T := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (eL i).property
    · intro hx
      refine ⟨eL.symm ⟨x, hx⟩, ?_⟩
      change (eL (eL.symm ⟨x, hx⟩)).val = x
      simp only [Equiv.apply_symm_apply]
  have hrightRange : Set.range (fun j : Fin l => e (Sum.inr j)) = Tᶜ := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (eR j).property
    · intro hx
      refine ⟨eR.symm ⟨x, hx⟩, ?_⟩
      change (eR (eR.symm ⟨x, hx⟩)).val = x
      simp only [Equiv.apply_symm_apply]
  refine ⟨e, hzero, hleftRange, hrightRange, ?_⟩
  intro x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change G.Adj (eL i).val (eL j).val ↔ i ≠ j
      constructor
      · intro h hij
        exact h.ne (congrArg (fun t : Fin m => (eL t).val) hij)
      · intro hij
        exact hclique (eL i).property (eL j).property
          (fun h => hij (eL.injective (Subtype.ext h)))
    | inr j =>
      change G.Adj (eL i).val (eR j).val ↔ i.val = 0
      constructor
      · intro h
        exact (hhub i).mp ((hneighbors _ (eR j).property _).mp h.symm)
      · intro hi
        exact ((hneighbors _ (eR j).property _).mpr ((hhub i).mpr hi)).symm
  | inr i =>
    cases y with
    | inl j =>
      change G.Adj (eR i).val (eL j).val ↔ j.val = 0
      exact (hneighbors _ (eR i).property _).trans (hhub j)
    | inr j =>
      change G.Adj (eR i).val (eR j).val ↔ False
      constructor
      · intro h
        have hval := (hneighbors _ (eR i).property _).mp h
        exact (eR j).property (hval.symm ▸ hb)
      · exact False.elim

/-- Literal actual-cone caller: the finite cardinalities, hub, spanning
equivalence and full original adjacency are all conclusions. -/
theorem cone_finite_container {n K : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Option (Fin n))) (hK : 5 ≤ K) (hcard : S.card = K - 2)
    (hclique : (cone G).IsClique (S : Set (Option (Fin n))))
    (hfree : ∀ r : ℕ, K ≤ r → (cycleGraph r).Free (cone G))
    (hdelete : ∀ a : Option (Fin n),
      ((cone G).induce {z : Option (Fin n) | z ≠ a}).Connected)
    (houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v) :
    let m := K - 3
    let l := n - m
    let T : Set (Fin n) := {v | some v ∈ S}
    2 ≤ m ∧ 2 ≤ l ∧ m + l = n ∧ Fintype.card T = m ∧
      ∃ b : Fin n, ∃ e : (Fin m ⊕ Fin l) ≃ Fin n,
        b ∈ T ∧ e (Sum.inl ⟨0, by omega⟩) = b ∧
        Set.range (fun i : Fin m => e (Sum.inl i)) = T ∧
        Set.range (fun j : Fin l => e (Sum.inr j)) = Tᶜ ∧
        ∀ x y : Fin m ⊕ Fin l, G.Adj (e x) (e y) ↔
          match x, y with
          | Sum.inl i, Sum.inl j => i ≠ j
          | Sum.inl i, Sum.inr _ => i.val = 0
          | Sum.inr _, Sum.inl j => j.val = 0
          | Sum.inr _, Sum.inr _ => False := by
  classical
  dsimp only
  obtain ⟨hnone, hTclique, b, hb, hneighbors⟩ :=
    cone_core_partition G S hK hcard hclique hfree hdelete houtside
  obtain ⟨hTcard, hTcCard, hm, hl, hsum⟩ :=
    finite_pullback_cardinality S hK hcard hnone houtside
  obtain ⟨e, hezero, heleft, heright, headj⟩ :=
    finite_clique_hub_enumeration G {v : Fin n | some v ∈ S}
      (by omega : 0 < K - 3) hTcard hTcCard hTclique b hb hneighbors
  exact ⟨hm, hl, hsum, hTcard, b, e, hb, hezero, heleft, heright, headj⟩

end ErdosProblems.PathUpperReduction.ConeFiniteContainer1105

end

namespace ErdosProblems.PathUpperReduction.CoreEndpointBound1105

def extremalCount (N K a : ℕ) : ℕ :=
  (K - a).choose 2 + a * (N - K + a)

theorem extremalCount_cast (N K a : ℕ) (haK : a ≤ K) (hKN : K ≤ N) :
    2 * (extremalCount N K a : ℚ) =
      3 * (a : ℚ) ^ 2 + (2 * (N : ℚ) - 4 * (K : ℚ) + 1) * (a : ℚ) +
        (K : ℚ) ^ 2 - (K : ℚ) := by
  simp only [extremalCount, Nat.cast_add, Nat.cast_mul,
    Nat.cast_choose_two, Nat.cast_sub haK, Nat.cast_sub hKN]
  ring

theorem extremalCount_endpoints (N K a : ℕ) (hK : 5 ≤ K) (hKN : K ≤ N)
    (ha : 2 ≤ a) (hat : a ≤ (K - 1) / 2) :
    extremalCount N K a ≤
      max (extremalCount N K 2) (extremalCount N K ((K - 1) / 2)) := by
  let t : ℕ := (K - 1) / 2
  have ht2 : 2 ≤ t := by dsimp [t]; omega
  have htK : t ≤ K := by dsimp [t]; omega
  have hat' : a ≤ t := hat
  have haK : a ≤ K := le_trans hat' htK
  have h2K : 2 ≤ K := by omega
  by_cases haeq : a = 2
  · subst a
    exact le_max_left _ _
  have hlt : 2 < t := by omega
  have haq : (2 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have htaq : (a : ℚ) ≤ (t : ℚ) := Nat.cast_le.mpr hat'
  have htq : (2 : ℚ) < (t : ℚ) := Nat.cast_lt.mpr hlt
  have hw₁ : 0 ≤ (t : ℚ) - (a : ℚ) := sub_nonneg.mpr htaq
  have hw₂ : 0 ≤ (a : ℚ) - 2 := sub_nonneg.mpr haq
  have hw : 0 < (t : ℚ) - 2 := sub_pos.mpr htq
  have hpoly₂ := extremalCount_cast N K 2 h2K hKN
  have hpoly_t := extremalCount_cast N K t htK hKN
  have hpoly_a := extremalCount_cast N K a haK hKN
  have hchord :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount N K 2 : ℚ)) +
          ((a : ℚ) - 2) * (2 * (extremalCount N K t : ℚ)) -
          ((t : ℚ) - 2) * (2 * (extremalCount N K a : ℚ)) =
        3 * ((t : ℚ) - 2) * ((a : ℚ) - 2) * ((t : ℚ) - (a : ℚ)) := by
    rw [hpoly₂, hpoly_t, hpoly_a]
    ring
  have hproduct :
      0 ≤ 3 * ((t : ℚ) - 2) * ((a : ℚ) - 2) * ((t : ℚ) - (a : ℚ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hw)) hw₂) hw₁
  have hinterp :
      ((t : ℚ) - 2) * (2 * (extremalCount N K a : ℚ)) ≤
        ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount N K 2 : ℚ)) +
          ((a : ℚ) - 2) * (2 * (extremalCount N K t : ℚ)) := by
    linarith [hchord, hproduct]
  let M : ℕ := max (extremalCount N K 2) (extremalCount N K t)
  have h₂M : (extremalCount N K 2 : ℚ) ≤ (M : ℚ) :=
    Nat.cast_le.mpr (le_max_left _ _)
  have htM : (extremalCount N K t : ℚ) ≤ (M : ℚ) :=
    Nat.cast_le.mpr (le_max_right _ _)
  have h₂M' : 2 * (extremalCount N K 2 : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have htM' : 2 * (extremalCount N K t : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have hweighted :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount N K 2 : ℚ)) +
          ((a : ℚ) - 2) * (2 * (extremalCount N K t : ℚ)) ≤
        ((t : ℚ) - 2) * (2 * (M : ℚ)) := by
    calc
      _ ≤ ((t : ℚ) - (a : ℚ)) * (2 * (M : ℚ)) +
          ((a : ℚ) - 2) * (2 * (M : ℚ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h₂M' hw₁)
          (mul_le_mul_of_nonneg_left htM' hw₂)
      _ = _ := by ring
  have htwice : 2 * (extremalCount N K a : ℚ) ≤ 2 * (M : ℚ) :=
    le_of_mul_le_mul_left (le_trans hinterp hweighted) hw
  have hq : (extremalCount N K a : ℚ) ≤ (M : ℚ) := by linarith
  exact Nat.cast_le.mp hq

theorem emptyCoreCount_le_endpoint (N K : ℕ) (hK : 5 ≤ K) (hKN : K ≤ N) :
    ((K - 1) / 2).choose 2 + ((K - 1) / 2) * (N - (K - 1) / 2) ≤
      extremalCount N K ((K - 1) / 2) := by
  let t : ℕ := (K - 1) / 2
  have htK : t ≤ K := by dsimp [t]; omega
  have htN : t ≤ N := le_trans htK hKN
  have hpoly := extremalCount_cast N K t htK hKN
  have hphi :
      2 * ((t.choose 2 + t * (N - t) : ℕ) : ℚ) =
        (t : ℚ) * ((t : ℚ) - 1) + 2 * (t : ℚ) * ((N : ℚ) - (t : ℚ)) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_sub htN]
    ring
  have hparity : K = 2 * t + 1 ∨ K = 2 * t + 2 := by dsimp [t]; omega
  have hq : ((t.choose 2 + t * (N - t) : ℕ) : ℚ) ≤
      (extremalCount N K t : ℚ) := by
    rcases hparity with hodd | heven
    · have hKq : (K : ℚ) = 2 * (t : ℚ) + 1 := by
        rw [hodd]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      rw [hKq] at hpoly
      nlinarith [hphi]
    · have hKq : (K : ℚ) = 2 * (t : ℚ) + 2 := by
        rw [heven]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hKq] at hpoly
      nlinarith [hphi]
  exact Nat.cast_le.mp hq

end ErdosProblems.PathUpperReduction.CoreEndpointBound1105

namespace ErdosProblems.PathUpperReduction.ConnectedPathScalarChecked1105

open ErdosProblems.PathUpperReduction.CoreEndpointBound1105

theorem extremalCount_cone_shift (n k a : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n)
    (_ha : 1 ≤ a) (hak : a ≤ k - 2) :
    extremalCount (n + 1) (k + 1) (a + 1) =
      n + extremalCount n (k - 1) a := by
  let u : ℕ := k - 1 - a
  let b : ℕ := n - (k - 1) + a
  have hleft : k + 1 - (a + 1) = u + 1 := by dsimp [u]; omega
  have htail : n + 1 - (k + 1) + (a + 1) = b := by dsimp [b]; omega
  have hsum : u + b = n := by dsimp [u, b]; omega
  have hchoose : (u + 1).choose 2 = u + u.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' u 1
  unfold extremalCount
  rw [hleft, htail]
  change (u + 1).choose 2 + (a + 1) * b = n + (u.choose 2 + a * b)
  rw [hchoose]
  calc
    u + u.choose 2 + (a + 1) * b = (u + b) + (u.choose 2 + a * b) := by ring
    _ = n + (u.choose 2 + a * b) := by rw [hsum]

theorem cone_first_endpoint (n k : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    extremalCount (n + 1) (k + 1) 2 = n + extremalCount n (k - 1) 1 := by
  exact extremalCount_cone_shift n k 1 hk hkn (by omega) (by omega)

theorem cone_last_endpoint (n k : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    extremalCount (n + 1) (k + 1) ((k + 1 - 1) / 2) =
      n + extremalCount n (k - 1) ((k - 2) / 2) := by
  have ha : 1 ≤ (k - 2) / 2 := by omega
  have hak : (k - 2) / 2 ≤ k - 2 := by omega
  have hindex : (k - 2) / 2 + 1 = (k + 1 - 1) / 2 := by omega
  have hshift := extremalCount_cone_shift n k ((k - 2) / 2) hk hkn ha hak
  rw [hindex] at hshift
  exact hshift

theorem cone_endpoint_max (n k : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    max (extremalCount (n + 1) (k + 1) 2)
        (extremalCount (n + 1) (k + 1) ((k + 1 - 1) / 2)) =
      n + max (extremalCount n (k - 1) 1)
        (extremalCount n (k - 1) ((k - 2) / 2)) := by
  rw [cone_first_endpoint n k hk hkn, cone_last_endpoint n k hk hkn, ← add_max]

theorem cone_endpoint_bound_iff (n k e : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    (n + e ≤ max (extremalCount (n + 1) (k + 1) 2)
        (extremalCount (n + 1) (k + 1) ((k + 1 - 1) / 2))) ↔
      e ≤ max (extremalCount n (k - 1) 1)
        (extremalCount n (k - 1) ((k - 2) / 2)) := by
  rw [cone_endpoint_max n k hk hkn]
  exact add_le_add_iff_left n

end ErdosProblems.PathUpperReduction.ConnectedPathScalarChecked1105

section

open SimpleGraph
open ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.EvenCoverColorCaller1105

theorem rainbow_path_of_actual_vertex_cover_above_even_max {d n q : ℕ}
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Finset (Fin n)) (hX : X.card = d)
    (hcover : ∀ u v : Fin n, (selectedGraph χ r).Adj u v → u ∈ X ∨ v ∈ X)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    ∃ p : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  have hd2 : 2 ≤ d := le_trans (by decide : 2 ≤ 4) hd
  have hqB : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  exact ActualVertexCoverSellExit1105.rainbow_path_of_actual_vertex_cover
    hd2 hn χ r X hX hcover hqB

theorem palette_le_linear_of_actual_vertex_cover_and_no_rainbow {d n q : ℕ}
    (hd : 2 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Finset (Fin n)) (hX : X.card = d)
    (hcover : ∀ u v : Fin n, (selectedGraph χ r).Adj u v → u ∈ X ∨ v ∈ X)
    (hno : ∀ p : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow p.toHom χ) :
    q ≤ (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 := by
  by_contra hq
  have hqB : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q :=
    lt_of_not_ge hq
  obtain ⟨p, hp⟩ :=
    ActualVertexCoverSellExit1105.rainbow_path_of_actual_vertex_cover
      hd hn χ r X hX hcover hqB
  exact hno p hp

end ErdosProblems.PathUpperReduction.EvenCoverColorCaller1105

end

namespace ErdosProblems.EvenExceptionExchange
open SimpleGraph

abbrev Vertex (a b : ℕ) := Fin a ⊕ (Fin 3 ⊕ Fin b)
def isA {a b : ℕ} : Vertex a b → Prop
  | .inl _ => True | .inr _ => False
def isC {a b : ℕ} : Vertex a b → Prop
  | .inr (.inl _) => True | _ => False

/-- Literally K_a joined to the disjoint union K_3 and I_b. -/
def familyGraph (a b : ℕ) : SimpleGraph (Vertex a b) where
  Adj x y := x ≠ y ∧ (isA x ∨ isA y ∨ (isC x ∧ isC y))
  symm := by
    refine ⟨?_⟩
    intro x y h; rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩
  loopless := by
    refine ⟨?_⟩
    intro x h; exact h.1 rfl

/-- The existing local order-provider interface, now routed to ordinary Copy.
No coloring, maximality, degree hypothesis or graph classification is added. -/
def copy_of_avoiding_order {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (owner : G.edgeSet) (u v : V) (p : Fin (m + 1) → V)
    (hp : Function.Injective p)
    (havoid : ∀ i : Fin m,
      s(p (Fin.castSucc i), p (Fin.succ i)) = s(u, v) ∨
      (G.Adj (p (Fin.castSucc i)) (p (Fin.succ i)) ∧
       s(p (Fin.castSucc i), p (Fin.succ i)) ≠ owner.val)) :
    (pathGraph (m + 1)).Copy
      (G.deleteEdges {owner.val} ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) := by
  let T := G.deleteEdges {owner.val} ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  have hstep (i : Fin m) : T.Adj (p (Fin.castSucc i)) (p (Fin.succ i)) := by
    rcases havoid i with hnew | ⟨hold, hne⟩
    · apply (SimpleGraph.sup_adj _ _ _ _).mpr
      right
      change s(p (Fin.castSucc i), p (Fin.succ i)) ∈ ({s(u, v)} : Set (Sym2 V)) ∧ p (Fin.castSucc i) ≠ p (Fin.succ i)
      constructor
      · simpa only [Set.mem_singleton_iff] using hnew
      · apply hp.ne
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
    · apply (SimpleGraph.sup_adj _ _ _ _).mpr
      left
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨hold, by simpa only [Set.mem_singleton_iff] using hne⟩
  refine ⟨⟨p, ?_⟩, hp⟩
  intro i j hij
  rcases (pathGraph_adj.mp hij) with h | h
  · have hi : i.val < m := by have hj := j.isLt; omega
    let t : Fin m := ⟨i.val, hi⟩
    have hit : i = Fin.castSucc t := Fin.ext rfl
    have hjt : j = Fin.succ t := Fin.ext (by simpa only [Fin.val_succ] using h.symm)
    simpa only [hit, hjt] using hstep t
  · have hj : j.val < m := by have hi := i.isLt; omega
    let t : Fin m := ⟨j.val, hj⟩
    have hjt : j = Fin.castSucc t := Fin.ext rfl
    have hit : i = Fin.succ t := Fin.ext (by simpa only [Fin.val_succ] using h.symm)
    simpa only [hit, hjt] using T.symm.symm _ _ (hstep t)

end ErdosProblems.EvenExceptionExchange

namespace ErdosProblems.SaturatedEvenH

open SimpleGraph

abbrev MotifVertex (ell : ℕ) := Fin (ell - 1) ⊕ (Fin 3 ⊕ Fin ell)

def aVertex {ell : ℕ} (a : Fin (ell - 1)) : MotifVertex ell := Sum.inl a
def cVertex {ell : ℕ} (c : Fin 3) : MotifVertex ell := Sum.inr (Sum.inl c)
def bVertex {ell : ℕ} (b : Fin ell) : MotifVertex ell := Sum.inr (Sum.inr b)

def isA {ell : ℕ} : MotifVertex ell → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

def isC {ell : ℕ} : MotifVertex ell → Prop
  | Sum.inl _ => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

/-- Exactly the clique on A union C and the complete A-B bipartite graph. -/
def motifGraph (ell : ℕ) : SimpleGraph (MotifVertex ell) where
  Adj x y := x ≠ y ∧ (isA x ∨ isA y ∨ (isC x ∧ isC y))
  symm := by
    refine ⟨?_⟩
    intro x y h
    exact ⟨h.1.symm, by tauto⟩
  loopless := by
    refine ⟨?_⟩
    intro x h
    exact h.1 rfl

def aZero {ell : ℕ} (hell : 2 ≤ ell) : Fin (ell - 1) := ⟨0, by omega⟩
def bZero {ell : ℕ} (hell : 2 ≤ ell) : Fin ell := ⟨0, by omega⟩
def bOne {ell : ℕ} (hell : 2 ≤ ell) : Fin ell := ⟨1, by omega⟩

def chord {ell : ℕ} (hell : 2 ≤ ell) : Sym2 (MotifVertex ell) :=
  s(bVertex (bZero hell), bVertex (bOne hell))

/-- T2 for ell=2, and T for all ell>=3. No extra tail vertex is supplied. -/
def baseOrder {ell : ℕ} (hell : 2 ≤ ell)
    (i : Fin (2 * ell + 2)) : MotifVertex ell :=
  if h0 : i.val = 0 then bVertex (bZero hell)
  else if h1 : i.val = 1 then bVertex (bOne hell)
  else if h2 : i.val = 2 then aVertex (aZero hell)
  else if h3 : i.val = 3 then cVertex 0
  else if h4 : i.val = 4 then cVertex 1
  else if h5 : i.val = 5 then cVertex 2
  else if (i.val - 6) % 2 = 0 then
    aVertex ⟨(i.val - 6) / 2 + 1, by have hi := i.isLt; omega⟩
  else
    bVertex ⟨(i.val - 6) / 2 + 2, by have hi := i.isLt; omega⟩

/-- The literal position of each named vertex in T/T2. -/
def basePosition {ell : ℕ} (hell : 2 ≤ ell) : MotifVertex ell → Fin (2 * ell + 2)
  | Sum.inl a =>
    if a.val = 0 then ⟨2, by omega⟩
    else ⟨2 * a.val + 4, by have ha' := a.isLt; omega⟩
  | Sum.inr (Sum.inl c) => ⟨c.val + 3, by have hc := c.isLt; omega⟩
  | Sum.inr (Sum.inr b) =>
    if b.val = 0 then ⟨0, by omega⟩
    else if b.val = 1 then ⟨1, by omega⟩
    else ⟨2 * b.val + 3, by have hb := b.isLt; omega⟩

theorem basePosition_baseOrder {ell : ℕ} (hell : 2 ≤ ell)
    (i : Fin (2 * ell + 2)) : basePosition hell (baseOrder hell i) = i := by
  apply Fin.ext
  have hi := i.isLt
  dsimp [baseOrder]
  split_ifs <;> simp_all [basePosition, aZero, bZero, bOne,
    aVertex, bVertex, cVertex] <;> omega

theorem baseOrder_injective {ell : ℕ} (hell : 2 ≤ ell) :
    Function.Injective (baseOrder hell) := by
  intro i j hij
  have h := congrArg (basePosition hell) hij
  simpa only [basePosition_baseOrder] using h

theorem base_step_chord {ell : ℕ} (hell : 2 ≤ ell)
    (i : Fin (2 * ell + 1)) (hi : i.val = 0) :
    s(baseOrder hell (Fin.castSucc i), baseOrder hell (Fin.succ i)) = chord hell := by
  simp [baseOrder, chord, hi]

theorem base_step_old {ell : ℕ} (hell : 2 ≤ ell)
    (i : Fin (2 * ell + 1)) (hi : i.val ≠ 0) :
    (motifGraph ell).Adj (baseOrder hell (Fin.castSucc i))
      (baseOrder hell (Fin.succ i)) := by
  refine ⟨(baseOrder_injective hell).ne (by
    intro heq
    have h := congrArg Fin.val heq
    simp only [Fin.val_castSucc, Fin.val_succ] at h
    omega), ?_⟩
  have hib := i.isLt
  by_cases hsmall : i.val ≤ 5
  · have hcases : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
        i.val = 4 ∨ i.val = 5 := by omega
    rcases hcases with h1 | h2 | h3 | h4 | h5
    · right; left
      simp [baseOrder, Fin.val_succ, h1, isA, aVertex]
    · left
      simp [baseOrder, Fin.val_castSucc, h2, isA, aVertex]
    · right; right
      simp [baseOrder, Fin.val_castSucc, Fin.val_succ, h3, isC, cVertex]
    · right; right
      simp [baseOrder, Fin.val_castSucc, Fin.val_succ, h4, isC, cVertex]
    · right; left
      simp [baseOrder, Fin.val_succ, h5, isA, aVertex]
  · have h0 : i.val ≠ 0 := hi
    have h1 : i.val ≠ 1 := by omega
    have h2 : i.val ≠ 2 := by omega
    have h3 : i.val ≠ 3 := by omega
    have h4 : i.val ≠ 4 := by omega
    have h5 : i.val ≠ 5 := by omega
    by_cases hp : (i.val - 6) % 2 = 0
    · left
      simp [baseOrder, Fin.val_castSucc, h0, h1, h2, h3, h4, h5,
        hp, isA, aVertex]
    · have hs0 : i.val + 1 ≠ 0 := by omega
      have hs1 : i.val + 1 ≠ 1 := by omega
      have hs2 : i.val + 1 ≠ 2 := by omega
      have hs3 : i.val + 1 ≠ 3 := by omega
      have hs4 : i.val + 1 ≠ 4 := by omega
      have hs5 : i.val + 1 ≠ 5 := by omega
      have hsp : (i.val + 1 - 6) % 2 = 0 := by omega
      right; left
      dsimp only [baseOrder, Fin.val_succ]
      split_ifs <;> dsimp only [isA, aVertex, bVertex] <;> omega

theorem base_step_ne_of_positions {ell : ℕ} (hell : 2 ≤ ell)
    (x y : MotifVertex ell)
    (hpos : ¬ ((basePosition hell x).val + 1 = (basePosition hell y).val ∨
      (basePosition hell y).val + 1 = (basePosition hell x).val))
    (i : Fin (2 * ell + 1)) :
    s(baseOrder hell (Fin.castSucc i), baseOrder hell (Fin.succ i)) ≠ s(x, y) := by
  intro heq
  have h := congrArg (Sym2.map (basePosition hell)) heq
  simp only [Sym2.map_mk, basePosition_baseOrder] at h
  rcases Sym2.eq_iff.mp h with h | h
  · apply hpos
    left
    have hx := congrArg Fin.val h.1
    have hy := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ] at hx hy
    omega
  · apply hpos
    right
    have hx := congrArg Fin.val h.1
    have hy := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ] at hx hy
    omega

theorem positions_not_aa {ell : ℕ} (hell : 2 ≤ ell)
    (a a' : Fin (ell - 1)) :
    ¬ ((basePosition hell (aVertex a)).val + 1 =
        (basePosition hell (aVertex a')).val ∨
      (basePosition hell (aVertex a')).val + 1 =
        (basePosition hell (aVertex a)).val) := by
  have ha := a.isLt
  have ha' := a'.isLt
  simp only [basePosition, aVertex]
  split_ifs <;> simp_all only <;> omega

theorem positions_not_ac_middle {ell : ℕ} (hell : 2 ≤ ell)
    (a : Fin (ell - 1)) :
    ¬ ((basePosition hell (aVertex a)).val + 1 =
        (basePosition hell (cVertex (1 : Fin 3))).val ∨
      (basePosition hell (cVertex (1 : Fin 3))).val + 1 =
        (basePosition hell (aVertex a)).val) := by
  have ha := a.isLt
  simp only [basePosition, aVertex, cVertex]
  split_ifs <;> simp_all only <;> omega

theorem positions_not_ab_first {ell : ℕ} (hell : 2 ≤ ell)
    (a : Fin (ell - 1)) :
    ¬ ((basePosition hell (aVertex a)).val + 1 =
        (basePosition hell (bVertex (bZero hell))).val ∨
      (basePosition hell (bVertex (bZero hell))).val + 1 =
        (basePosition hell (aVertex a)).val) := by
  have ha := a.isLt
  have hz : (basePosition hell (bVertex (bZero hell))).val = 0 := rfl
  simp only [hz]
  simp only [basePosition, aVertex]
  split_ifs <;> simp_all

def partPerm {ell : ℕ} (α : Equiv.Perm (Fin (ell - 1)))
    (β : Equiv.Perm (Fin 3)) (δ : Equiv.Perm (Fin ell)) :
    Equiv.Perm (MotifVertex ell) := Equiv.sumCongr α (Equiv.sumCongr β δ)

theorem partPerm_old {ell : ℕ}
    (α : Equiv.Perm (Fin (ell - 1))) (β : Equiv.Perm (Fin 3))
    (δ : Equiv.Perm (Fin ell)) (x y : MotifVertex ell)
    (h : (motifGraph ell).Adj x y) :
    (motifGraph ell).Adj (partPerm α β δ x) (partPerm α β δ y) := by
  refine ⟨(partPerm α β δ).injective.ne h.1, ?_⟩
  rcases x with a | (c | b) <;> rcases y with a' | (c' | b') <;>
    simp_all [partPerm, motifGraph, isA, isC]

def AvoidsPair {ell : ℕ} (hell : 2 ≤ ell)
    (p : Fin (2 * ell + 2) → MotifVertex ell) (x y : MotifVertex ell) : Prop :=
  ∀ i : Fin (2 * ell + 1),
    s(p (Fin.castSucc i), p (Fin.succ i)) = chord hell ∨
      ((motifGraph ell).Adj (p (Fin.castSucc i)) (p (Fin.succ i)) ∧
        s(p (Fin.castSucc i), p (Fin.succ i)) ≠ s(x, y))

theorem avoidingPair_symm {ell : ℕ} (hell : 2 ≤ ell)
    (p : Fin (2 * ell + 2) → MotifVertex ell) (x y : MotifVertex ell)
    (hp : AvoidsPair hell p x y) : AvoidsPair hell p y x := by
  intro i
  rcases hp i with h | ⟨h, hne⟩
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    simpa only [Sym2.eq_swap] using hne

theorem build_avoiding_pair {ell : ℕ} (hell : 2 ≤ ell)
    (x y : MotifVertex ell)
    (α : Equiv.Perm (Fin (ell - 1))) (β : Equiv.Perm (Fin 3))
    (δ : Equiv.Perm (Fin ell))
    (hchord : Sym2.map (partPerm α β δ) (chord hell) = chord hell)
    (hpos : ¬ ((basePosition hell ((partPerm α β δ).symm x)).val + 1 =
        (basePosition hell ((partPerm α β δ).symm y)).val ∨
      (basePosition hell ((partPerm α β δ).symm y)).val + 1 =
        (basePosition hell ((partPerm α β δ).symm x)).val)) :
    ∃ p : Fin (2 * ell + 2) → MotifVertex ell,
      Function.Injective p ∧ AvoidsPair hell p x y := by
  let σ := partPerm α β δ
  let p := σ ∘ baseOrder hell
  refine ⟨p, σ.injective.comp (baseOrder_injective hell), ?_⟩
  intro i
  by_cases hi : i.val = 0
  · left
    change Sym2.map σ s(baseOrder hell (Fin.castSucc i),
      baseOrder hell (Fin.succ i)) = chord hell
    rw [base_step_chord hell i hi]
    exact hchord
  · right
    refine ⟨partPerm_old α β δ _ _ (base_step_old hell i hi), ?_⟩
    intro heq
    have h := congrArg (Sym2.map σ.symm) heq
    have hbase : s(baseOrder hell (Fin.castSucc i), baseOrder hell (Fin.succ i)) =
        s(σ.symm x, σ.symm y) := by
      simpa only [Sym2.map_mk, p, Function.comp_apply,
        Equiv.symm_apply_apply] using h
    exact base_step_ne_of_positions hell (σ.symm x) (σ.symm y) hpos i hbase

theorem avoid_aa {ell : ℕ} (hell : 2 ≤ ell)
    (a a' : Fin (ell - 1)) :
    ∃ p : Fin (2 * ell + 2) → MotifVertex ell,
      Function.Injective p ∧ AvoidsPair hell p (aVertex a) (aVertex a') := by
  apply build_avoiding_pair hell _ _ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  · rfl
  · exact positions_not_aa hell a a'

theorem avoid_ac {ell : ℕ} (hell : 2 ≤ ell)
    (a : Fin (ell - 1)) (c : Fin 3) :
    ∃ p : Fin (2 * ell + 2) → MotifVertex ell,
      Function.Injective p ∧ AvoidsPair hell p (aVertex a) (cVertex c) := by
  apply build_avoiding_pair hell _ _ (Equiv.refl _) (Equiv.swap c 1) (Equiv.refl _)
  · rfl
  · change ¬ ((basePosition hell (aVertex a)).val + 1 =
        (basePosition hell (cVertex (Equiv.swap c 1 c))).val ∨
      (basePosition hell (cVertex (Equiv.swap c 1 c))).val + 1 =
        (basePosition hell (aVertex a)).val)
    rw [Equiv.swap_apply_left]
    exact positions_not_ac_middle hell a

theorem avoid_cc {ell : ℕ} (hell : 2 ≤ ell)
    (c c' : Fin 3) (hne : c ≠ c') :
    ∃ p : Fin (2 * ell + 2) → MotifVertex ell,
      Function.Injective p ∧ AvoidsPair hell p (cVertex c) (cVertex c') := by
  have hswap (x y : Fin 3) : (Equiv.swap x y).symm = Equiv.swap x y := rfl
  have hex : ∃ β : Equiv.Perm (Fin 3),
      ¬ ((basePosition hell (cVertex (β.symm c))).val + 1 =
          (basePosition hell (cVertex (β.symm c'))).val ∨
        (basePosition hell (cVertex (β.symm c'))).val + 1 =
          (basePosition hell (cVertex (β.symm c))).val) := by
    fin_cases c <;> fin_cases c'
    · exact False.elim (hne rfl)
    · refine ⟨Equiv.swap (1 : Fin 3) 2, ?_⟩
      norm_num [basePosition, cVertex, hswap, Equiv.swap_apply_def]
    · refine ⟨Equiv.refl _, ?_⟩
      norm_num [basePosition, cVertex]
    · refine ⟨Equiv.swap (1 : Fin 3) 2, ?_⟩
      norm_num [basePosition, cVertex, hswap, Equiv.swap_apply_def]
    · exact False.elim (hne rfl)
    · refine ⟨Equiv.swap (0 : Fin 3) 1, ?_⟩
      norm_num [basePosition, cVertex, hswap, Equiv.swap_apply_def]
    · refine ⟨Equiv.refl _, ?_⟩
      norm_num [basePosition, cVertex]
    · refine ⟨Equiv.swap (0 : Fin 3) 1, ?_⟩
      norm_num [basePosition, cVertex, hswap, Equiv.swap_apply_def]
    · exact False.elim (hne rfl)
  obtain ⟨β, hβ⟩ := hex
  apply build_avoiding_pair hell _ _ (Equiv.refl _) β (Equiv.refl _)
  · rfl
  · exact hβ

theorem avoid_ab {ell : ℕ} (hell : 2 ≤ ell)
    (a : Fin (ell - 1)) (b : Fin ell) :
    ∃ p : Fin (2 * ell + 2) → MotifVertex ell,
      Function.Injective p ∧ AvoidsPair hell p (aVertex a) (bVertex b) := by
  by_cases hb0 : b = bZero hell
  · subst b
    apply build_avoiding_pair hell _ _ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    · rfl
    · exact positions_not_ab_first hell a
  by_cases hb1 : b = bOne hell
  · subst b
    apply build_avoiding_pair hell _ _ (Equiv.refl _) (Equiv.refl _)
      (Equiv.swap (bOne hell) (bZero hell))
    · change s(bVertex (Equiv.swap (bOne hell) (bZero hell) (bZero hell)),
        bVertex (Equiv.swap (bOne hell) (bZero hell) (bOne hell))) = chord hell
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      simp only [chord, Sym2.eq_swap]
    · change ¬ ((basePosition hell (aVertex a)).val + 1 =
          (basePosition hell
            (bVertex (Equiv.swap (bOne hell) (bZero hell) (bOne hell)))).val ∨
        (basePosition hell
            (bVertex (Equiv.swap (bOne hell) (bZero hell) (bOne hell)))).val + 1 =
          (basePosition hell (aVertex a)).val)
      rw [Equiv.swap_apply_left]
      exact positions_not_ab_first hell a
  · have hb0v : b.val ≠ 0 := by
      intro h
      apply hb0
      exact Fin.ext h
    have hb1v : b.val ≠ 1 := by
      intro h
      apply hb1
      exact Fin.ext h
    have hell3 : 3 ≤ ell := by have hb := b.isLt; omega
    let lastB : Fin ell := ⟨ell - 1, by omega⟩
    have hzlast : bZero hell ≠ lastB := by
      intro h
      have hval := congrArg Fin.val h
      simp [bZero, lastB] at hval
      omega
    have holast : bOne hell ≠ lastB := by
      intro h
      have hval := congrArg Fin.val h
      simp [bOne, lastB] at hval
      omega
    apply build_avoiding_pair hell _ _ (Equiv.swap a (aZero hell)) (Equiv.refl _)
      (Equiv.swap b lastB)
    · change s(bVertex (Equiv.swap b lastB (bZero hell)),
        bVertex (Equiv.swap b lastB (bOne hell))) = chord hell
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hb0) hzlast,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hb1) holast]
      rfl
    · have hpos : ¬ ((basePosition hell (aVertex (aZero hell))).val + 1 =
          (basePosition hell (bVertex lastB)).val ∨
        (basePosition hell (bVertex lastB)).val + 1 =
          (basePosition hell (aVertex (aZero hell))).val) := by
        have hb := b.isLt
        simp only [basePosition, aVertex, bVertex, aZero, lastB]
        split_ifs <;> simp_all only <;> omega
      change ¬ ((basePosition hell
          (aVertex (Equiv.swap a (aZero hell) a))).val + 1 =
            (basePosition hell (bVertex (Equiv.swap b lastB b))).val ∨
        (basePosition hell (bVertex (Equiv.swap b lastB b))).val + 1 =
          (basePosition hell (aVertex (Equiv.swap a (aZero hell) a))).val)
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
      exact hpos

/-- Every single old owner edge is avoided while the same named chord is used.
The order, injectivity, consecutive old-edge membership and avoidance are derived. -/
theorem saturated_even_h_avoid_edge {ell : ℕ} (hell : 2 ≤ ell)
    (owner : (motifGraph ell).edgeSet) :
    ∃ p : Fin (2 * ell + 2) → MotifVertex ell,
      Function.Injective p ∧
      ∀ i : Fin (2 * ell + 1),
        s(p (Fin.castSucc i), p (Fin.succ i)) = chord hell ∨
          ((motifGraph ell).Adj (p (Fin.castSucc i)) (p (Fin.succ i)) ∧
            s(p (Fin.castSucc i), p (Fin.succ i)) ≠ owner.val) := by
  obtain ⟨e, he⟩ := owner
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : (motifGraph ell).Adj x y := (SimpleGraph.mem_edgeSet _).mp he
    rcases x with a | (c | b) <;> rcases y with a' | (c' | b')
    · exact avoid_aa hell a a'
    · exact avoid_ac hell a c'
    · exact avoid_ab hell a b'
    · obtain ⟨p, hp, havoid⟩ := avoid_ac hell a' c
      exact ⟨p, hp, avoidingPair_symm hell p _ _ havoid⟩
    · apply avoid_cc hell c c'
      intro h
      exact hxy.1 (congrArg cVertex h)
    · simp [motifGraph, isA, isC] at hxy
    · obtain ⟨p, hp, havoid⟩ := avoid_ab hell a' b
      exact ⟨p, hp, avoidingPair_symm hell p _ _ havoid⟩
    · simp [motifGraph, isA, isC] at hxy
    · simp [motifGraph, isA, isC] at hxy

end ErdosProblems.SaturatedEvenH

namespace ErdosProblems.EvenExceptionExchange

/-- Keep the distinguished new B edge in positions zero/one and retain any
specified actual owner endpoint. A third distinct endpoint is at position two.
All sizes and endpoint coincidences are included. -/
theorem exists_b_embedding_with_owner
    (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (u v w : Fin b) (huv : u ≠ v) :
    ∃ f : Fin (a + 1) ↪ Fin b,
      f ⟨0, by omega⟩ = u ∧ f ⟨1, by omega⟩ = v ∧
      w ∈ Set.range f ∧
      (w ≠ u → w ≠ v → f ⟨2, by omega⟩ = w) := by
  classical
  let x0 : Fin b := ⟨0, by omega⟩
  let x1 : Fin b := ⟨1, by omega⟩
  let x2 : Fin b := ⟨2, by omega⟩
  have h01 : x0 ≠ x1 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x0, x1] at hv
    omega
  have h02 : x0 ≠ x2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x0, x2] at hv
    omega
  have h12 : x1 ≠ x2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x1, x2] at hv
    omega
  let σ : Equiv.Perm (Fin b) := Equiv.swap x0 u
  have hσ0 : σ x0 = u := Equiv.swap_apply_left x0 u
  let z : Fin b := σ.symm v
  have hz0 : z ≠ x0 := by
    intro h
    apply huv
    calc
      u = σ x0 := hσ0.symm
      _ = σ z := congrArg σ h.symm
      _ = v := σ.apply_symm_apply v
  let τ : Equiv.Perm (Fin b) := Equiv.swap x1 z
  have hτ0 : τ x0 = x0 :=
    Equiv.swap_apply_of_ne_of_ne h01 hz0.symm
  have hτ1 : τ x1 = z := Equiv.swap_apply_left x1 z
  let π : Equiv.Perm (Fin b) := τ.trans σ
  have hπ0 : π x0 = u := by
    change σ (τ x0) = u
    rw [hτ0]
    exact hσ0
  have hπ1 : π x1 = v := by
    change σ (τ x1) = v
    rw [hτ1]
    exact σ.apply_symm_apply v
  let e : Fin (a + 1) ↪ Fin b := (Fin.castLEEmb hab).trans π.toEmbedding
  have he0 : e ⟨0, by omega⟩ = u := by
    change π x0 = u
    exact hπ0
  have he1 : e ⟨1, by omega⟩ = v := by
    change π x1 = v
    exact hπ1
  by_cases hwu : w = u
  · refine ⟨e, he0, he1, ?_, ?_⟩
    · exact ⟨⟨0, by omega⟩, he0.trans hwu.symm⟩
    · intro hne _
      exact (hne hwu).elim
  by_cases hwv : w = v
  · refine ⟨e, he0, he1, ?_, ?_⟩
    · exact ⟨⟨1, by omega⟩, he1.trans hwv.symm⟩
    · intro _ hne
      exact (hne hwv).elim
  let t : Fin b := π.symm w
  have ht0 : x0 ≠ t := by
    intro h
    apply hwu
    calc
      w = π t := (π.apply_symm_apply w).symm
      _ = π x0 := congrArg π h.symm
      _ = u := hπ0
  have ht1 : x1 ≠ t := by
    intro h
    apply hwv
    calc
      w = π t := (π.apply_symm_apply w).symm
      _ = π x1 := congrArg π h.symm
      _ = v := hπ1
  let γ : Equiv.Perm (Fin b) := Equiv.swap x2 t
  have hγ0 : γ x0 = x0 := Equiv.swap_apply_of_ne_of_ne h02 ht0
  have hγ1 : γ x1 = x1 := Equiv.swap_apply_of_ne_of_ne h12 ht1
  have hγ2 : γ x2 = t := Equiv.swap_apply_left x2 t
  let f : Fin (a + 1) ↪ Fin b :=
    (Fin.castLEEmb hab).trans (γ.trans π).toEmbedding
  have hf0 : f ⟨0, by omega⟩ = u := by
    change π (γ x0) = u
    rw [hγ0]
    exact hπ0
  have hf1 : f ⟨1, by omega⟩ = v := by
    change π (γ x1) = v
    rw [hγ1]
    exact hπ1
  have hf2 : f ⟨2, by omega⟩ = w := by
    change π (γ x2) = w
    rw [hγ2]
    exact π.apply_symm_apply w
  exact ⟨f, hf0, hf1, ⟨⟨2, by omega⟩, hf2⟩, fun _ _ => hf2⟩

end ErdosProblems.EvenExceptionExchange

namespace ErdosProblems.EvenExceptionExchange
open SimpleGraph

def aPlacement (a : ℕ) : Fin (a + 1 - 1) ↪ Fin a where
  toFun i := ⟨i.val, by
    have hpred : a + 1 - 1 = a := by omega
    simpa only [hpred] using i.isLt⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg Fin.val h

def motifPlacement {a b : ℕ} (f : Fin (a + 1) ↪ Fin b) :
    ErdosProblems.SaturatedEvenH.MotifVertex (a + 1) ↪ Vertex a b :=
  Function.Embedding.sumMap (aPlacement a)
    (Function.Embedding.sumMap (Function.Embedding.refl (Fin 3)) f)

theorem placement_adj_iff {a b : ℕ} (f : Fin (a + 1) ↪ Fin b)
    (x y : ErdosProblems.SaturatedEvenH.MotifVertex (a + 1)) :
    (familyGraph a b).Adj (motifPlacement f x) (motifPlacement f y) ↔
      (ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).Adj x y := by
  constructor
  · intro h
    refine ⟨fun heq => h.1 (congrArg (motifPlacement f) heq), ?_⟩
    rcases x with ax | (cx | bx) <;> rcases y with ay | (cy | by')
    all_goals exact h.2
  · intro h
    refine ⟨(motifPlacement f).injective.ne h.1, ?_⟩
    rcases x with ax | (cx | bx) <;> rcases y with ay | (cy | by')
    all_goals exact h.2

theorem placement_preimage {a b : ℕ} (f : Fin (a + 1) ↪ Fin b)
    (x : Vertex a b)
    (hB : ∀ z : Fin b, x = Sum.inr (Sum.inr z) → z ∈ Set.range f) :
    ∃ x0 : ErdosProblems.SaturatedEvenH.MotifVertex (a + 1),
      motifPlacement f x0 = x := by
  rcases x with i | (c | z)
  · let j : Fin (a + 1 - 1) := ⟨i.val, by
      have hpred : a + 1 - 1 = a := by omega
      simpa only [hpred] using i.isLt⟩
    refine ⟨Sum.inl j, ?_⟩
    change Sum.inl (aPlacement a j) = Sum.inl i
    apply congrArg Sum.inl
    apply Fin.ext
    rfl
  · exact ⟨Sum.inr (Sum.inl c), rfl⟩
  · obtain ⟨j,hj⟩ := hB z rfl
    refine ⟨Sum.inr (Sum.inr j), ?_⟩
    change Sum.inr (Sum.inr (f j)) = Sum.inr (Sum.inr z)
    rw [hj]

/-- On the actual full exceptional family, any one actual old owner can be
deleted and any prescribed distinct B pair inserted, yielding ordinary P_(2a+4).
The owner is pulled back through an injective placement, never assumed favorable. -/
noncomputable def path_copy_after_actual_owner_exchange
    (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (owner : (familyGraph a b).edgeSet) (u v : Fin b) (huv : u ≠ v) :
    (pathGraph (2 * a + 4)).Copy
      ((familyGraph a b).deleteEdges {owner.val} ⊔
        SimpleGraph.fromEdgeSet
          {s((Sum.inr (Sum.inr u) : Vertex a b), Sum.inr (Sum.inr v))}) := by
  classical
  apply Classical.choice
  obtain ⟨e,he⟩ := owner
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : (familyGraph a b).Adj x y := (SimpleGraph.mem_edgeSet _).mp he
    let w : Fin b := match x, y with
      | Sum.inr (Sum.inr z), _ => z
      | _, Sum.inr (Sum.inr z) => z
      | _, _ => u
    obtain ⟨f,hf0,hf1,hw,_⟩ :=
      exists_b_embedding_with_owner a b ha hab u v w huv
    have hxB : ∀ z : Fin b, x = Sum.inr (Sum.inr z) → z ∈ Set.range f := by
      intro z hz
      subst x
      simpa only [w] using hw
    have hyB : ∀ z : Fin b, y = Sum.inr (Sum.inr z) → z ∈ Set.range f := by
      intro z hz
      subst y
      rcases x with ax | (cx | bx)
      · simpa only [w] using hw
      · simpa only [w] using hw
      · rcases hxy.2 with hA | hA | ⟨hC,hC'⟩
        · cases hA
        · cases hA
        · cases hC
    obtain ⟨x0,hx0⟩ := placement_preimage f x hxB
    obtain ⟨y0,hy0⟩ := placement_preimage f y hyB
    have h0 : (ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).Adj x0 y0 := by
      apply (placement_adj_iff f x0 y0).mp
      rw [hx0,hy0]
      exact hxy
    let owner0 : (ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).edgeSet :=
      ⟨s(x0,y0), (SimpleGraph.mem_edgeSet _).mpr h0⟩
    have howner : Sym2.map (motifPlacement f) owner0.val = s(x,y) := by
      change s(motifPlacement f x0, motifPlacement f y0) = s(x,y)
      rw [hx0,hy0]
    let hell : 2 ≤ a + 1 := by omega
    have horder : ∃ p : Fin (2 * a + 4) →
          ErdosProblems.SaturatedEvenH.MotifVertex (a + 1),
        Function.Injective p ∧
        ∀ i : Fin (2 * a + 3),
          s(p (Fin.castSucc i),p (Fin.succ i)) =
            ErdosProblems.SaturatedEvenH.chord hell ∨
          ((ErdosProblems.SaturatedEvenH.motifGraph (a + 1)).Adj
            (p (Fin.castSucc i)) (p (Fin.succ i)) ∧
            s(p (Fin.castSucc i),p (Fin.succ i)) ≠ owner0.val) := by
      have hraw := ErdosProblems.SaturatedEvenH.saturated_even_h_avoid_edge hell owner0
      have hmul : 2 * (a + 1) = 2 * a + 2 := by omega
      rw [hmul] at hraw
      exact hraw
    obtain ⟨p,hp,havoid⟩ := horder
    let q : Fin (2 * a + 4) → Vertex a b := motifPlacement f ∘ p
    have hq : Function.Injective q := (motifPlacement f).injective.comp hp
    have hchord : Sym2.map (motifPlacement f)
        (ErdosProblems.SaturatedEvenH.chord hell) =
          s((Sum.inr (Sum.inr u) : Vertex a b), Sum.inr (Sum.inr v)) := by
      change s((Sum.inr (Sum.inr (f (ErdosProblems.SaturatedEvenH.bZero hell))) :
          Vertex a b),
        Sum.inr (Sum.inr (f (ErdosProblems.SaturatedEvenH.bOne hell)))) =
          s(Sum.inr (Sum.inr u),Sum.inr (Sum.inr v))
      have hf0' : f (ErdosProblems.SaturatedEvenH.bZero hell) = u := hf0
      have hf1' : f (ErdosProblems.SaturatedEvenH.bOne hell) = v := hf1
      rw [hf0',hf1']
    have hqavoid : ∀ i : Fin (2 * a + 3),
        s(q (Fin.castSucc i),q (Fin.succ i)) =
          s((Sum.inr (Sum.inr u) : Vertex a b), Sum.inr (Sum.inr v)) ∨
        ((familyGraph a b).Adj (q (Fin.castSucc i)) (q (Fin.succ i)) ∧
          s(q (Fin.castSucc i),q (Fin.succ i)) ≠ s(x,y)) := by
      intro i
      rcases havoid i with hnew | ⟨hold,hne⟩
      · left
        change Sym2.map (motifPlacement f)
          s(p (Fin.castSucc i),p (Fin.succ i)) =
            s(Sum.inr (Sum.inr u),Sum.inr (Sum.inr v))
        rw [hnew]
        exact hchord
      · right
        refine ⟨(placement_adj_iff f _ _).mpr hold, ?_⟩
        intro heq
        apply hne
        apply Sym2.map.injective (motifPlacement f).injective
        change s(q (Fin.castSucc i),q (Fin.succ i)) =
          Sym2.map (motifPlacement f) owner0.val
        rw [howner]
        exact heq
    exact ⟨copy_of_avoiding_order (familyGraph a b) ⟨s(x,y),he⟩
      (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr v)) q hq hqavoid⟩

end ErdosProblems.EvenExceptionExchange

namespace ErdosProblems.EvenExceptionExchange
open SimpleGraph
open ErdosProblems.PathUpperReduction

def bbHostEdge {a b n : ℕ} (phi : Vertex a b ≃ Fin n)
    (u v : Fin b) (huv : u ≠ v) : HostEdge n := by
  let U : Vertex a b := Sum.inr (Sum.inr u)
  let V : Vertex a b := Sum.inr (Sum.inr v)
  have hUV : U ≠ V := by
    intro h
    exact huv (Sum.inr.inj (Sum.inr.inj h))
  refine ⟨s(phi U, phi V), ?_⟩
  apply (SimpleGraph.mem_edgeSet _).mpr
  simpa only [SimpleGraph.top_adj] using phi.injective.ne hUV

/-- An ordinary path in the ACTUAL replacement representative, under a literal
pullback equality for the ACTUAL original selected graph. The removed edge is
exactly the selected edge of the color of the inserted B-B host edge. -/
noncomputable def replacement_path_copy_of_selected_comap_eq_family
    {n q : ℕ} (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (phi : Vertex a b ≃ Fin n)
    (hselected : (selectedGraph chi r).comap phi = familyGraph a b)
    (u v : Fin b) (huv : u ≠ v) :
    (pathGraph (2 * a + 4)).Copy
      (selectedGraph chi (r.replace (bbHostEdge phi u v huv))) := by
  classical
  let chordEdge : HostEdge n := bbHostEdge phi u v huv
  let U : Vertex a b := Sum.inr (Sum.inr u)
  let V : Vertex a b := Sum.inr (Sum.inr v)
  let old : HostEdge n := r.edge (chi chordEdge)
  have holdmem : old.val ∈ (selectedGraph chi r).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨chi chordEdge, rfl⟩
  let oldSelected : (selectedGraph chi r).edgeSet := ⟨old.val, holdmem⟩
  let back : (selectedGraph chi r).Copy (familyGraph a b) := by
    refine ⟨⟨phi.symm, ?_⟩, phi.symm.injective⟩
    intro x y hxy
    rw [← hselected]
    change (selectedGraph chi r).Adj (phi (phi.symm x)) (phi (phi.symm y))
    simpa only [Equiv.apply_symm_apply] using hxy
  let owner : (familyGraph a b).edgeSet := back.mapEdgeSet oldSelected
  have howner : owner.val = Sym2.map phi.symm old.val := rfl
  let T : SimpleGraph (Vertex a b) :=
    (familyGraph a b).deleteEdges {owner.val} ⊔
      SimpleGraph.fromEdgeSet {s(U,V)}
  let forward : T.Copy (selectedGraph chi (r.replace chordEdge)) := by
    refine ⟨⟨phi, ?_⟩, phi.injective⟩
    intro x y hxy
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hxy with hretain | hnew
    · have hdelete := SimpleGraph.deleteEdges_adj.mp hretain
      have hfamily : (familyGraph a b).Adj x y := hdelete.1
      have hselectedXY : (selectedGraph chi r).Adj (phi x) (phi y) := by
        change ((selectedGraph chi r).comap phi).Adj x y
        rw [hselected]
        exact hfamily
      have hownerNe : s(x,y) ≠ owner.val := by
        simpa only [Set.mem_singleton_iff] using hdelete.2
      have holdNe : s(phi x,phi y) ≠ old.val := by
        intro heq
        apply hownerNe
        have hpull := congrArg (Sym2.map phi.symm) heq
        rw [howner]
        change s(phi.symm (phi x),phi.symm (phi y)) =
          Sym2.map phi.symm old.val at hpull
        simpa only [Equiv.symm_apply_apply] using hpull
      apply delete_selectedEdge_le_replace chi r chordEdge
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨hselectedXY, by simpa only [Set.mem_singleton_iff] using holdNe⟩
    · have hchord : s(x,y) = s(U,V) := by
        simpa only [Set.mem_singleton_iff] using
          ((SimpleGraph.fromEdgeSet_adj {s(U,V)}).mp hnew).1
      have hmap : s(phi x,phi y) = chordEdge.val := by
        change Sym2.map phi s(x,y) = Sym2.map phi s(U,V)
        exact congrArg (Sym2.map phi) hchord
      have hmem := replacedEdge_mem chi r chordEdge
      apply (SimpleGraph.mem_edgeSet _).mp
      rw [hmap]
      exact hmem
  let familyCopy := path_copy_after_actual_owner_exchange a b ha hab owner u v huv
  exact forward.comp familyCopy

/-- The same exact-family replacement gives a rainbow path for the ORIGINAL
complete-host coloring chi. No favorable owner or replacement coloring is used. -/
theorem exists_original_rainbow_path_of_selected_comap_eq_family
    {n q : ℕ} (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (phi : Vertex a b ≃ Fin n)
    (hselected : (selectedGraph chi r).comap phi = familyGraph a b)
    (u v : Fin b) (huv : u ≠ v) :
    ∃ f : (pathGraph (2 * a + 4)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom chi := by
  classical
  let e : HostEdge n := bbHostEdge phi u v huv
  let f := replacement_path_copy_of_selected_comap_eq_family
    a b ha hab chi r phi hselected u v huv
  exact ⟨(Copy.ofLE (selectedGraph chi (r.replace e))
    (⊤ : SimpleGraph (Fin n)) le_top).comp f,
    copy_in_selectedGraph_isRainbow chi (r.replace e) f⟩

end ErdosProblems.EvenExceptionExchange

namespace ErdosProblems.PathUpperReduction.EvenIntermediateCoreScalar1105

open ErdosProblems.PathUpperReduction.CoreEndpointBound1105

/-- The a=3 endpoint uses the ORIGINAL threshold, including its d=4 boundary. -/
theorem even_cone_three_le_original_threshold (d n : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) :
    extremalCount (n + 1) (2 * d + 3) 3 ≤
      n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  have hKN : 2 * d + 3 ≤ n + 1 := by omega
  have hpoly := extremalCount_cast (n + 1) (2 * d + 3) 3 (by omega) hKN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hpoly
  have hdq : (4 : ℚ) ≤ (d : ℚ) := Nat.cast_le.mpr hd
  let A : ℕ := (2 * d).choose 2 + 1
  let B : ℕ := (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2
  have hA : 2 * (A : ℚ) = 4 * (d : ℚ) ^ 2 - 2 * (d : ℚ) + 2 := by
    simp only [A, Nat.cast_add, Nat.cast_one, Nat.cast_choose_two,
      Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hB : 2 * (B : ℚ) =
      2 * ((d : ℚ) - 1) * (n : ℚ) - (d : ℚ) * ((d : ℚ) - 1) + 4 := by
    simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
      Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : d ≤ n),
      Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases hsmall : n ≤ 3 * d - 1
  · have hnq : (n : ℚ) ≤ 3 * (d : ℚ) - 1 := by
      have h : (n : ℚ) ≤ ((3 * d - 1 : ℕ) : ℚ) := Nat.cast_le.mpr hsmall
      simpa only [Nat.cast_sub (by omega : 1 ≤ 3 * d), Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one] using h
    have hq : (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ ((n + A : ℕ) : ℚ) := by
      rw [Nat.cast_add]
      nlinarith [hpoly, hA]
    have hNat : extremalCount (n + 1) (2 * d + 3) 3 ≤ n + A := Nat.cast_le.mp hq
    exact hNat.trans (Nat.add_le_add_left (le_max_left A B) n)
  · have hlarge : 3 * d ≤ n := by omega
    have hnq : 3 * (d : ℚ) ≤ (n : ℚ) := by
      have h : ((3 * d : ℕ) : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hlarge
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    have hp₁ : 0 ≤ ((d : ℚ) - 3) * ((n : ℚ) - 3 * (d : ℚ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hp₂ : 0 ≤ ((d : ℚ) - 4) * ((d : ℚ) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hq : (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ ((n + B : ℕ) : ℚ) := by
      rw [Nat.cast_add]
      nlinarith [hpoly, hB, hp₁, hp₂]
    have hNat : extremalCount (n + 1) (2 * d + 3) 3 ≤ n + B := Nat.cast_le.mp hq
    exact hNat.trans (Nat.add_le_add_left (le_max_right A B) n)

/-- Convex interpolation on the exact sharpened interval 3≤a≤d−1.
The collapsed d=4 interval is handled before positive-factor cancellation. -/
theorem even_cone_intermediate_le_original_threshold (d n a : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) (ha : 3 ≤ a) (had : a ≤ d - 1) :
    extremalCount (n + 1) (2 * d + 3) a ≤
      n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  let t : ℕ := d - 1
  let M : ℕ := n + max ((2 * d).choose 2 + 1)
    ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2)
  have hat : a ≤ t := had
  have h3M : extremalCount (n + 1) (2 * d + 3) 3 ≤ M :=
    even_cone_three_le_original_threshold d n hd hn
  by_cases haeq : a = 3
  · subst a
    exact h3M
  have ht3 : 3 < t := by dsimp [t] at hat ⊢; omega
  have hd5 : 5 ≤ d := by dsimp [t] at ht3; omega
  have htK : t ≤ 2 * d + 3 := by dsimp [t]; omega
  have haK : a ≤ 2 * d + 3 := hat.trans htK
  have hKN : 2 * d + 3 ≤ n + 1 := by omega
  have hpoly₃ := extremalCount_cast (n + 1) (2 * d + 3) 3 (by omega) hKN
  have hpoly_t := extremalCount_cast (n + 1) (2 * d + 3) t htK hKN
  have hpoly_a := extremalCount_cast (n + 1) (2 * d + 3) a haK hKN
  have htM : extremalCount (n + 1) (2 * d + 3) t ≤ M := by
    let B : ℕ := (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2
    have htcast : (t : ℚ) = (d : ℚ) - 1 := by
      dsimp [t]
      exact Nat.cast_sub (by omega : 1 ≤ d)
    have hpoly := hpoly_t
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, htcast] at hpoly
    have hB : 2 * (B : ℚ) =
        2 * ((d : ℚ) - 1) * (n : ℚ) - (d : ℚ) * ((d : ℚ) - 1) + 4 := by
      simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
        Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : d ≤ n),
        Nat.cast_one, Nat.cast_ofNat]
      ring
    have hnlarge : d + 7 ≤ n := by omega
    have hnq : (d : ℚ) + 7 ≤ (n : ℚ) := by
      have h : ((d + 7 : ℕ) : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hnlarge
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    have hq : (extremalCount (n + 1) (2 * d + 3) t : ℚ) ≤ ((n + B : ℕ) : ℚ) := by
      rw [Nat.cast_add]
      nlinarith [hpoly, hB]
    have hNat : extremalCount (n + 1) (2 * d + 3) t ≤ n + B := Nat.cast_le.mp hq
    exact hNat.trans (Nat.add_le_add_left (le_max_right _ B) n)
  have haq : (3 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have htaq : (a : ℚ) ≤ (t : ℚ) := Nat.cast_le.mpr hat
  have htq : (3 : ℚ) < (t : ℚ) := Nat.cast_lt.mpr ht3
  have hw₁ : 0 ≤ (t : ℚ) - (a : ℚ) := sub_nonneg.mpr htaq
  have hw₂ : 0 ≤ (a : ℚ) - 3 := sub_nonneg.mpr haq
  have hw : 0 < (t : ℚ) - 3 := sub_pos.mpr htq
  have hchord :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ)) +
          ((a : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ)) -
          ((t : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) a : ℚ)) =
        3 * ((t : ℚ) - 3) * ((a : ℚ) - 3) * ((t : ℚ) - (a : ℚ)) := by
    rw [hpoly₃, hpoly_t, hpoly_a]
    ring
  have hproduct :
      0 ≤ 3 * ((t : ℚ) - 3) * ((a : ℚ) - 3) * ((t : ℚ) - (a : ℚ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hw)) hw₂) hw₁
  have hinterp :
      ((t : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) a : ℚ)) ≤
        ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ)) +
          ((a : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ)) := by
    linarith [hchord, hproduct]
  have h3Mq : (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ (M : ℚ) := Nat.cast_le.mpr h3M
  have htMq : (extremalCount (n + 1) (2 * d + 3) t : ℚ) ≤ (M : ℚ) := Nat.cast_le.mpr htM
  have h3M' : 2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have htM' : 2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have hweighted :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount (n + 1) (2 * d + 3) 3 : ℚ)) +
          ((a : ℚ) - 3) * (2 * (extremalCount (n + 1) (2 * d + 3) t : ℚ)) ≤
        ((t : ℚ) - 3) * (2 * (M : ℚ)) := by
    calc
      _ ≤ ((t : ℚ) - (a : ℚ)) * (2 * (M : ℚ)) +
          ((a : ℚ) - 3) * (2 * (M : ℚ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h3M' hw₁)
          (mul_le_mul_of_nonneg_left htM' hw₂)
      _ = _ := by ring
  have htwice : 2 * (extremalCount (n + 1) (2 * d + 3) a : ℚ) ≤ 2 * (M : ℚ) :=
    le_of_mul_le_mul_left (hinterp.trans hweighted) hw
  have hq : (extremalCount (n + 1) (2 * d + 3) a : ℚ) ≤ (M : ℚ) := by linarith
  exact Nat.cast_le.mp hq

/-- Exact intermediate core count at the original even palette threshold. -/
theorem intermediate_core_count_le_original_even_threshold (d n r : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n)
    (hrLower : d + 4 ≤ r) (hrUpper : r ≤ 2 * d) :
    r.choose 2 + (2 * d + 3 - r) * (n + 1 - r) ≤
      n + max ((2 * d).choose 2 + 1)
        ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) := by
  let a : ℕ := 2 * d + 3 - r
  have ha : 3 ≤ a := by dsimp [a]; omega
  have had : a ≤ d - 1 := by dsimp [a]; omega
  have hKa : 2 * d + 3 - a = r := by dsimp [a]; omega
  have hNKa : n + 1 - (2 * d + 3) + a = n + 1 - r := by dsimp [a]; omega
  have h := even_cone_intermediate_le_original_threshold d n a hd hn ha had
  change (2 * d + 3 - a).choose 2 + a * (n + 1 - (2 * d + 3) + a) ≤ _ at h
  rw [hKa, hNKa] at h
  exact h

end ErdosProblems.PathUpperReduction.EvenIntermediateCoreScalar1105

namespace ErdosProblems.PathUpperReduction.UniformCone1105

open SimpleGraph

/-- Add one apex, with every old-old adjacency exactly unchanged. -/
def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a
    · exact id
    · exact G.loopless.irrefl _⟩

/-- The positive, nonwrapping offsets after an apex position. -/
def apexOffset {k m : ℕ} (hkm : k < m) (i : Fin k) : Fin m :=
  ⟨i.val + 1, by omega⟩

/-- The literal first k source vertices of a cycle with at least k vertices. -/
def prefixOffset {k m : ℕ} (hkm : k ≤ m) (i : Fin k) : Fin m :=
  ⟨i.val, by omega⟩

/-- Extract old vertices at actual injective cycle positions. This helper's
positions are constructed in the two following theorems. -/
theorem pathCopy_of_cycle_positions {V : Type*} (G : SimpleGraph V)
    {k m : ℕ} (f : (cycleGraph m).Copy (cone G))
    (q : Fin k → Fin m) (hq : Function.Injective q)
    (hstep : ∀ {a b : Fin k}, a.val + 1 = b.val →
      (cycleGraph m).Adj (q a) (q b))
    (hnotapex : ∀ i, f (q i) ≠ none) :
    ∃ p : (pathGraph k).Copy G, ∀ i, some (p i) = f (q i) := by
  classical
  have hsome (i : Fin k) : ∃ v : V, f (q i) = some v := by
    cases he : f (q i) with
    | none => exact (hnotapex i he).elim
    | some v => exact ⟨v, rfl⟩
  let p : Fin k → V := fun i => Classical.choose (hsome i)
  have hp_eq (i : Fin k) : f (q i) = some (p i) :=
    Classical.choose_spec (hsome i)
  have hp : Function.Injective p := by
    intro a b h
    apply hq
    apply f.injective
    change f (q a) = f (q b)
    rw [hp_eq a, hp_eq b, h]
  have hpstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      G.Adj (p a) (p b) := by
    have hm := f.toHom.map_adj (hstep hab)
    change (cone G).Adj (f (q a)) (f (q b)) at hm
    rw [hp_eq a, hp_eq b] at hm
    exact hm
  let φ : (pathGraph k) →g G := ⟨p, by
    intro a b hab
    rcases pathGraph_adj.mp hab with h | h
    · exact hpstep h
    · exact (hpstep h).symm⟩
  refine ⟨φ.toCopy hp, ?_⟩
  intro i
  exact (hp_eq i).symm

/-- When this actual cycle contains the apex, select its k old vertices
immediately after that apex. The cycle need not span the host. -/
theorem pathCopy_of_cycle_with_apex {V : Type*} (G : SimpleGraph V)
    {k m : ℕ} [NeZero m] (hkm : k < m)
    (f : (cycleGraph m).Copy (cone G)) (j : Fin m) (hj : f j = none) :
    ∃ p : (pathGraph k).Copy G,
      ∀ i, some (p i) = f (j + apexOffset hkm i) := by
  classical
  let d : Fin k → Fin m := apexOffset hkm
  let q : Fin k → Fin m := fun i => j + d i
  have hd : Function.Injective d := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change a.val + 1 = b.val + 1 at hv
    omega
  have hq : Function.Injective q := by
    intro a b h
    apply hd
    exact add_left_cancel h
  have hstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      (cycleGraph m).Adj (q a) (q b) := by
    have hle : d a ≤ d b := by
      change a.val + 1 ≤ b.val + 1
      omega
    have hsub : (d b - d a).val = 1 := by
      rw [Fin.sub_val_of_le hle]
      change (b.val + 1) - (a.val + 1) = 1
      omega
    have hrot : (q b - q a).val = 1 := by
      have heq : q b - q a = d b - d a := by
        dsimp [q]
        abel
      rw [heq]
      exact hsub
    exact cycleGraph_adj'.mpr (Or.inr hrot)
  have hnotapex (i : Fin k) : f (q i) ≠ none := by
    intro hi
    have hqi : q i = j := f.injective (hi.trans hj.symm)
    have hz : d i = (0 : Fin m) := by
      apply add_left_cancel (a := j)
      simpa only [q, add_zero] using hqi
    have hv := congrArg Fin.val hz
    have hbad : i.val + 1 = 0 := by
      simpa only [d, apexOffset, Fin.val_zero] using hv
    omega
  exact pathCopy_of_cycle_positions G f q hq (fun h => hstep h) hnotapex

/-- When this actual cycle avoids the apex, select its first k vertices. -/
theorem pathCopy_of_cycle_without_apex {V : Type*} (G : SimpleGraph V)
    {k m : ℕ} (hkm : k ≤ m) (f : (cycleGraph m).Copy (cone G))
    (hnotapex : ∀ j, f j ≠ none) :
    ∃ p : (pathGraph k).Copy G,
      ∀ i, some (p i) = f (prefixOffset hkm i) := by
  classical
  let q : Fin k → Fin m := prefixOffset hkm
  have hq : Function.Injective q := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) h
  have hstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      (cycleGraph m).Adj (q a) (q b) := by
    have hle : q a ≤ q b := by
      change a.val ≤ b.val
      omega
    have hsub : (q b - q a).val = 1 := by
      rw [Fin.sub_val_of_le hle]
      change b.val - a.val = 1
      omega
    exact cycleGraph_adj'.mpr (Or.inr hsub)
  exact pathCopy_of_cycle_positions G f q hq (fun h => hstep h)
    (fun i => hnotapex (q i))

/-- On any host carrier, ordinary P_k freedom excludes every cycle of
order at least k+1 in the faithful one-apex cone. -/
theorem cone_all_long_cycle_free {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 5 ≤ k) (hfree : (pathGraph k).Free G) :
    ∀ m, k + 1 ≤ m → (cycleGraph m).Free (cone G) := by
  classical
  intro m hm hcopy
  obtain ⟨f⟩ := hcopy
  have hm6 : 6 ≤ m := le_trans (Nat.add_le_add_right hk 1) hm
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 6) hm6
  let : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hkm : k < m := by omega
  by_cases ha : ∃ j, f j = none
  · obtain ⟨j, hj⟩ := ha
    obtain ⟨p, _⟩ := pathCopy_of_cycle_with_apex G hkm f j hj
    exact hfree ⟨p⟩
  · have hnotapex : ∀ j, f j ≠ none := by
      intro j hj
      exact ha ⟨j, hj⟩
    obtain ⟨p, _⟩ := pathCopy_of_cycle_without_apex G (Nat.le_of_lt hkm) f hnotapex
    exact hfree ⟨p⟩

/-- Literal finite-host FC1105 domain; no spanning or apex-range premise. -/
theorem finite_cone_all_long_cycle_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (_hkn : k ≤ n) (hk : 5 ≤ k) (hfree : (pathGraph k).Free G) :
    ∀ m, k + 1 ≤ m → (cycleGraph m).Free (cone G) :=
  cone_all_long_cycle_free G hk hfree

end ErdosProblems.PathUpperReduction.UniformCone1105

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenSelectedFamilyIdentification1105

open SimpleGraph
open ErdosProblems.EvenExceptionExchange

/-- An actual cone classification identifies the SAME original graph with
the existing exceptional family. The apex really belongs to C, and is
removed internally; every original host vertex appears in the bijection. -/
theorem exists_family_pullback_of_actual_cone_classification (n d : ℕ)
    (M : SimpleGraph (Fin n)) (S C : Finset (Option (Fin n)))
    (hd : 2 ≤ d) (hnd : 2 * d + 2 ≤ n)
    (hCS : C ⊆ S) (hScard : S.card = d + 3) (hCcard : C.card = d)
    (hapex : none ∈ C)
    (hclass : ∀ u v, (UniformCone1105.cone M).Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C))) :
    ∃ phi : Vertex (d - 1) (n - d - 2) ≃ Fin n,
      M.comap phi = familyGraph (d - 1) (n - d - 2) := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun v => some v ∈ S)
  let A : Finset (Fin n) := Finset.univ.filter (fun v => some v ∈ C)
  let B : Finset (Fin n) := U \ A
  let D : Finset (Fin n) := Finset.univ \ U
  let f : Fin n ↪ Option (Fin n) := ⟨some, Option.some_injective _⟩
  have hapexS : none ∈ S := hCS hapex
  have hAU : A ⊆ U := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      hCS (Finset.mem_filter.mp hv).2⟩
  have hmapA : A.map f = C.erase none := by
    ext v
    cases v with
    | none => simp [f]
    | some v => simp [A, f]
  have hmapU : U.map f = S.erase none := by
    ext v
    cases v with
    | none => simp [f]
    | some v => simp [U, f]
  have hAcard : A.card = d - 1 := by
    have h := congrArg Finset.card hmapA
    rw [Finset.card_map, Finset.card_erase_of_mem hapex, hCcard] at h
    exact h
  have hUcard : U.card = d + 2 := by
    have h := congrArg Finset.card hmapU
    rw [Finset.card_map, Finset.card_erase_of_mem hapexS, hScard] at h
    omega
  have hBcard : B.card = 3 := by
    have h := Finset.card_sdiff_add_card_eq_card hAU
    change B.card + A.card = U.card at h
    rw [hAcard, hUcard] at h
    omega
  have hDcard : D.card = n - d - 2 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ U)
    change D.card + U.card = (Finset.univ : Finset (Fin n)).card at h
    rw [hUcard, Finset.card_univ, Fintype.card_fin] at h
    have hdn : d + 2 ≤ n :=
      Nat.le_trans (by omega : d + 2 ≤ 2 * d + 2) hnd
    omega
  let eA : Fin (d - 1) ≃ (A : Set (Fin n)) :=
    (Finset.equivFinOfCardEq hAcard).symm
  let eB : Fin 3 ≃ (B : Set (Fin n)) :=
    (Finset.equivFinOfCardEq hBcard).symm
  let eD : Fin (n - d - 2) ≃ (D : Set (Fin n)) :=
    (Finset.equivFinOfCardEq hDcard).symm
  have hAUset : (A : Set (Fin n)) ⊆ (U : Set (Fin n)) := hAU
  let eBD : (B : Set (Fin n)) ≃
      ↥((U : Set (Fin n)) \ (A : Set (Fin n))) :=
    Set.equivOfEq (by ext v; simp [B])
  let eDC : (D : Set (Fin n)) ≃ ↥((U : Set (Fin n))ᶜ) :=
    Set.equivOfEq (by ext v; simp [D])
  let eParts : (A : Set (Fin n)) ⊕
      ((B : Set (Fin n)) ⊕ (D : Set (Fin n))) ≃ Fin n :=
    (Equiv.sumCongr (Equiv.refl _)
      (Equiv.sumCongr eBD eDC)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans
        ((Equiv.sumCongr (Equiv.Set.sumDiffSubset hAUset)
          (Equiv.refl _)).trans (Equiv.Set.sumCompl (U : Set (Fin n)))))
  let phi : Vertex (d - 1) (n - d - 2) ≃ Fin n :=
    (Equiv.sumCongr eA (Equiv.sumCongr eB eD)).trans eParts
  have hphiA (i : Fin (d - 1)) : phi (Sum.inl i) = (eA i).val := rfl
  have hphiB (i : Fin 3) : phi (Sum.inr (Sum.inl i)) = (eB i).val := rfl
  have hphiD (i : Fin (n - d - 2)) :
      phi (Sum.inr (Sum.inr i)) = (eD i).val := rfl
  have hAC (i : Fin (d - 1)) : some (phi (Sum.inl i)) ∈ C := by
    rw [hphiA]
    exact (Finset.mem_filter.mp (eA i).property).2
  have hAS (i : Fin (d - 1)) : some (phi (Sum.inl i)) ∈ S := hCS (hAC i)
  have hBS (i : Fin 3) : some (phi (Sum.inr (Sum.inl i))) ∈ S := by
    rw [hphiB]
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (eB i).property).1).2
  have hBC (i : Fin 3) : some (phi (Sum.inr (Sum.inl i))) ∉ C := by
    rw [hphiB]
    intro hiC
    exact (Finset.mem_sdiff.mp (eB i).property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiC⟩)
  have hDS (i : Fin (n - d - 2)) :
      some (phi (Sum.inr (Sum.inr i))) ∉ S := by
    rw [hphiD]
    intro hiS
    exact (Finset.mem_sdiff.mp (eD i).property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩)
  have hDC (i : Fin (n - d - 2)) :
      some (phi (Sum.inr (Sum.inr i))) ∉ C := fun h => hDS i (hCS h)
  generalize hphi : phi = φ at hAS hAC hBS hBC hDS hDC
  clear hphiA hphiB hphiD hphi eA eB eD eBD eDC eParts phi
  have hM (u v : Fin n) : M.Adj u v ↔ u ≠ v ∧
      ((some u ∈ S ∧ some v ∈ S) ∨
        (some u ∉ S ∧ some v ∈ C) ∨ (some v ∉ S ∧ some u ∈ C)) := by
    have h := hclass (some u) (some v)
    change M.Adj u v ↔ some u ≠ some v ∧
      ((some u ∈ S ∧ some v ∈ S) ∨
        (some u ∉ S ∧ some v ∈ C) ∨ (some v ∉ S ∧ some u ∈ C)) at h
    simpa only [ne_eq, Option.some_inj] using h
  refine ⟨φ, ?_⟩
  ext u v
  change M.Adj (φ u) (φ v) ↔
    (familyGraph (d - 1) (n - d - 2)).Adj u v
  rw [hM]
  have hne : φ u ≠ φ v ↔ u ≠ v := by
    constructor
    · intro h hUV
      exact h (congrArg φ hUV)
    · intro h hUV
      exact h (φ.injective hUV)
  rw [hne]
  rcases u with i | (j | k) <;> rcases v with i' | (j' | k')
  · change _ ↔ (_ ∧ (True ∨ True ∨ (False ∧ False)))
    have hi := hAS i
    have hi' := hAS i'
    have hc := hAC i
    have hc' := hAC i'
    tauto
  · change _ ↔ (_ ∧ (True ∨ False ∨ (False ∧ True)))
    have hi := hAS i
    have hj := hBS j'
    have hc := hAC i
    have hc' := hBC j'
    tauto
  · change _ ↔ (_ ∧ (True ∨ False ∨ (False ∧ False)))
    have hi := hAS i
    have hk := hDS k'
    have hc := hAC i
    have hc' := hDC k'
    tauto
  · change _ ↔ (_ ∧ (False ∨ True ∨ (True ∧ False)))
    have hj := hBS j
    have hi := hAS i'
    have hc := hBC j
    have hc' := hAC i'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (True ∧ True)))
    have hj := hBS j
    have hj' := hBS j'
    have hc := hBC j
    have hc' := hBC j'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (True ∧ False)))
    have hj := hBS j
    have hk := hDS k'
    have hc := hBC j
    have hc' := hDC k'
    tauto
  · change _ ↔ (_ ∧ (False ∨ True ∨ (False ∧ False)))
    have hk := hDS k
    have hi := hAS i'
    have hc := hDC k
    have hc' := hAC i'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (False ∧ True)))
    have hk := hDS k
    have hj := hBS j'
    have hc := hDC k
    have hc' := hBC j'
    tauto
  · change _ ↔ (_ ∧ (False ∨ False ∨ (False ∧ False)))
    have hk := hDS k
    have hk' := hDS k'
    have hc := hDC k
    have hc' := hDC k'
    tauto

end ErdosProblems.PathUpperReduction.EvenSelectedFamilyIdentification1105
end

section

#guard (let m : ℕ := 4; let l : ℕ := 3; let q : ℕ := 9;
  max (m.choose 2 + 1)
    (((m + 1) / 2 - 1).choose 2 +
      ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
      (if Odd m then 1 else 2)) < q ∧
    q ≤ m.choose 2 + l ∧ ¬ (2 * l ≤ m) ∧ q = 6 + l)

#guard (let m : ℕ := 6; let l : ℕ := 2; let q : ℕ := 17;
  max (m.choose 2 + 1)
    (((m + 1) / 2 - 1).choose 2 +
      ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
      (if Odd m then 1 else 2)) < q ∧
    q ≤ m.choose 2 + l ∧ 2 * l ≤ m)

#guard (let m : ℕ := 6; let l : ℕ := 4;
  ((m + 1) / 2 - 1).choose 2 +
      ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
      (if Odd m then 1 else 2) = 19 ∧ m.choose 2 + l = 19)

namespace ErdosProblems.PathUpperReduction.WindowNumerics1105

theorem odd_capacity_le_threshold (a l : ℕ) (ha : 2 ≤ a) (hl : a + 1 ≤ l) :
    (2 * a + 1).choose 2 + l ≤ a.choose 2 + a * (a + l + 1) + 1 := by
  have haq : (2 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have hlq : (a : ℚ) + 1 ≤ (l : ℚ) := by
    have h : ((a + 1 : ℕ) : ℚ) ≤ (l : ℚ) := Nat.cast_le.mpr hl
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hfactor : 0 ≤ (a : ℚ) - 1 := by linarith
  have hgap : 0 ≤ (l : ℚ) - ((a : ℚ) + 1) := by linarith
  have hmul := mul_nonneg hfactor hgap
  have hsq := mul_nonneg (Nat.cast_nonneg a : (0 : ℚ) ≤ (a : ℚ)) hfactor
  have hidentity :
      2 * (((2 * a + 1).choose 2 + l : ℕ) : ℚ) -
          2 * ((a.choose 2 + a * (a + l + 1) + 1 : ℕ) : ℚ) =
        (a : ℚ) * ((a : ℚ) + 1) - 2 * ((a : ℚ) - 1) * (l : ℚ) - 2 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
      Nat.cast_one, Nat.cast_ofNat]
    ring
  have hcast : (((2 * a + 1).choose 2 + l : ℕ) : ℚ) ≤
      ((a.choose 2 + a * (a + l + 1) + 1 : ℕ) : ℚ) := by
    nlinarith [hidentity, hmul, hsq]
  exact Nat.cast_le.mp hcast

theorem even_capacity_le_threshold (a l : ℕ) (ha : 3 ≤ a) (hl : a + 1 ≤ l) :
    (2 * a).choose 2 + l ≤
      (a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 := by
  have ha1 : 1 ≤ a := by omega
  have haq : (3 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have hlq : (a : ℚ) + 1 ≤ (l : ℚ) := by
    have h : ((a + 1 : ℕ) : ℚ) ≤ (l : ℚ) := Nat.cast_le.mpr hl
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hfactor : 0 ≤ (a : ℚ) - 2 := by linarith
  have hgap : 0 ≤ (l : ℚ) - ((a : ℚ) + 1) := by linarith
  have hmul := mul_nonneg hfactor hgap
  have hsq := mul_nonneg (Nat.cast_nonneg a : (0 : ℚ) ≤ (a : ℚ))
    (show 0 ≤ (a : ℚ) - 3 by linarith)
  have hidentity :
      2 * (((2 * a).choose 2 + l : ℕ) : ℚ) -
          2 * (((a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 : ℕ) : ℚ) =
        (a : ℚ) * ((a : ℚ) + 1) - 2 * ((a : ℚ) - 2) * (l : ℚ) - 4 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
      Nat.cast_sub ha1, Nat.cast_one, Nat.cast_ofNat]
    ring
  have hcast : (((2 * a).choose 2 + l : ℕ) : ℚ) ≤
      (((a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 : ℕ) : ℚ) := by
    nlinarith [hidentity, hmul, hsq]
  exact Nat.cast_le.mp hcast

theorem palette_implies_s1_window (m l q : ℕ) (hm : 5 ≤ m) (_hl : 2 ≤ l)
    (hq : max (m.choose 2 + 1)
      (((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2)) < q)
    (hcapacity : q ≤ m.choose 2 + l) : 2 * l ≤ m := by
  have hBq :
      ((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  by_contra hwindow
  let a : ℕ := m / 2
  have hparity : m = 2 * a + 1 ∨ m = 2 * a := by dsimp [a]; omega
  rcases hparity with hodd | heven
  · have ha : 2 ≤ a := by omega
    have hl : a + 1 ≤ l := by omega
    have hpred : (m + 1) / 2 - 1 = a := by omega
    have hterm : m + l - (m + 1) / 2 + 1 = a + l + 1 := by omega
    have hmOdd : Odd m := Nat.odd_iff.mpr (by omega)
    have hC : m.choose 2 + l ≤ a.choose 2 + a * (a + l + 1) + 1 := by
      rw [hodd]
      exact odd_capacity_le_threshold a l ha hl
    have hB : a.choose 2 + a * (a + l + 1) + 1 < q := by
      simpa only [hpred, hterm, ite_eq_left hmOdd] using hBq
    omega
  · have ha : 3 ≤ a := by omega
    have hl : a + 1 ≤ l := by omega
    have hpred : (m + 1) / 2 - 1 = a - 1 := by omega
    have hterm : m + l - (m + 1) / 2 + 1 = a + l + 1 := by omega
    have hmNotOdd : ¬ Odd m := Nat.not_odd_iff.mpr (by omega)
    have hC : m.choose 2 + l ≤
        (a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 := by
      rw [heven]
      exact even_capacity_le_threshold a l ha hl
    have hB : (a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 < q := by
      simpa only [hpred, hterm, ite_eq_right hmNotOdd] using hBq
    omega

theorem s1_palette_implies_window_or_full_four (m l q : ℕ)
    (hm : 4 ≤ m) (hl : 2 ≤ l)
    (hq : max (m.choose 2 + 1)
      (((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2)) < q)
    (hcapacity : q ≤ m.choose 2 + l) :
    m.choose 2 + 2 ≤ q ∧ (2 * l ≤ m ∨ (m = 4 ∧ q = 6 + l)) := by
  have hAq : m.choose 2 + 1 < q :=
    lt_of_le_of_lt (le_max_left _ _) hq
  refine ⟨by omega, ?_⟩
  by_cases hfour : m = 4
  · right
    refine ⟨hfour, ?_⟩
    have hBq :
        ((m + 1) / 2 - 1).choose 2 +
          ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
          (if Odd m then 1 else 2) < q :=
      lt_of_le_of_lt (le_max_right _ _) hq
    have hpred : (m + 1) / 2 - 1 = 1 := by omega
    have hterm : m + l - (m + 1) / 2 + 1 = l + 3 := by omega
    have hmNotOdd : ¬ Odd m := Nat.not_odd_iff.mpr (by omega)
    have hchoose1 : (1 : ℕ).choose 2 = 0 := by decide
    have hchoose4 : m.choose 2 = 6 := by rw [hfour]; decide
    rw [hpred, hterm, ite_eq_right hmNotOdd, hchoose1, one_mul, zero_add] at hBq
    rw [hchoose4] at hcapacity
    omega
  · left
    exact palette_implies_s1_window m l q (by omega) hl hq hcapacity

theorem original_palette_implies_window_or_full_four (k n q : ℕ)
    (hk : 6 ≤ k) (hkn : k ≤ n)
    (hq : max ((k - 2).choose 2 + 1)
      (((k - 1) / 2 - 1).choose 2 +
        ((k - 1) / 2 - 1) * (n - (k - 1) / 2 + 1) +
        (if Odd k then 1 else 2)) < q)
    (hcapacity : q ≤ (k - 2).choose 2 + (n - k + 2)) :
    (k - 2).choose 2 + 2 ≤ q ∧
      (2 * (n - k + 2) ≤ k - 2 ∨ (k = 6 ∧ q = n + 2)) := by
  let m : ℕ := k - 2
  let l : ℕ := n - k + 2
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hl : 2 ≤ l := by dsimp [l]; omega
  have hkm : k = m + 2 := by dsimp [m]; omega
  have hn : n = m + l := by dsimp [m, l]; omega
  have hell : (k - 1) / 2 = (m + 1) / 2 := by omega
  have hterm : n - (m + 1) / 2 + 1 = m + l - (m + 1) / 2 + 1 := by omega
  have hparity : Odd k ↔ Odd m := by
    simp only [Nat.odd_iff]
    omega
  have hq' : max (m.choose 2 + 1)
      (((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2)) < q := by
    simpa only [hell, hterm, hparity] using hq
  have hcapacity' : q ≤ m.choose 2 + l := hcapacity
  obtain ⟨hmargin, hcases⟩ :=
    s1_palette_implies_window_or_full_four m l q hm hl hq' hcapacity'
  refine ⟨hmargin, ?_⟩
  rcases hcases with hwindow | ⟨hfour, hfull⟩
  · exact Or.inl hwindow
  · right
    constructor <;> omega

end ErdosProblems.PathUpperReduction.WindowNumerics1105

end

noncomputable section
namespace ErdosProblems.PathUpperReduction.UniformConeStructure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)
attribute [local instance] Classical.propDecidable

/-- Deleting the apex recovers the entire original carrier and adjacency. -/
def oldVertexIso {V : Type*} (G : SimpleGraph V) :
    G ≃g (cone G).induce ({(none : Option V)}ᶜ : Set (Option V)) where
  toFun v := ⟨some v, by simp⟩
  invFun x := match x with
    | ⟨some v, _⟩ => v
    | ⟨none, h⟩ => False.elim (by simp at h)
  left_inv v := rfl
  right_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | none => simp at hx
    | some v => rfl
  map_rel_iff' := by
    intro u v
    rfl

theorem cone_apex_isUniversal {V : Type*} (G : SimpleGraph V) :
    (cone G).IsUniversal none := by
  intro w hne
  cases w with
  | none => exact False.elim (hne rfl)
  | some v => trivial

theorem cone_connected {V : Type*} (G : SimpleGraph V) :
    (cone G).Connected :=
  Connected.of_isUniversal (cone_apex_isUniversal G)

/-- Deleting an old vertex preserves the actual universal apex. -/
theorem cone_delete_old_connected {V : Type*} (G : SimpleGraph V) (v : V) :
    ((cone G).induce ({(some v : Option V)}ᶜ : Set (Option V))).Connected := by
  let apex : ({(some v : Option V)}ᶜ : Set (Option V)) := ⟨none, by simp⟩
  apply Connected.of_isUniversal (v := apex)
  intro x hne
  change (cone G).Adj none x.val
  rcases x with ⟨x, hx⟩
  cases x with
  | none => exact False.elim (hne (Subtype.ext rfl))
  | some w => trivial

/-- Apex deletion needs exactly original connectedness, not G-v connectedness. -/
theorem cone_delete_apex_connected {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) :
    ((cone G).induce ({(none : Option V)}ᶜ : Set (Option V))).Connected :=
  (oldVertexIso G).connected_iff.mp hG

theorem cone_all_vertex_deletions_connected {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (z : Option V) :
    ((cone G).induce ({z}ᶜ : Set (Option V))).Connected := by
  cases z with
  | none => exact cone_delete_apex_connected G hG
  | some v => exact cone_delete_old_connected G v

theorem cone_neighborFinset_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cone G).neighborFinset none = Finset.univ.image (some : V → Option V) := by
  ext v
  rw [(cone G).mem_neighborFinset]
  cases v <;> simp [cone]

theorem cone_degree_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cone G).degree none = Fintype.card V := by
  change ((cone G).neighborFinset none).card = _
  rw [cone_neighborFinset_none,
    Finset.card_image_of_injective _ (Option.some_injective V)]
  exact Finset.card_univ

/-- Count actual unordered edges and guard the natural subtraction. -/
theorem cone_edgeFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cone G).edgeFinset.card = G.edgeFinset.card + Fintype.card V := by
  let attached := cone G
  have hold := (oldVertexIso G).card_edgeFinset_eq
  have hinduced := SimpleGraph.card_edgeFinset_induce_compl_singleton attached none
  have hdeleted := SimpleGraph.card_edgeFinset_deleteIncidenceSet attached none
  have hdegree := cone_degree_none G
  have hle := attached.degree_le_card_edgeFinset (v := none)
  change G.edgeFinset.card =
    (attached.induce ({(none : Option V)}ᶜ : Set (Option V))).edgeFinset.card at hold
  change attached.degree none = Fintype.card V at hdegree
  change attached.edgeFinset.card = G.edgeFinset.card + Fintype.card V
  omega

theorem finite_cone_edgeFinset_card {n : ℕ} (G : SimpleGraph (Fin n)) :
    (cone G).edgeFinset.card = G.edgeFinset.card + n := by
  simpa only [Fintype.card_fin] using cone_edgeFinset_card G

/-- All cycle-bound inputs concern the same cone of the whole original graph. -/
theorem finite_connected_path_free_cone {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : 5 ≤ k) (hkn : k ≤ n) (hG : G.Connected)
    (hfree : (pathGraph k).Free G) :
    (cone G).Connected ∧
    (∀ z : Option (Fin n),
      ((cone G).induce ({z}ᶜ : Set (Option (Fin n)))).Connected) ∧
    (∀ m : ℕ, k + 1 ≤ m → (cycleGraph m).Free (cone G)) ∧
    (cone G).edgeFinset.card = G.edgeFinset.card + n := by
  refine ⟨cone_connected G, cone_all_vertex_deletions_connected G hG, ?_,
    finite_cone_edgeFinset_card G⟩
  exact ErdosProblems.PathUpperReduction.UniformCone1105.finite_cone_all_long_cycle_free
    G hkn hk hfree

end ErdosProblems.PathUpperReduction.UniformConeStructure1105
end

namespace ErdosProblems.PathUpperReduction.UniformWindowScalar1105

open ErdosProblems.PathUpperReduction.CoreEndpointBound1105
open ErdosProblems.PathUpperReduction.ConnectedPathScalarChecked1105

/-- The odd-cone interval uses the accepted base endpoint theorem after the
exact cone shift. No new convexity argument is needed for this application. -/
theorem odd_cone_intermediate_count_le_endpoints (ell n d : ℕ)
    (hell : 4 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (hd3 : 3 ≤ d) (hdell : d ≤ ell) :
    extremalCount (n + 1) (2 * ell + 2) d ≤
      max (extremalCount (n + 1) (2 * ell + 2) 3)
        (extremalCount (n + 1) (2 * ell + 2) ell) := by
  have hk : 5 ≤ 2 * ell + 1 := by omega
  have hshift (a : ℕ) (ha : 1 ≤ a) (hak : a ≤ 2 * ell - 1) :
      extremalCount (n + 1) (2 * ell + 2) (a + 1) =
        n + extremalCount n (2 * ell) a := by
    have h := extremalCount_cone_shift n (2 * ell + 1) a hk hn ha (by omega)
    have hplus : 2 * ell + 1 + 1 = 2 * ell + 2 := by omega
    have hminus : 2 * ell + 1 - 1 = 2 * ell := by omega
    rw [hplus, hminus] at h
    exact h
  have hd : d - 1 + 1 = d := by omega
  have hl : ell - 1 + 1 = ell := by omega
  have h_d := hshift (d - 1) (by omega) (by omega)
  rw [hd] at h_d
  have h_three := hshift 2 (by omega) (by omega)
  have h_last := hshift (ell - 1) (by omega) (by omega)
  rw [hl] at h_last
  have hcap := extremalCount_endpoints n (2 * ell) (d - 1)
    (by omega) (by omega) (by omega) (by omega)
  have ht : (2 * ell - 1) / 2 = ell - 1 := by omega
  rw [ht] at hcap
  rw [h_d, h_three, h_last, ← add_max]
  exact Nat.add_le_add_left hcap n

/-- The literal odd FC linear branch, including its subtraction, equals
the existing h(n,k-1,ell-1) on the original n>=k domain. -/
theorem odd_linear_eq_extremal (ell n : ℕ) (hell : 4 ≤ ell)
    (hn : 2 * ell + 1 ≤ n) :
    extremalCount n (2 * ell) (ell - 1) =
      (ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1 := by
  have hmajor : 2 * ell - (ell - 1) = ell + 1 := by omega
  have hminor : n - 2 * ell + (ell - 1) = n - ell - 1 := by omega
  have htail : n - ell + 1 = (n - ell - 1) + 2 := by omega
  have hchoose_base : ell.choose 2 = (ell - 1) + (ell - 1).choose 2 := by
    have he : ell - 1 + 1 = ell := by omega
    simpa only [he, Nat.choose_one_right] using Nat.choose_succ_succ' (ell - 1) 1
  have hchoose : (ell + 1).choose 2 =
      (ell - 1).choose 2 + 2 * (ell - 1) + 1 := by
    have h : (ell + 1).choose 2 = ell + ell.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' ell 1
    rw [hchoose_base] at h
    omega
  unfold extremalCount
  rw [hmajor, hminor, hchoose, htail]
  ring

/-- For every original odd host, not just a finite window, the literal
maximum threshold dominates the intermediate a=2 path count. -/
theorem odd_original_threshold_dominates_two (ell n : ℕ) (hell : 4 ≤ ell)
    (hn : 2 * ell + 1 ≤ n) :
    extremalCount n (2 * ell) 2 ≤
      max ((2 * ell - 1).choose 2 + 1)
        (extremalCount n (2 * ell) (ell - 1)) := by
  have hKN : 2 * ell ≤ n := by omega
  have hpoly₂ := extremalCount_cast n (2 * ell) 2 (by omega) hKN
  have hpoly_last := extremalCount_cast n (2 * ell) (ell - 1) (by omega) hKN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hpoly₂
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ ell),
    Nat.cast_one] at hpoly_last
  have hA :
      2 * (((2 * ell - 1).choose 2 + 1 : ℕ) : ℚ) =
        4 * (ell : ℚ) ^ 2 - 6 * (ell : ℚ) + 4 := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_choose_two,
      Nat.cast_sub (by omega : 1 ≤ 2 * ell), Nat.cast_mul, Nat.cast_ofNat]
    ring
  by_cases hlow : n ≤ 3 * ell - 3
  · have hnt : n + 3 ≤ 3 * ell := by omega
    have hnq : (n : ℚ) + 3 ≤ 3 * (ell : ℚ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_le.mpr hnt : ((n + 3 : ℕ) : ℚ) ≤ ((3 * ell : ℕ) : ℚ))
    have hreal : (extremalCount n (2 * ell) 2 : ℚ) ≤
        (((2 * ell - 1).choose 2 + 1 : ℕ) : ℚ) := by
      nlinarith [hpoly₂, hA]
    exact le_trans (Nat.cast_le.mp hreal) (le_max_left _ _)
  · have hnt : 3 * ell ≤ n + 2 := by omega
    have hnq : 3 * (ell : ℚ) ≤ (n : ℚ) + 2 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_le.mpr hnt : ((3 * ell : ℕ) : ℚ) ≤ ((n + 2 : ℕ) : ℚ))
    have hellq : (4 : ℚ) ≤ (ell : ℚ) := Nat.cast_le.mpr hell
    have hfactor : 0 ≤ (ell : ℚ) - 3 := by linarith
    have hgap : 0 ≤ (n : ℚ) - (3 * (ell : ℚ) - 2) := by linarith
    have hmul := mul_nonneg hfactor hgap
    have hproduct := mul_nonneg
      (Nat.cast_nonneg ell : (0 : ℚ) ≤ (ell : ℚ)) hfactor
    have hreal : (extremalCount n (2 * ell) 2 : ℚ) ≤
        (extremalCount n (2 * ell) (ell - 1) : ℚ) := by
      nlinarith [hpoly₂, hpoly_last, hmul, hproduct]
    exact le_trans (Nat.cast_le.mp hreal) (le_max_right _ _)

/-- The exact original odd high-palette hypothesis gives the strict cone
threshold needed to exclude every actual core slot d>=3 and the empty core.
No graph, favorable core, rainbow path or closure premise is present. -/
theorem odd_palette_strict_cone_threshold (ell n q : ℕ) (hell : 4 ≤ ell)
    (hn : 2 * ell + 1 ≤ n)
    (hq : max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) < q) :
    max (extremalCount (n + 1) (2 * ell + 2) 3)
      (extremalCount (n + 1) (2 * ell + 2) ell) < n + q := by
  rw [← odd_linear_eq_extremal ell n hell hn] at hq
  have htwo : extremalCount n (2 * ell) 2 < q :=
    lt_of_le_of_lt (odd_original_threshold_dominates_two ell n hell hn) hq
  have hlast : extremalCount n (2 * ell) (ell - 1) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hsucc : 2 * ell + 1 + 1 = 2 * ell + 2 := by omega
  have hpred : 2 * ell + 1 - 1 = 2 * ell := by omega
  have hlastSucc : ell - 1 + 1 = ell := by omega
  have hthree := extremalCount_cone_shift n (2 * ell + 1) 2
    (by omega) hn (by omega) (by omega)
  have hcone_last := extremalCount_cone_shift n (2 * ell + 1) (ell - 1)
    (by omega) hn (by omega) (by omega)
  rw [hsucc, hpred] at hthree
  rw [hsucc, hpred, hlastSucc] at hcone_last
  rw [hthree, hcone_last, ← add_max]
  exact Nat.add_lt_add_left (max_lt_iff.mpr ⟨htwo, hlast⟩) n

end ErdosProblems.PathUpperReduction.UniformWindowScalar1105
