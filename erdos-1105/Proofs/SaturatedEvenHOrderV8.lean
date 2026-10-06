module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic

@[expose] public section

/-! Explicit `T` and `T2` paths for the saturated even-`H` motif, avoiding an arbitrary old-edge owner by permutations within its three parts. -/

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
