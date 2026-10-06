module

public import CycleTwoSelectedPathsRainbowV3
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Int.Cast.Basic

@[expose] public section

/-!
# Literal cyclic cross-color lift and adjacent translations

Every matrix entry is the original chi color of
the literal complete-host edge between the two cyclic orders. Palette
separation is from the full NEW union for that same chi; r is unchanged. No component, chord, degree, prescribed-endpoint path, or translation premise
is added. This module constructs no Copy: it applies the two-path provider.
-/

namespace ErdosProblems.AntiRamseyCycleCyclicCrossMatrixTranslations

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open scoped Fin.CommRing

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The next cyclic index, including the last-to-zero edge. -/
def cyclicSuccessor {a : ℕ} (ha : 0 < a) (x : Fin a) : Fin a :=
  letI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  x + 1

/-- A cyclic window index in either orientation. -/
def cyclicWindowIndex {a L : ℕ} (ha : 0 < a)
    (i : ℤ) (forward : Bool) (x : Fin L) : Fin a :=
  letI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  if forward then (i : Fin a) + (x.val : Fin a)
    else (i : Fin a) - (x.val : Fin a)

/-- A literal cyclic window of a given ordered vertex map. -/
def cyclicWindow {a L : ℕ} {α : Type*} (A : Fin a → α)
    (ha : 0 < a) (i : ℤ) (forward : Bool) : Fin L → α :=
  fun x => A (cyclicWindowIndex ha i forward x)

theorem cyclicWindowIndex_injective {a L : ℕ}
    (ha : 0 < a) (hL : L ≤ a) (i : ℤ) (forward : Bool) :
    Function.Injective (cyclicWindowIndex (L := L) ha i forward) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  have hsmall : Function.Injective (fun x : Fin L => (x.val : Fin a)) := by
    intro x y hxy
    apply Fin.val_injective
    have hv := congrArg Fin.val hxy
    rw [Fin.val_natCast, Fin.val_natCast,
      Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt hL),
      Nat.mod_eq_of_lt (lt_of_lt_of_le y.isLt hL)] at hv
    exact hv
  cases forward with
  | false =>
    intro x y hxy
    change (i : Fin a) - (x.val : Fin a) =
      (i : Fin a) - (y.val : Fin a) at hxy
    exact hsmall (sub_right_inj.mp hxy)
  | true =>
    intro x y hxy
    change (i : Fin a) + (x.val : Fin a) =
      (i : Fin a) + (y.val : Fin a) at hxy
    exact hsmall (add_left_cancel hxy)

theorem cyclicWindow_injective {a L : ℕ} {α : Type*}
    (A : Fin a → α) (ha : 0 < a) (hA : Function.Injective A)
    (hL : L ≤ a) (i : ℤ) (forward : Bool) :
    Function.Injective (cyclicWindow (L := L) A ha i forward) :=
  hA.comp (cyclicWindowIndex_injective ha hL i forward)

theorem cyclicWindow_path {a L : ℕ} {α : Type*}
    (G : SimpleGraph α) (A : Fin a → α) (ha : 0 < a)
    (hcycle : ∀ x : Fin a, G.Adj (A x) (A (cyclicSuccessor ha x)))
    (i : ℤ) (forward : Bool) :
    ∀ x y : Fin L, x.val + 1 = y.val →
      G.Adj (cyclicWindow A ha i forward x) (cyclicWindow A ha i forward y) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  intro x y hxy
  have hy : (y.val : Fin a) = (x.val : Fin a) + 1 := by
    rw [← hxy, Nat.cast_add, Nat.cast_one]
  cases forward with
  | false =>
    change G.Adj (A ((i : Fin a) - (x.val : Fin a)))
      (A ((i : Fin a) - (y.val : Fin a)))
    have hindex : (i : Fin a) - (y.val : Fin a) + 1 =
        (i : Fin a) - (x.val : Fin a) := by
      rw [hy]
      abel
    have hs := (hcycle ((i : Fin a) - (y.val : Fin a))).symm
    change G.Adj (A ((i : Fin a) - (y.val : Fin a) + 1))
      (A ((i : Fin a) - (y.val : Fin a))) at hs
    exact hindex ▸ hs
  | true =>
    change G.Adj (A ((i : Fin a) + (x.val : Fin a)))
      (A ((i : Fin a) + (y.val : Fin a)))
    rw [hy, ← add_assoc]
    exact hcycle ((i : Fin a) + (x.val : Fin a))

/-- The actual original complete-host cross edge; disjointness proves it exists. -/
def cyclicCrossEdge {a b : ℕ} (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (x : Fin a) (y : Fin b) : HostEdge n :=
  ⟨s(A x, B y), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    apply (top_adj _ _).mpr
    exact Set.disjoint_range_iff.mp hdisjoint x y⟩

/-- The literal integer lift of the original cross-edge color matrix. -/
def liftedCrossColor {a b : ℕ} (χ : TopEdgeLabeling (Fin n) C)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hdisjoint : Disjoint (Set.range A) (Set.range B)) : ℤ → ℤ → C :=
  letI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  letI : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  fun i j => χ (cyclicCrossEdge A B hdisjoint (i : Fin a) (j : Fin b))

omit [DecidableEq C] in
/-- Both exact integer periods of the literal lift. -/
theorem liftedCrossColor_periodic [DecidableEq C] {a b : ℕ} (χ : TopEdgeLabeling (Fin n) C)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hdisjoint : Disjoint (Set.range A) (Set.range B)) :
    (∀ i j : ℤ, liftedCrossColor χ A B ha hb hdisjoint (i + a) j =
      liftedCrossColor χ A B ha hb hdisjoint i j) ∧
    (∀ i j : ℤ, liftedCrossColor χ A B ha hb hdisjoint i (j + b) =
      liftedCrossColor χ A B ha hb hdisjoint i j) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  let : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  constructor <;> intro i j <;>
    simp only [liftedCrossColor, Int.cast_add, Int.cast_natCast,
      Fin.natCast_self, add_zero]

theorem cyclic_rectangle_cross_colors_eq
    {a b L T : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : ∀ x : Fin a,
      (selectedGraph χ r).Adj (A x) (A (cyclicSuccessor ha x)))
    (hBcycle : ∀ y : Fin b,
      (selectedGraph χ r).Adj (B y) (B (cyclicSuccessor hb y)))
    (hpalette : ∀ x : Fin a, ∀ y : Fin b,
      χ (cyclicCrossEdge A B hdisjoint x y) ∉ newColorUnion χ)
    (hL : 2 ≤ L) (hT : 2 ≤ T) (hLa : L ≤ a) (hTb : T ≤ b)
    (hno : ¬ ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ) (i j : ℤ) (forward : Bool) :
    liftedCrossColor χ A B ha hb hdisjoint (i + (L - 1 : ℕ)) j =
      liftedCrossColor χ A B ha hb hdisjoint i
        (j + if forward then ((T - 1 : ℕ) : ℤ) else -((T - 1 : ℕ) : ℤ)) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  let : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  let AP : Fin L → Fin n := cyclicWindow A ha i true
  let BP : Fin T → Fin n := cyclicWindow B hb j forward
  have hpathsDisjoint : Disjoint (Set.range AP) (Set.range BP) := by
    apply Set.disjoint_range_iff.mpr
    intro x y
    exact Set.disjoint_range_iff.mp hdisjoint
      (cyclicWindowIndex ha i true x) (cyclicWindowIndex hb j forward y)
  let between : HostEdge n := cyclicCrossEdge A B hdisjoint
    ((i + (L - 1 : ℕ) : ℤ) : Fin a) (j : Fin b)
  let closing : HostEdge n := cyclicCrossEdge A B hdisjoint (i : Fin a)
    ((j + if forward then ((T - 1 : ℕ) : ℤ) else -((T - 1 : ℕ) : ℤ) : ℤ) : Fin b)
  have hbetween : between.val =
      s(AP ⟨L - 1, by omega⟩, BP ⟨0, by omega⟩) := by
    change s(A ((i + (L - 1 : ℕ) : ℤ) : Fin a), B (j : Fin b)) =
      s(cyclicWindow A ha i true ⟨L - 1, by omega⟩,
        cyclicWindow B hb j forward ⟨0, by omega⟩)
    cases forward <;>
      simp [cyclicWindow, cyclicWindowIndex]
  have hclosing : closing.val =
      s(AP ⟨0, by omega⟩, BP ⟨T - 1, by omega⟩) := by
    change s(A (i : Fin a),
      B ((j + if forward then ((T - 1 : ℕ) : ℤ) else -((T - 1 : ℕ) : ℤ) : ℤ) : Fin b)) =
      s(cyclicWindow A ha i true ⟨0, by omega⟩,
        cyclicWindow B hb j forward ⟨T - 1, by omega⟩)
    cases forward with
    | false => simp [cyclicWindow, cyclicWindowIndex, sub_eq_add_neg]
    | true => simp [cyclicWindow, cyclicWindowIndex]
  change χ between = χ closing
  by_contra hdifferent
  exact hno
    (ErdosProblems.AntiRamseyTwoSelectedPathsRainbow.two_disjoint_selected_paths_close_rainbow
      χ r hL hT AP BP
      (cyclicWindow_injective A ha hA hLa i true)
      (cyclicWindow_injective B hb hB hTb j forward) hpathsDisjoint
      (cyclicWindow_path (selectedGraph χ r) A ha hAcycle i true)
      (cyclicWindow_path (selectedGraph χ r) B hb hBcycle j forward)
      between closing hbetween hclosing (hpalette _ _) (hpalette _ _) hdifferent)

theorem cyclic_split_translations
    {a b L T : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : ∀ x : Fin a,
      (selectedGraph χ r).Adj (A x) (A (cyclicSuccessor ha x)))
    (hBcycle : ∀ y : Fin b,
      (selectedGraph χ r).Adj (B y) (B (cyclicSuccessor hb y)))
    (hpalette : ∀ x : Fin a, ∀ y : Fin b,
      χ (cyclicCrossEdge A B hdisjoint x y) ∉ newColorUnion χ)
    (hL : 2 ≤ L) (hT : 2 ≤ T) (hLa : L ≤ a) (hTb : T ≤ b)
    (hno : ¬ ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ) (i j : ℤ) :
    liftedCrossColor χ A B ha hb hdisjoint i j =
      liftedCrossColor χ A B ha hb hdisjoint
        (i + (L - 1 : ℕ)) (j + (T - 1 : ℕ)) ∧
    liftedCrossColor χ A B ha hb hdisjoint i j =
      liftedCrossColor χ A B ha hb hdisjoint
        (i + (L - 1 : ℕ)) (j - (T - 1 : ℕ)) := by
  have hp := cyclic_rectangle_cross_colors_eq χ r A B ha hb hA hB hdisjoint
    hAcycle hBcycle hpalette hL hT hLa hTb hno i (j + (T - 1 : ℕ)) false
  have hn := cyclic_rectangle_cross_colors_eq χ r A B ha hb hA hB hdisjoint
    hAcycle hBcycle hpalette hL hT hLa hTb hno i (j - (T - 1 : ℕ)) true
  constructor
  · simpa using hp.symm
  · simpa using hn.symm

/-- The four exact adjacent-split translations of the same periodic literal
matrix. No matrix invariance is a premise. -/
theorem cyclic_cross_matrix_has_adjacent_translations
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : ∀ x : Fin a,
      (selectedGraph χ r).Adj (A x) (A (cyclicSuccessor (by omega) x)))
    (hBcycle : ∀ y : Fin b,
      (selectedGraph χ r).Adj (B y) (B (cyclicSuccessor (by omega) y)))
    (hpalette : ∀ x : Fin a, ∀ y : Fin b,
      χ (cyclicCrossEdge A B hdisjoint x y) ∉ newColorUnion χ)
    (hno : ¬ ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ) :
    let L : ℕ := max 2 (k - b)
    let d : ℤ := (L : ℤ) - 1
    let e : ℤ := (k : ℤ) - L - 1
    let M : ℤ → ℤ → C := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
    ∀ i j : ℤ,
      M i j = M (i + d) (j + e) ∧
      M i j = M (i + d + 1) (j + e - 1) ∧
      M i j = M (i + d) (j - e) ∧
      M i j = M (i + d + 1) (j - e + 1) := by
  let ha0 : 0 < a := by omega
  let hb0 : 0 < b := by omega
  let L : ℕ := max 2 (k - b)
  let T : ℕ := k - L
  let d : ℤ := (L : ℤ) - 1
  let e : ℤ := (k : ℤ) - L - 1
  let M : ℤ → ℤ → C := liftedCrossColor χ A B ha0 hb0 hdisjoint
  change ∀ i j : ℤ,
    M i j = M (i + d) (j + e) ∧
    M i j = M (i + d + 1) (j + e - 1) ∧
    M i j = M (i + d) (j - e) ∧
    M i j = M (i + d + 1) (j - e + 1)
  have hL : 2 ≤ L := le_max_left _ _
  have hLa : L + 1 ≤ a := by
    have hm : max 2 (k - b) ≤ a - 1 := max_le (by omega) (by omega)
    dsimp only [L]
    omega
  have hLk : L ≤ k - 3 := by
    exact max_le (by omega) (by omega)
  have hLb : k - b ≤ L := le_max_right _ _
  have hT : 3 ≤ T := by dsimp only [T]; omega
  have hTb : T ≤ b := by dsimp only [T]; omega
  have hcount : L + T = k := by dsimp only [T]; omega
  have hcount' : (L + 1) + (T - 1) = k := by omega
  have hno0 : ¬ ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by exact hcount.symm ▸ hno
  have hno1 : ¬ ∃ f : (cycleGraph ((L + 1) + (T - 1))).Copy
      (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
    exact hcount'.symm ▸ hno
  have hd0 : ((L - 1 : ℕ) : ℤ) = d := by dsimp only [d]; omega
  have he0 : ((T - 1 : ℕ) : ℤ) = e := by dsimp only [T, e]; omega
  have hd1 : (((L + 1) - 1 : ℕ) : ℤ) = d + 1 := by dsimp only [d]; omega
  have he1 : (((T - 1) - 1 : ℕ) : ℤ) = e - 1 := by dsimp only [T, e]; omega
  intro i j
  have h0 := cyclic_split_translations χ r A B ha0 hb0 hA hB hdisjoint
    hAcycle hBcycle hpalette hL (by omega) (by omega) hTb hno0 i j
  have h1 := cyclic_split_translations (L := L + 1) (T := T - 1)
    χ r A B ha0 hb0 hA hB hdisjoint hAcycle hBcycle hpalette
    (by omega) (by omega) hLa (by omega) hno1 i j
  rw [hd0, he0] at h0
  rw [hd1, he1] at h1
  have hi : i + (d + 1) = i + d + 1 := by omega
  have hjp : j + (e - 1) = j + e - 1 := by omega
  have hjn : j - (e - 1) = j - e + 1 := by omega
  rw [hi, hjp, hjn] at h1
  exact ⟨h0.1, h1.1, h0.2, h1.2⟩

end ErdosProblems.AntiRamseyCycleCyclicCrossMatrixTranslations
