module

/-
Copyright 2026 The Formal Conjectures Authors.
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

public import Erdos107Unified435
public import InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Set
open EuclideanGeometry

/-!
# Erdős Problem #107: General-Position Shear/Sorting Bridge to `IsXMonotone` and KKS $(3, 4, 2)$ / $(3, 3, 3)$ Wedge-Pigeonhole Pentagon Forcing

This module extends `Erdos107Unified435.lean` and
`InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107.lean` on the Erdős–Szekeres convex polygon
problem (`erdos_107`) across four sections:

1. **Horizontal Shear Transformations (`shearPt`) and Exact Invariance of `lineSide`, `Collinear`, `NonTrilinear`, `ConvexIndep`, and `HasConvexNGon`**:
   We define the horizontal shear map `shearPt m p = mkPt (p 0 + m * p 1) (p 1)` and its linear wrapper
   `shearLinearMap m : ℝ² →ₗ[ℝ] ℝ²`, prove exact determinant invariance `lineSide_shearPt` and
   collinearity/general-position invariance (`collinear_shearPt_iff`, `nonTrilinear_image_shearPt`),
   and deduce via `LinearMap.image_convexHull` that `ConvexIndep` and `HasConvexNGon` are invariant
   under every horizontal shear (`convexIndep_image_shearPt`, `hasConvexNGon_image_shearPt_iff`).
   We construct an explicit finite-avoidance shear slope `goodShearSlope pts` that guarantees strict
   $x$-coordinate injectivity (`shearPt_x_injOn_goodShearSlope`) on any finite point set `pts : Finset ℝ²`.

2. **General-Position $x$-Coordinate Sorting Bridge (`xSortedSeq`) and Unconditional Membership `erdosSzekeresUpper k ∈ cardSet k`**:
   Using `Finset.orderEmbOfFin` on the image of $x$-coordinates, we construct `xSortedSeq T : ℕ → ℝ²`,
   prove that it is globally `IsXMonotone` (`isXMonotone_xSortedSeq`), bijects `Finset.range T.card`
   onto `T` (`image_xSortedSeq_range`), and preserves general position on `Finset.range T.card`
   (`isSeqNonTrilinearOn_xSortedSeq`). Combining localized cup–cap recursion (`erdos_szekeres_cup_cap_theorem_on`)
   with `hasConvexNGon_of_hasCup_or_hasCap` and `goodShearSlope`, we prove unconditionally for all $k \ge 2$
   that `erdosSzekeresUpper k ∈ cardSet k` (`erdosSzekeresUpper_mem_cardSet`), resolve the FormalConjectures
   theorem `nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty` with zero `sorry`, and establish the
   unconditional bounds `f k ≤ erdosSzekeresUpper k`, `n ≤ f n`, `f m ≤ f n` ($m \le n$), and `5 ≤ f 4 ∧ f 4 ≤ 7`.

3. **Kalbfleisch–Kalbfleisch–Stanton $(3, 4, 2)$ and $(3, 3, 3)$ Inner-Triangle Wedge-Pigeonhole Pentagon Forcing**:
   We prove the universal edge-pair same-open-side 4-triple orientation lemma
   (`kks_edge_pair_same_open_side_all_four_triples_pos`) and positive/negative cap-wedge pentagon forcing
   theorems (`kks_edge_pair_pos_wedge_forces_fiveGon`, `kks_edge_pair_neg_wedge_forces_fiveGon`), the
   4-sign cyclic/diagonal dichotomy (`pigeonhole_four_signs_cyclic_or_diag`), the $(3, 4, 2)$ middle-4-gon
   and outer-triangle line separation reductions (`kks_three_four_two_middle_quad_line_dichotomy`,
   `kks_three_four_two_wedge_pentagon_reduction`), the $(3, 3, 3)$ exterior edge-halfplane covering and
   4-exterior-point pigeonhole reductions (`kks_triangle_exterior_point_edge_covering`,
   `kks_four_exterior_points_edge_pigeonhole`, `kks_three_three_three_wedge_pentagon_reduction`), and the
   complete $(3, 6)$-layer reduction (`kks_three_six_layer_complete_reduction`).

4. **Positive and Negative Controls**:
   We prove that the convex-independent inner square `{sqPP, sqNP, sqNN, sqPN}` fails raw $x$-coordinate
   injectivity before shearing (`not_injOn_x_innerSquare`, negative control) while horizontal shearing
   restores injectivity and preserves `ConvexIndep`, and that a vertical collinear triple remains collinear
   under every horizontal shear (`collinear_shearPt_vertical_triple`, negative control showing `NonTrilinear`
   is essential).
-/

namespace Erdos107

/-! ## Section 1: Horizontal Shear Transformations and Exact Geometric Invariance -/

/-- Horizontal shear transformation $T_m(x, y) = (x + m y, y)$ on $\mathbb{R}^2$. -/
def shearPt (m : ℝ) (p : ℝ²) : ℝ² :=
  mkPt (p 0 + m * p 1) (p 1)

@[simp]
theorem shearPt_zero (m : ℝ) (p : ℝ²) : shearPt m p 0 = p 0 + m * p 1 := by
  simp [shearPt]

#print axioms shearPt_zero

@[simp]
theorem shearPt_one (m : ℝ) (p : ℝ²) : shearPt m p 1 = p 1 := by
  simp [shearPt]

#print axioms shearPt_one

/-- Horizontal shear with slope $-m$ is the exact two-sided inverse of `shearPt m`. -/
theorem shearPt_neg_cancel (m : ℝ) (p : ℝ²) : shearPt (-m) (shearPt m p) = p := by
  ext i; fin_cases i
  · simp [shearPt]
  · simp [shearPt]

#print axioms shearPt_neg_cancel

/-- Every horizontal shear transformation `shearPt m` is injective on $\mathbb{R}^2$. -/
theorem shearPt_injective (m : ℝ) : Function.Injective (shearPt m) := by
  intro p q hpq
  have h := congrArg (shearPt (-m)) hpq
  simpa [shearPt_neg_cancel] using h

#print axioms shearPt_injective

/-- **Exact Oriented Area Invariance Under Horizontal Shear**:
For every $m \in \mathbb{R}$ and $p, q, r \in \mathbb{R}^2$, `shearPt m` preserves `lineSide` identically. -/
theorem lineSide_shearPt (m : ℝ) (p q r : ℝ²) :
    lineSide (shearPt m p) (shearPt m q) (shearPt m r) = lineSide p q r := by
  dsimp [lineSide, shearPt]
  simp only [mkPt_zero, mkPt_one]
  ring

#print axioms lineSide_shearPt

/-- Collinearity of any triple in $\mathbb{R}^2$ is invariant under `shearPt m`. -/
theorem collinear_shearPt_iff (m : ℝ) (p q r : ℝ²) :
    Collinear ℝ ({shearPt m p, shearPt m q, shearPt m r} : Set ℝ²) ↔
      Collinear ℝ ({p, q, r} : Set ℝ²) := by
  constructor
  · intro h
    apply collinear_of_lineSide_eq_zero
    rw [← lineSide_shearPt m]
    exact cross_eq_zero_of_collinear h
  · intro h
    apply collinear_of_lineSide_eq_zero
    rw [lineSide_shearPt m]
    exact cross_eq_zero_of_collinear h

#print axioms collinear_shearPt_iff

/-- General position (`NonTrilinear`) of any planar point set is preserved under `shearPt m`. -/
theorem nonTrilinear_image_shearPt {A : Set ℝ²} (m : ℝ) (hA : NonTrilinear A) :
    NonTrilinear (shearPt m '' A) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hyz hxz
  have hxy' : x ≠ y := fun h => hxy (congrArg (shearPt m) h)
  have hyz' : y ≠ z := fun h => hyz (congrArg (shearPt m) h)
  have hxz' : x ≠ z := fun h => hxz (congrArg (shearPt m) h)
  rw [collinear_shearPt_iff]
  exact hA hx hy hz hxy' hyz' hxz'

#print axioms nonTrilinear_image_shearPt

/-- Linear map packaging of `shearPt m`. -/
def shearLinearMap (m : ℝ) : ℝ² →ₗ[ℝ] ℝ² where
  toFun := shearPt m
  map_add' p q := by
    ext i; fin_cases i
    · simp [shearPt]; ring
    · simp [shearPt]
  map_smul' c p := by
    ext i; fin_cases i
    · simp [shearPt]; ring
    · simp [shearPt]

/-- Horizontal shear commutes with `convexHull ℝ`. -/
theorem image_shearPt_convexHull (m : ℝ) (s : Set ℝ²) :
    shearPt m '' convexHull ℝ s = convexHull ℝ (shearPt m '' s) :=
  LinearMap.image_convexHull (shearLinearMap m) s

#print axioms image_shearPt_convexHull

/-- Convex independence (`ConvexIndep`) is preserved under `shearPt m`. -/
theorem convexIndep_image_shearPt {S : Set ℝ²} (m : ℝ) (hS : ConvexIndep S) :
    ConvexIndep (shearPt m '' S) := by
  rintro _ ⟨a, ha, rfl⟩ hmem
  have hdiff : (shearPt m '' S) \ {shearPt m a} = shearPt m '' (S \ {a}) :=
    (Set.image_diff (shearPt_injective m) S {a}).symm ▸ by simp
  rw [hdiff, ← image_shearPt_convexHull] at hmem
  rcases hmem with ⟨b, hb, hba⟩
  have hab : b = a := shearPt_injective m hba
  subst hab
  exact hS b ha hb

#print axioms convexIndep_image_shearPt

/-- Existence of a convex $n$-gon (`HasConvexNGon n`) is invariant under `shearPt m`. -/
theorem hasConvexNGon_image_shearPt_iff (m : ℝ) (n : ℕ) (A : Set ℝ²) :
    HasConvexNGon n (shearPt m '' A) ↔ HasConvexNGon n A := by
  constructor
  · rintro ⟨T, hTcard, hTsub, hTconv⟩
    refine ⟨T.image (shearPt (-m)), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (shearPt_injective (-m)), hTcard]
    · intro x hx
      rw [Finset.coe_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      rcases hTsub hy with ⟨z, hz, rfl⟩
      simpa [shearPt_neg_cancel] using hz
    · rw [Finset.coe_image]
      exact convexIndep_image_shearPt (-m) hTconv
  · rintro ⟨S, hScard, hSsub, hSconv⟩
    refine ⟨S.image (shearPt m), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (shearPt_injective m), hScard]
    · rw [Finset.coe_image]
      exact Set.image_mono hSsub
    · rw [Finset.coe_image]
      exact convexIndep_image_shearPt m hSconv

#print axioms hasConvexNGon_image_shearPt_iff

/-- Explicit real selector avoiding any finite set $B \subseteq \mathbb{R}$. -/
def avoidFinsetReal (B : Finset ℝ) : ℝ :=
  if h : B.Nonempty then B.max' h + 1 else 0

theorem avoidFinsetReal_not_mem (B : Finset ℝ) : avoidFinsetReal B ∉ B := by
  dsimp [avoidFinsetReal]
  split_ifs with h
  · intro hmem
    have hle := Finset.le_max' B (B.max' h + 1) hmem
    linarith
  · intro hmem
    exact h ⟨0, hmem⟩

#print axioms avoidFinsetReal_not_mem

/-- The finite set of forbidden shear slopes $(q_0 - p_0)/(p_1 - q_1)$ for pairs $(p, q) \in \text{pts}^2$. -/
def forbiddenShearSlopes (pts : Finset ℝ²) : Finset ℝ :=
  (pts ×ˢ pts).image (fun pq => (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1))

/-- Canonical shear slope avoiding all forbidden slopes of `pts`. -/
def goodShearSlope (pts : Finset ℝ²) : ℝ :=
  avoidFinsetReal (forbiddenShearSlopes pts)

/-- **Universal Finite-Point-Set $x$-Coordinate Perturbation Lemma**:
For every finite point set `pts : Finset ℝ²`, the sheared point set under `goodShearSlope pts`
has strictly distinct $x$-coordinates (`Set.InjOn (fun p => shearPt (goodShearSlope pts) p 0) pts`). -/
theorem shearPt_x_injOn_goodShearSlope (pts : Finset ℝ²) :
    Set.InjOn (fun p => shearPt (goodShearSlope pts) p 0) (pts : Set ℝ²) := by
  intro p hp q hq heq
  simp only [shearPt_zero] at heq
  by_cases hpq1 : p 1 = q 1
  · have hpq0 : p 0 = q 0 := by rw [hpq1] at heq; linarith
    ext i; fin_cases i
    · exact hpq0
    · exact hpq1
  · exfalso
    have hsub : p 1 - q 1 ≠ 0 := sub_ne_zero.mpr hpq1
    have hm : goodShearSlope pts = (q 0 - p 0) / (p 1 - q 1) := by
      rw [eq_div_iff hsub]
      linarith
    have hmem : goodShearSlope pts ∈ forbiddenShearSlopes pts := by
      rw [hm]
      exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    exact avoidFinsetReal_not_mem (forbiddenShearSlopes pts) hmem

#print axioms shearPt_x_injOn_goodShearSlope

/-! ## Section 2: General-Position $x$-Coordinate Sorting Bridge and Unconditional `erdosSzekeresUpper k ∈ cardSet k` -/

/-- Inverse lookup of a point in $T$ by its $x$-coordinate, defaulting to $(x, 0)$ outside the $x$-projection of $T$. -/
def pointOfX (T : Finset ℝ²) (x : ℝ) : ℝ² :=
  if hx : x ∈ T.image (fun p : ℝ² => p 0) then
    Classical.choose (Finset.mem_image.mp hx)
  else
    mkPt x 0

@[simp]
theorem pointOfX_zero (T : Finset ℝ²) (x : ℝ) : pointOfX T x 0 = x := by
  dsimp [pointOfX]
  split_ifs with hx
  · exact (Classical.choose_spec (Finset.mem_image.mp hx)).2
  · simp

#print axioms pointOfX_zero

theorem pointOfX_mem (T : Finset ℝ²) {x : ℝ} (hx : x ∈ T.image (fun p : ℝ² => p 0)) :
    pointOfX T x ∈ T := by
  dsimp [pointOfX]
  rw [dif_pos hx]
  exact (Classical.choose_spec (Finset.mem_image.mp hx)).1

#print axioms pointOfX_mem

theorem pointOfX_self {T : Finset ℝ²} (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²))
    {p : ℝ²} (hp : p ∈ T) : pointOfX T (p 0) = p := by
  have hx : p 0 ∈ T.image (fun q : ℝ² => q 0) := Finset.mem_image_of_mem _ hp
  exact hinj (pointOfX_mem T hx) hp (pointOfX_zero T (p 0))

#print axioms pointOfX_self

/-- Strictly increasing $x$-coordinate sequence enumerating `T.image (· 0)` via `Finset.orderEmbOfFin`
on $0 \dots |X| - 1$ and extending linearly for $i \ge |X|$. -/
def xSortedX (T : Finset ℝ²) (i : ℕ) : ℝ :=
  let X := T.image (fun p : ℝ² => p 0)
  if hi : i < X.card then
    X.orderEmbOfFin rfl ⟨i, hi⟩
  else
    (if hX : X.Nonempty then X.max' hX else 0) + ((i - X.card + 1 : ℕ) : ℝ)

/-- Canonical $x$-sorted point sequence `xSortedSeq T : ℕ → ℝ²` associated to a finite point set $T$. -/
def xSortedSeq (T : Finset ℝ²) (i : ℕ) : ℝ² :=
  pointOfX T (xSortedX T i)

/-- For every finite point set $T \subseteq \mathbb{R}^2$, `xSortedSeq T` is globally $x$-monotone (`IsXMonotone`). -/
theorem isXMonotone_xSortedSeq (T : Finset ℝ²) : IsXMonotone (xSortedSeq T) := by
  intro i j hij
  simp only [xSortedSeq, pointOfX_zero, xSortedX]
  let X := T.image (fun p : ℝ² => p 0)
  by_cases hj : j < X.card
  · have hi : i < X.card := lt_trans hij hj
    rw [dif_pos hi, dif_pos hj]
    exact (X.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)
  · rw [dif_neg hj]
    by_cases hi : i < X.card
    · rw [dif_pos hi]
      have hmem : X.orderEmbOfFin rfl ⟨i, hi⟩ ∈ X := Finset.orderEmbOfFin_mem X rfl ⟨i, hi⟩
      have hX : X.Nonempty := ⟨_, hmem⟩
      rw [dif_pos hX]
      have hle : X.orderEmbOfFin rfl ⟨i, hi⟩ ≤ X.max' hX := Finset.le_max' X _ hmem
      have hpos : (0 : ℝ) < ((j - X.card + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      linarith
    · rw [dif_neg hi]
      have hlt_nat : i - X.card + 1 < j - X.card + 1 := by omega
      have hlt_real : ((i - X.card + 1 : ℕ) : ℝ) < ((j - X.card + 1 : ℕ) : ℝ) := by
        exact_mod_cast hlt_nat
      linarith

#print axioms isXMonotone_xSortedSeq

/-- **Exact Range Identification for $x$-Injective Finite Point Sets**:
Whenever $T$ has distinct $x$-coordinates, `xSortedSeq T` maps `Finset.range T.card` onto $T$. -/
theorem image_xSortedSeq_range {T : Finset ℝ²}
    (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²)) :
    xSortedSeq T '' ((Finset.range T.card : Finset ℕ) : Set ℕ) = (T : Set ℝ²) := by
  let X := T.image (fun p : ℝ² => p 0)
  have hXcard : X.card = T.card := Finset.card_image_of_injOn hinj
  ext p
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hiX : i < X.card := by omega
    have hxmem : xSortedX T i ∈ X := by
      dsimp [xSortedX]
      rw [dif_pos hiX]
      exact Finset.orderEmbOfFin_mem X rfl ⟨i, hiX⟩
    exact pointOfX_mem T hxmem
  · intro hp
    have hpX : p 0 ∈ (X : Set ℝ) := Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hp)
    rw [← Finset.range_orderEmbOfFin X rfl] at hpX
    rcases hpX with ⟨⟨i, hiX⟩, hi_eq⟩
    refine ⟨i, by omega, ?_⟩
    dsimp [xSortedSeq, xSortedX]
    rw [dif_pos hiX, hi_eq]
    exact pointOfX_self hinj hp

#print axioms image_xSortedSeq_range

/-- Localized non-trilinearity of a sequence $P : \mathbb{N} \to \mathbb{R}^2$ restricted to $S : \text{Finset}\,\mathbb{N}$. -/
def IsSeqNonTrilinearOn (P : ℕ → ℝ²) (S : Finset ℕ) : Prop :=
  ∀ ⦃i j k : ℕ⦄, i ∈ S → j ∈ S → k ∈ S → i < j → j < k →
    ¬ Collinear ℝ ({P i, P j, P k} : Set ℝ²)

theorem isSeqNonTrilinearOn_mono {P : ℕ → ℝ²} {S T : Finset ℕ}
    (hST : S ⊆ T) (hT : IsSeqNonTrilinearOn P T) :
    IsSeqNonTrilinearOn P S :=
  fun _ _ _ hi hj hk hij hjk => hT (hST hi) (hST hj) (hST hk) hij hjk

#print axioms isSeqNonTrilinearOn_mono

/-- If $T \subseteq \mathbb{R}^2$ is `NonTrilinear` and has distinct $x$-coordinates, then `xSortedSeq T`
satisfies `IsSeqNonTrilinearOn` on `Finset.range T.card`. -/
theorem isSeqNonTrilinearOn_xSortedSeq {T : Finset ℝ²}
    (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²))
    (hnt : NonTrilinear (T : Set ℝ²)) :
    IsSeqNonTrilinearOn (xSortedSeq T) (Finset.range T.card) := by
  intro i j k hi hj hk hij hjk
  have hmono := isXMonotone_xSortedSeq T
  have himg := image_xSortedSeq_range hinj
  have hiT : xSortedSeq T i ∈ (T : Set ℝ²) := by
    rw [← himg]; exact ⟨i, hi, rfl⟩
  have hjT : xSortedSeq T j ∈ (T : Set ℝ²) := by
    rw [← himg]; exact ⟨j, hj, rfl⟩
  have hkT : xSortedSeq T k ∈ (T : Set ℝ²) := by
    rw [← himg]; exact ⟨k, hk, rfl⟩
  exact hnt hiT hjT hkT
    (xMonotone_ne_of_lt hmono hij)
    (xMonotone_ne_of_lt hmono hjk)
    (xMonotone_ne_of_lt hmono (lt_trans hij hjk))

#print axioms isSeqNonTrilinearOn_xSortedSeq

/-- Localized Endpoint-Gluing Lemma on a finite index set $S$. -/
theorem cup_end_meets_cap_start_on {P : ℕ → ℝ²} {S : Finset ℕ} {m k a b c : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinearOn P S)
    (hcup : CupChainEnding P S m a b) (hcap : CapChainStarting P S k b c) :
    HasCup P S (m + 1) ∨ HasCap P S (k + 1) := by
  have hab : a < b := cupChainEnding_lt hcup
  have hbc : b < c := capChainStarting_lt hcap
  have haS : a ∈ S := cupChainEnding_left_mem hcup
  have hbS : b ∈ S := cupChainEnding_right_mem hcup
  have hcS : c ∈ S := capChainStarting_right_mem hcap
  have hxne : P a 0 ≠ P b 0 := ne_of_lt (hmono hab)
  have hnc : ¬ Collinear ℝ ({P a, P b, P c} : Set ℝ²) := hnontri haS hbS hcS hab hbc
  rcases slopeLt_or_slopeGt_of_not_collinear hxne hnc with hsl | hsg
  · exact Or.inl ⟨b, c, hbS, hcS, hbc, a, hcup, hsl⟩
  · exact Or.inr ⟨a, b, haS, hbS, hab, c, hsg, hcap⟩

#print axioms cup_end_meets_cap_start_on

/-- Localized Erdős–Szekeres Cup–Cap Theorem on any finite index set $S$ where `IsSeqNonTrilinearOn P S` holds. -/
theorem erdos_szekeres_cup_cap_theorem_on {P : ℕ → ℝ²} (hmono : IsXMonotone P) :
    ∀ (m k : ℕ) (S : Finset ℕ),
      IsSeqNonTrilinearOn P S →
      (m + k).choose m + 1 ≤ S.card → HasCup P S m ∨ HasCap P S k
  | 0, _, S, _, hcard => by
      simp only [Nat.zero_add, Nat.choose_zero_right] at hcard
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inl ⟨x, y, hx, hy, hlt⟩
      · exact Or.inl ⟨y, x, hy, hx, hgt⟩
  | _ + 1, 0, S, _, hcard => by
      simp only [Nat.add_zero, Nat.choose_self] at hcard
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inr ⟨x, y, hx, hy, hlt⟩
      · exact Or.inr ⟨y, x, hy, hx, hgt⟩
  | m + 1, k + 1, S, hnontri, hcard => by
      classical
      let E : Finset ℕ := S.filter (fun b => ∃ a, CupChainEnding P S m a b)
      have hES : E ⊆ S := Finset.filter_subset _ _
      have hpart : (S \ E).card + E.card = S.card := Finset.card_sdiff_add_card_eq_card hES
      have hchoose : ((m + 1) + (k + 1)).choose (m + 1) =
          (m + (k + 1)).choose m + ((m + 1) + k).choose (m + 1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.choose_succ_succ (m + k + 1) m
      by_cases hSE : (m + (k + 1)).choose m + 1 ≤ (S \ E).card
      · rcases erdos_szekeres_cup_cap_theorem_on hmono m (k + 1) (S \ E)
            (isSeqNonTrilinearOn_mono Finset.sdiff_subset hnontri) hSE with hcup | hcap
        · rcases hcup with ⟨a, b, hab⟩
          have hb_mem : b ∈ S \ E := cupChainEnding_right_mem hab
          have hb_cup : CupChainEnding P S m a b := cupChainEnding_mono Finset.sdiff_subset hab
          rw [Finset.mem_sdiff, Finset.mem_filter] at hb_mem
          exact False.elim (hb_mem.2 ⟨hb_mem.1, a, hb_cup⟩)
        · exact Or.inr (hasCap_mono Finset.sdiff_subset hcap)
      · have hE_card : ((m + 1) + k).choose (m + 1) + 1 ≤ E.card := by omega
        rcases erdos_szekeres_cup_cap_theorem_on hmono (m + 1) k E
            (isSeqNonTrilinearOn_mono hES hnontri) hE_card with hcupE | hcapE
        · exact Or.inl (hasCup_mono hES hcupE)
        · rcases hcapE with ⟨b, c, hcap⟩
          have hbE : b ∈ E := capChainStarting_left_mem hcap
          rw [Finset.mem_filter] at hbE
          rcases hbE.2 with ⟨a, hcup⟩
          have hcapS : CapChainStarting P S k b c := capChainStarting_mono hES hcap
          exact cup_end_meets_cap_start_on hmono hnontri hcup hcapS

#print axioms erdos_szekeres_cup_cap_theorem_on

/-- Any $x$-injective `NonTrilinear` finite point set $T \subseteq \mathbb{R}^2$ of size at least
`erdosSzekeresUpper k` ($k \ge 2$) contains a convex $k$-gon. -/
theorem hasConvexNGon_of_x_injOn_and_nonTrilinear {T : Finset ℝ²} {k : ℕ}
    (hk : 2 ≤ k) (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²))
    (hnt : NonTrilinear (T : Set ℝ²)) (hcard : erdosSzekeresUpper k ≤ T.card) :
    HasConvexNGon k (T : Set ℝ²) := by
  have hmono := isXMonotone_xSortedSeq T
  have hnt_seq := isSeqNonTrilinearOn_xSortedSeq hinj hnt
  have hcard_range : (Finset.range T.card).card = T.card := Finset.card_range T.card
  have hbound : ((k - 2) + (k - 2)).choose (k - 2) + 1 ≤ (Finset.range T.card).card := by
    have hsum : (k - 2) + (k - 2) = 2 * k - 4 := by omega
    rw [hsum, hcard_range]
    exact hcard
  have hcupcap := erdos_szekeres_cup_cap_theorem_on hmono (k - 2) (k - 2)
    (Finset.range T.card) hnt_seq hbound
  have hngon := hasConvexNGon_of_hasCup_or_hasCap hmono hk hcupcap
  rwa [image_xSortedSeq_range hinj] at hngon

#print axioms hasConvexNGon_of_x_injOn_and_nonTrilinear

/-- **Unconditional General-Position Erdős–Szekeres Convex $k$-Gon Theorem on $\mathbb{R}^2$**:
For every $k \ge 2$, any `NonTrilinear` finite point set `pts : Finset ℝ²` (without any $x$-coordinate
distinctness hypothesis) of cardinality at least `erdosSzekeresUpper k` contains a convex $k$-gon. -/
theorem hasConvexNGon_of_nonTrilinear_and_card_ge {pts : Finset ℝ²} {k : ℕ}
    (hk : 2 ≤ k) (hnt : NonTrilinear (pts : Set ℝ²))
    (hcard : erdosSzekeresUpper k ≤ pts.card) :
    HasConvexNGon k (pts : Set ℝ²) := by
  let m := goodShearSlope pts
  let T := pts.image (shearPt m)
  have hTcoe : (T : Set ℝ²) = shearPt m '' (pts : Set ℝ²) := Finset.coe_image
  have hTcard : T.card = pts.card :=
    Finset.card_image_of_injective _ (shearPt_injective m)
  have hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²) := by
    intro a ha b hb hab
    rw [hTcoe] at ha hb
    rcases ha with ⟨pa, hpa, rfl⟩
    rcases hb with ⟨pb, hpb, rfl⟩
    have hpab : pa = pb := shearPt_x_injOn_goodShearSlope pts hpa hpb hab
    rw [hpab]
  have hntT : NonTrilinear (T : Set ℝ²) := by
    rw [hTcoe]
    exact nonTrilinear_image_shearPt m hnt
  have hTngon : HasConvexNGon k (T : Set ℝ²) :=
    hasConvexNGon_of_x_injOn_and_nonTrilinear hk hinj hntT (hTcard.symm ▸ hcard)
  rw [hTcoe, hasConvexNGon_image_shearPt_iff] at hTngon
  exact hTngon

#print axioms hasConvexNGon_of_nonTrilinear_and_card_ge

/-- **Unconditional Asymmetric Erdős–Szekeres Convex Polygon Dichotomy on $\mathbb{R}^2$**:
For all $r, s \ge 2$, any `NonTrilinear` finite point set `pts : Finset ℝ²` (without any $x$-coordinate
restriction) of cardinality at least `cupCapBound r s` contains either a convex $r$-gon or a convex $s$-gon. -/
theorem asymmetric_cupCapBound_hasConvexNGon_dichotomy {pts : Finset ℝ²} {r s : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hnt : NonTrilinear (pts : Set ℝ²))
    (hcard : cupCapBound r s ≤ pts.card) :
    HasConvexNGon r (pts : Set ℝ²) ∨ HasConvexNGon s (pts : Set ℝ²) := by
  let m := goodShearSlope pts
  let T := pts.image (shearPt m)
  have hTcoe : (T : Set ℝ²) = shearPt m '' (pts : Set ℝ²) := Finset.coe_image
  have hTcard : T.card = pts.card :=
    Finset.card_image_of_injective _ (shearPt_injective m)
  have hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²) := by
    intro a ha b hb hab
    rw [hTcoe] at ha hb
    rcases ha with ⟨pa, hpa, rfl⟩
    rcases hb with ⟨pb, hpb, rfl⟩
    have hpab : pa = pb := shearPt_x_injOn_goodShearSlope pts hpa hpb hab
    rw [hpab]
  have hntT : NonTrilinear (T : Set ℝ²) := by
    rw [hTcoe]
    exact nonTrilinear_image_shearPt m hnt
  have hmono := isXMonotone_xSortedSeq T
  have hnt_seq := isSeqNonTrilinearOn_xSortedSeq hinj hntT
  have hbound : ((r - 2) + (s - 2)).choose (r - 2) + 1 ≤ (Finset.range T.card).card := by
    have hsum : (r - 2) + (s - 2) = r + s - 4 := by omega
    rw [hsum, Finset.card_range, hTcard]
    exact hcard
  rcases erdos_szekeres_cup_cap_theorem_on hmono (r - 2) (s - 2)
      (Finset.range T.card) hnt_seq hbound with hcup | hcap
  · left
    have hngon := hasConvexNGon_of_hasCup_or_hasCap hmono hr (Or.inl hcup)
    rwa [image_xSortedSeq_range hinj, hTcoe, hasConvexNGon_image_shearPt_iff] at hngon
  · right
    have hngon := hasConvexNGon_of_hasCup_or_hasCap hmono hs (Or.inr hcap)
    rwa [image_xSortedSeq_range hinj, hTcoe, hasConvexNGon_image_shearPt_iff] at hngon

#print axioms asymmetric_cupCapBound_hasConvexNGon_dichotomy

/-- **Unconditional Tóth–Valtr $(k - 1)$-Gon Forcing on General-Position Point Sets**:
For every $k \ge 3$, any `NonTrilinear` finite point set `pts : Finset ℝ²` of cardinality at least
`tothValtrUpper k = (2 * k - 5).choose (k - 2) + 1` contains a convex $(k - 1)$-gon. -/
theorem tothValtr_general_pointset_convexNGon_minus_one {pts : Finset ℝ²} {k : ℕ}
    (hk : 3 ≤ k) (hnt : NonTrilinear (pts : Set ℝ²))
    (hcard : tothValtrUpper k ≤ pts.card) :
    HasConvexNGon (k - 1) (pts : Set ℝ²) := by
  have hk1 : 2 ≤ k - 1 := by omega
  have hk2 : 2 ≤ k := by omega
  have h_asym := (tothValtrUpper_eq_cupCapBound_asymmetric hk).1
  have hcard' : cupCapBound (k - 1) k ≤ pts.card := h_asym ▸ hcard
  rcases asymmetric_cupCapBound_hasConvexNGon_dichotomy hk1 hk2 hnt hcard' with h1 | h2
  · exact h1
  · exact hasConvexNGon_mono_n h2 (by omega)

#print axioms tothValtr_general_pointset_convexNGon_minus_one

/-- **Unconditional Membership of `erdosSzekeresUpper k` in `cardSet k`**:
For every $k \ge 2$, $\binom{2k-4}{k-2} + 1 \in \mathrm{cardSet}\,k$. -/
theorem erdosSzekeresUpper_mem_cardSet {k : ℕ} (hk : 2 ≤ k) :
    erdosSzekeresUpper k ∈ cardSet k := by
  intro pts hcard hnt
  exact hasConvexNGon_of_nonTrilinear_and_card_ge hk hnt (le_of_eq hcard.symm)

#print axioms erdosSzekeresUpper_mem_cardSet

/-- Every `cardSet n` ($n \in \mathbb{N}$) is unconditionally nonempty. -/
theorem nonempty_cardSet_all (n : ℕ) : (cardSet n).Nonempty := by
  rcases le_or_gt n 3 with hn | hn
  · exact ⟨n, self_mem_cardSet_of_le_three hn⟩
  · exact ⟨erdosSzekeresUpper n, erdosSzekeresUpper_mem_cardSet (by omega)⟩

#print axioms nonempty_cardSet_all

/-- **Resolution of the FormalConjectures Solved Target `nonempty_cardSet` (`107.lean`)**:
For all $n \ge 3$, `(cardSet n).Nonempty`. -/
theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty :=
  fun n _ => nonempty_cardSet_all n

#print axioms nonempty_cardSet

/-- Unconditional Erdős–Szekeres upper bound $f(k) \le \binom{2k-4}{k-2} + 1$ for all $k \ge 2$. -/
theorem f_le_erdosSzekeresUpper {k : ℕ} (hk : 2 ≤ k) :
    f k ≤ erdosSzekeresUpper k :=
  f_le_erdosSzekeresUpper_of_mem_cardSet (erdosSzekeresUpper_mem_cardSet hk)

#print axioms f_le_erdosSzekeresUpper

/-- Unconditional trivial lower bound $n \le f(n)$ for all $n \in \mathbb{N}$. -/
theorem le_f_all (n : ℕ) : n ≤ f n :=
  le_f_of_nonempty (nonempty_cardSet_all n)

#print axioms le_f_all

/-- Unconditional monotonicity $f(m) \le f(n)$ whenever $m \le n$. -/
theorem f_mono_all {m n : ℕ} (hle : m ≤ n) : f m ≤ f n :=
  f_mono_of_nonempty hle (nonempty_cardSet_all n)

#print axioms f_mono_all

/-- Unconditional lower and upper bounds $5 \le f(4) \le 7$ (`erdosSzekeresConjectured 4 ≤ f 4 ≤ erdosSzekeresUpper 4`). -/
theorem f_four_bounds_unconditional : 5 ≤ f 4 ∧ f 4 ≤ 7 :=
  ⟨five_le_f_four (nonempty_cardSet_all 4), f_le_erdosSzekeresUpper (by decide : 2 ≤ 4)⟩

#print axioms f_four_bounds_unconditional

/-- Unconditional upper bound $f(5) \le 21$ (`f 5 ≤ erdosSzekeresUpper 5`). -/
theorem f_five_upper_unconditional : f 5 ≤ 21 :=
  f_le_erdosSzekeresUpper (by decide : 2 ≤ 5)

#print axioms f_five_upper_unconditional

/-! ## Section 3: Kalbfleisch–Kalbfleisch–Stanton $(3, 4, 2)$ and $(3, 3, 3)$ Inner-Triangle Wedge-Pigeonhole Pentagon Forcing -/

/-- **Universal Edge-Pair Same-Open-Side 4-Triple Orientation Lemma**:
If $p_1, p_2$ lie on the strictly positive side of the directed edge $a \to b$ and $a, b$ lie on the
strictly positive side of $p_1 \to p_2$, then all 4 ordered triples of $(a, b, p_1, p_2)$ have strictly
positive `lineSide`. -/
theorem kks_edge_pair_same_open_side_all_four_triples_pos {a b p₁ p₂ : ℝ²}
    (habp₁ : 0 < lineSide a b p₁) (habp₂ : 0 < lineSide a b p₂)
    (hp₁₂a : 0 < lineSide p₁ p₂ a) (hp₁₂b : 0 < lineSide p₁ p₂ b) :
    0 < lineSide a b p₁ ∧ 0 < lineSide a b p₂ ∧
    0 < lineSide a p₁ p₂ ∧ 0 < lineSide b p₁ p₂ := by
  refine ⟨habp₁, habp₂, ?_, ?_⟩
  · have h : lineSide a p₁ p₂ = lineSide p₁ p₂ a := by dsimp [lineSide]; ring
    linarith
  · have h : lineSide b p₁ p₂ = lineSide p₁ p₂ b := by dsimp [lineSide]; ring
    linarith

#print axioms kks_edge_pair_same_open_side_all_four_triples_pos

/-- **KKS Positive-Side Edge-Pair Wedge Pentagon Forcing Lemma**:
Whenever $p_1, p_2$ lie on the positive side of $a \to b$ and $a, b$ lie on the positive side of $p_1 \to p_2$,
adjoining any fifth point $v \in P$ in the positive cap wedge over $(a, b, p_1, p_2)$ forces `HasConvexNGon 5 P`. -/
theorem kks_edge_pair_pos_wedge_forces_fiveGon {P : Set ℝ²} {a b p₁ p₂ v : ℝ²}
    (ha : a ∈ P) (hb : b ∈ P) (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (hv : v ∈ P)
    (habp₁ : 0 < lineSide a b p₁) (habp₂ : 0 < lineSide a b p₂)
    (hp₁₂a : 0 < lineSide p₁ p₂ a) (hp₁₂b : 0 < lineSide p₁ p₂ b)
    (hvab : 0 < lineSide a b v) (hvap₁ : 0 < lineSide a p₁ v) (hvap₂ : 0 < lineSide a p₂ v)
    (hvbp₁ : 0 < lineSide b p₁ v) (hvbp₂ : 0 < lineSide b p₂ v) (hvp₁₂ : 0 < lineSide p₁ p₂ v) :
    HasConvexNGon 5 P := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    kks_edge_pair_same_open_side_all_four_triples_pos habp₁ habp₂ hp₁₂a hp₁₂b
  exact kks_quad_cap_wedge_forces_fiveGon ha hb hp₁ hp₂ hv
    h1 h2 h3 h4 hvab hvap₁ hvap₂ hvbp₁ hvbp₂ hvp₁₂

#print axioms kks_edge_pair_pos_wedge_forces_fiveGon

/-- **KKS Negative-Side Edge-Pair Wedge Pentagon Forcing Lemma**:
Whenever $p_1, p_2$ lie on the positive side of $a \to b$ and $a, b$ lie on the strictly negative side
of $p_1 \to p_2$, adjoining any fifth point $v \in P$ in the positive cap wedge over $(a, b, p_2, p_1)$
forces `HasConvexNGon 5 P`. -/
theorem kks_edge_pair_neg_wedge_forces_fiveGon {P : Set ℝ²} {a b p₁ p₂ v : ℝ²}
    (ha : a ∈ P) (hb : b ∈ P) (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (hv : v ∈ P)
    (habp₁ : 0 < lineSide a b p₁) (habp₂ : 0 < lineSide a b p₂)
    (hp₁₂a : lineSide p₁ p₂ a < 0) (hp₁₂b : lineSide p₁ p₂ b < 0)
    (hvab : 0 < lineSide a b v) (hvap₂ : 0 < lineSide a p₂ v) (hvap₁ : 0 < lineSide a p₁ v)
    (hvbp₂ : 0 < lineSide b p₂ v) (hvbp₁ : 0 < lineSide b p₁ v) (hvp₂₁ : 0 < lineSide p₂ p₁ v) :
    HasConvexNGon 5 P := by
  have hp₂₁a : 0 < lineSide p₂ p₁ a := by rw [lineSide_swap_left]; linarith
  have hp₂₁b : 0 < lineSide p₂ p₁ b := by rw [lineSide_swap_left]; linarith
  exact kks_edge_pair_pos_wedge_forces_fiveGon ha hb hp₂ hp₁ hv
    habp₂ habp₁ hp₂₁a hp₂₁b hvab hvap₂ hvap₁ hvbp₂ hvbp₁ hvp₂₁

#print axioms kks_edge_pair_neg_wedge_forces_fiveGon

/-- **Four-Sign Cyclic-Edge or Alternating-Diagonal Dichotomy**:
For any four non-zero real numbers $s_1, s_2, s_3, s_4 \ne 0$, either two cyclic neighbors share the
same strict sign, or the signs strictly alternate around the 4-cycle so both diagonal pairs share
the same strict sign. -/
theorem pigeonhole_four_signs_cyclic_or_diag {s₁ s₂ s₃ s₄ : ℝ}
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h₃ : s₃ ≠ 0) (h₄ : s₄ ≠ 0) :
    ((0 < s₁ ∧ 0 < s₂) ∨ (s₁ < 0 ∧ s₂ < 0)) ∨
    ((0 < s₂ ∧ 0 < s₃) ∨ (s₂ < 0 ∧ s₃ < 0)) ∨
    ((0 < s₃ ∧ 0 < s₄) ∨ (s₃ < 0 ∧ s₄ < 0)) ∨
    ((0 < s₄ ∧ 0 < s₁) ∨ (s₄ < 0 ∧ s₁ < 0)) ∨
    ((0 < s₁ ∧ 0 < s₃ ∧ s₂ < 0 ∧ s₄ < 0) ∨ (s₁ < 0 ∧ s₃ < 0 ∧ 0 < s₂ ∧ 0 < s₄)) := by
  rcases lt_or_gt_of_ne h₁ with h1n | h1p <;>
  rcases lt_or_gt_of_ne h₂ with h2n | h2p <;>
  rcases lt_or_gt_of_ne h₃ with h3n | h3p <;>
  rcases lt_or_gt_of_ne h₄ with h4n | h4p
  · exact Or.inl (Or.inr ⟨h1n, h2n⟩)
  · exact Or.inl (Or.inr ⟨h1n, h2n⟩)
  · exact Or.inl (Or.inr ⟨h1n, h2n⟩)
  · exact Or.inl (Or.inr ⟨h1n, h2n⟩)
  · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨h3n, h4n⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1n, h3n, h2p, h4p⟩))))
  · exact Or.inr (Or.inl (Or.inl ⟨h2p, h3p⟩))
  · exact Or.inr (Or.inl (Or.inl ⟨h2p, h3p⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨h2n, h3n⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨h2n, h3n⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1p, h3p, h2n, h4n⟩))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h3p, h4p⟩)))
  · exact Or.inl (Or.inl ⟨h1p, h2p⟩)
  · exact Or.inl (Or.inl ⟨h1p, h2p⟩)
  · exact Or.inl (Or.inl ⟨h1p, h2p⟩)
  · exact Or.inl (Or.inl ⟨h1p, h2p⟩)

#print axioms pigeonhole_four_signs_cyclic_or_diag

/-- **KKS $(3, 4, 2)$ Middle-4-Gon Inner-Line Convex 4-Gon Dichotomy**:
When the innermost pair $\{p_1, p_2\}$ lies strictly inside the middle 4-gon $(q_1, q_2, q_3, q_4)$,
the line $p_1 \leftrightarrow p_2$ either makes one of the four cyclic edge-pair 4-tuples
$\{q_i, q_{i+1}, p_1, p_2\}$ `ConvexIndep`, or alternates signs across the two diagonals $(q_1, q_3)$ and $(q_2, q_4)$. -/
theorem kks_three_four_two_middle_quad_line_dichotomy {q₁ q₂ q₃ q₄ p₁ p₂ : ℝ²}
    (h12p₁ : 0 < lineSide q₁ q₂ p₁) (h12p₂ : 0 < lineSide q₁ q₂ p₂)
    (h23p₁ : 0 < lineSide q₂ q₃ p₁) (h23p₂ : 0 < lineSide q₂ q₃ p₂)
    (h34p₁ : 0 < lineSide q₃ q₄ p₁) (h34p₂ : 0 < lineSide q₃ q₄ p₂)
    (h41p₁ : 0 < lineSide q₄ q₁ p₁) (h41p₂ : 0 < lineSide q₄ q₁ p₂)
    (hnc1 : ¬ Collinear ℝ ({p₁, p₂, q₁} : Set ℝ²))
    (hnc2 : ¬ Collinear ℝ ({p₁, p₂, q₂} : Set ℝ²))
    (hnc3 : ¬ Collinear ℝ ({p₁, p₂, q₃} : Set ℝ²))
    (hnc4 : ¬ Collinear ℝ ({p₁, p₂, q₄} : Set ℝ²)) :
    ConvexIndep ({q₁, q₂, p₁, p₂} : Set ℝ²) ∨
    ConvexIndep ({q₂, q₃, p₁, p₂} : Set ℝ²) ∨
    ConvexIndep ({q₃, q₄, p₁, p₂} : Set ℝ²) ∨
    ConvexIndep ({q₄, q₁, p₁, p₂} : Set ℝ²) ∨
    ((0 < lineSide p₁ p₂ q₁ ∧ 0 < lineSide p₁ p₂ q₃ ∧
      lineSide p₁ p₂ q₂ < 0 ∧ lineSide p₁ p₂ q₄ < 0) ∨
     (lineSide p₁ p₂ q₁ < 0 ∧ lineSide p₁ p₂ q₃ < 0 ∧
      0 < lineSide p₁ p₂ q₂ ∧ 0 < lineSide p₁ p₂ q₄)) := by
  have hs1 : lineSide p₁ p₂ q₁ ≠ 0 := fun h => hnc1 (collinear_of_lineSide_eq_zero h)
  have hs2 : lineSide p₁ p₂ q₂ ≠ 0 := fun h => hnc2 (collinear_of_lineSide_eq_zero h)
  have hs3 : lineSide p₁ p₂ q₃ ≠ 0 := fun h => hnc3 (collinear_of_lineSide_eq_zero h)
  have hs4 : lineSide p₁ p₂ q₄ ≠ 0 := fun h => hnc4 (collinear_of_lineSide_eq_zero h)
  rcases pigeonhole_four_signs_cyclic_or_diag hs1 hs2 hs3 hs4 with
    h12 | h23 | h34 | h41 | halt
  · exact Or.inl (convexIndep_four_of_same_open_side h12p₁ h12p₂ h12)
  · exact Or.inr (Or.inl (convexIndep_four_of_same_open_side h23p₁ h23p₂ h23))
  · exact Or.inr (Or.inr (Or.inl (convexIndep_four_of_same_open_side h34p₁ h34p₂ h34)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (convexIndep_four_of_same_open_side h41p₁ h41p₂ h41))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr halt)))

#print axioms kks_three_four_two_middle_quad_line_dichotomy

/-- **KKS $(3, 4, 2)$ Wedge-Pigeonhole Pentagon Reduction**:
In the $(3, 4, 2)$ configuration with middle 4-gon $(q_1, q_2, q_3, q_4)$ and innermost pair $(p_1, p_2)$,
`HasConvexNGon 5 P` reduces to the four cyclic same-open-side edge cases and the alternating diagonal case. -/
theorem kks_three_four_two_wedge_pentagon_reduction {P : Set ℝ²} {q₁ q₂ q₃ q₄ p₁ p₂ : ℝ²}
    (hnc1 : ¬ Collinear ℝ ({p₁, p₂, q₁} : Set ℝ²))
    (hnc2 : ¬ Collinear ℝ ({p₁, p₂, q₂} : Set ℝ²))
    (hnc3 : ¬ Collinear ℝ ({p₁, p₂, q₃} : Set ℝ²))
    (hnc4 : ¬ Collinear ℝ ({p₁, p₂, q₄} : Set ℝ²))
    (he12 : ((0 < lineSide p₁ p₂ q₁ ∧ 0 < lineSide p₁ p₂ q₂) ∨
      (lineSide p₁ p₂ q₁ < 0 ∧ lineSide p₁ p₂ q₂ < 0)) → HasConvexNGon 5 P)
    (he23 : ((0 < lineSide p₁ p₂ q₂ ∧ 0 < lineSide p₁ p₂ q₃) ∨
      (lineSide p₁ p₂ q₂ < 0 ∧ lineSide p₁ p₂ q₃ < 0)) → HasConvexNGon 5 P)
    (he34 : ((0 < lineSide p₁ p₂ q₃ ∧ 0 < lineSide p₁ p₂ q₄) ∨
      (lineSide p₁ p₂ q₃ < 0 ∧ lineSide p₁ p₂ q₄ < 0)) → HasConvexNGon 5 P)
    (he41 : ((0 < lineSide p₁ p₂ q₄ ∧ 0 < lineSide p₁ p₂ q₁) ∨
      (lineSide p₁ p₂ q₄ < 0 ∧ lineSide p₁ p₂ q₁ < 0)) → HasConvexNGon 5 P)
    (hdiag : ((0 < lineSide p₁ p₂ q₁ ∧ 0 < lineSide p₁ p₂ q₃ ∧
      lineSide p₁ p₂ q₂ < 0 ∧ lineSide p₁ p₂ q₄ < 0) ∨
     (lineSide p₁ p₂ q₁ < 0 ∧ lineSide p₁ p₂ q₃ < 0 ∧
      0 < lineSide p₁ p₂ q₂ ∧ 0 < lineSide p₁ p₂ q₄)) → HasConvexNGon 5 P) :
    HasConvexNGon 5 P := by
  have hs1 : lineSide p₁ p₂ q₁ ≠ 0 := fun h => hnc1 (collinear_of_lineSide_eq_zero h)
  have hs2 : lineSide p₁ p₂ q₂ ≠ 0 := fun h => hnc2 (collinear_of_lineSide_eq_zero h)
  have hs3 : lineSide p₁ p₂ q₃ ≠ 0 := fun h => hnc3 (collinear_of_lineSide_eq_zero h)
  have hs4 : lineSide p₁ p₂ q₄ ≠ 0 := fun h => hnc4 (collinear_of_lineSide_eq_zero h)
  rcases pigeonhole_four_signs_cyclic_or_diag hs1 hs2 hs3 hs4 with
    h12 | h23 | h34 | h41 | halt
  · exact he12 h12
  · exact he23 h23
  · exact he34 h34
  · exact he41 h41
  · exact hdiag halt

#print axioms kks_three_four_two_wedge_pentagon_reduction

/-- **KKS $(3, 3, 3)$ Exterior Edge-Halfplane Covering Lemma**:
Any point $x \in \mathbb{R}^2$ outside the open interior of $\triangle p_1 p_2 p_3$ and non-collinear
with its three edges lies in at least one of the three open exterior edge half-planes
`0 < lineSide p₂ p₁ x`, `0 < lineSide p₃ p₂ x`, or `0 < lineSide p₁ p₃ x`. -/
theorem kks_triangle_exterior_point_edge_covering {p₁ p₂ p₃ x : ℝ²}
    (hnc12 : ¬ Collinear ℝ ({p₁, p₂, x} : Set ℝ²))
    (hnc23 : ¬ Collinear ℝ ({p₂, p₃, x} : Set ℝ²))
    (hnc31 : ¬ Collinear ℝ ({p₃, p₁, x} : Set ℝ²))
    (hext : ¬ (0 < lineSide p₁ p₂ x ∧ 0 < lineSide p₂ p₃ x ∧ 0 < lineSide p₃ p₁ x)) :
    0 < lineSide p₂ p₁ x ∨ 0 < lineSide p₃ p₂ x ∨ 0 < lineSide p₁ p₃ x := by
  rcases lineSide_pos_or_neg_of_not_collinear hnc12 with h12p | h12n
  · rcases lineSide_pos_or_neg_of_not_collinear hnc23 with h23p | h23n
    · rcases lineSide_pos_or_neg_of_not_collinear hnc31 with h31p | h31n
      · exact False.elim (hext ⟨h12p, h23p, h31p⟩)
      · right; right; rw [lineSide_swap_left]; linarith
    · right; left; rw [lineSide_swap_left]; linarith
  · left; rw [lineSide_swap_left]; linarith

#print axioms kks_triangle_exterior_point_edge_covering

/-- Predicate asserting that at least two of the four elements $x_1, x_2, x_3, x_4$ belong to bucket $E$. -/
def HasPairInBucket {α : Type*} (E : α → Prop) (x₁ x₂ x₃ x₄ : α) : Prop :=
  (E x₁ ∧ E x₂) ∨ (E x₁ ∧ E x₃) ∨ (E x₁ ∧ E x₄) ∨
  (E x₂ ∧ E x₃) ∨ (E x₂ ∧ E x₄) ∨ (E x₃ ∧ E x₄)

theorem hasPairInBucket_elim {α : Type*} {E : α → Prop} {x₁ x₂ x₃ x₄ : α} {Q : Prop}
    (h : HasPairInBucket E x₁ x₂ x₃ x₄)
    (hgoal : ∀ u v, u ∈ ({x₁, x₂, x₃, x₄} : Set α) → v ∈ ({x₁, x₂, x₃, x₄} : Set α) →
      E u → E v → Q) : Q := by
  have hx1 : x₁ ∈ ({x₁, x₂, x₃, x₄} : Set α) := by simp
  have hx2 : x₂ ∈ ({x₁, x₂, x₃, x₄} : Set α) := by simp
  have hx3 : x₃ ∈ ({x₁, x₂, x₃, x₄} : Set α) := by simp
  have hx4 : x₄ ∈ ({x₁, x₂, x₃, x₄} : Set α) := by simp
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hgoal x₁ x₂ hx1 hx2 ha hb
  · exact hgoal x₁ x₃ hx1 hx3 ha hb
  · exact hgoal x₁ x₄ hx1 hx4 ha hb
  · exact hgoal x₂ x₃ hx2 hx3 ha hb
  · exact hgoal x₂ x₄ hx2 hx4 ha hb
  · exact hgoal x₃ x₄ hx3 hx4 ha hb

#print axioms hasPairInBucket_elim

/-- **KKS $(3, 3, 3)$ Four-Exterior-Point Three-Edge Pigeonhole Theorem**:
Whenever four exterior points $x_1, x_2, x_3, x_4$ are covered by three edge half-planes $E_1, E_2, E_3$,
at least one of the three half-planes contains a pair from $\{x_1, x_2, x_3, x_4\}$. -/
theorem kks_four_exterior_points_edge_pigeonhole {E₁ E₂ E₃ : ℝ² → Prop} {x₁ x₂ x₃ x₄ : ℝ²}
    (h₁ : E₁ x₁ ∨ E₂ x₁ ∨ E₃ x₁)
    (h₂ : E₁ x₂ ∨ E₂ x₂ ∨ E₃ x₂)
    (h₃ : E₁ x₃ ∨ E₂ x₃ ∨ E₃ x₃)
    (h₄ : E₁ x₄ ∨ E₂ x₄ ∨ E₃ x₄) :
    HasPairInBucket E₁ x₁ x₂ x₃ x₄ ∨
    HasPairInBucket E₂ x₁ x₂ x₃ x₄ ∨
    HasPairInBucket E₃ x₁ x₂ x₃ x₄ := by
  rcases h₁ with h1a | h1b | h1c
  · rcases h₂ with h2a | h2b | h2c
    · exact Or.inl (Or.inl ⟨h1a, h2a⟩)
    · rcases h₃ with h3a | h3b | h3c
      · exact Or.inl (Or.inr (Or.inl ⟨h1a, h3a⟩))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2b, h3b⟩)))))
      · rcases h₄ with h4a | h4b | h4c
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h1a, h4a⟩)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2b, h4b⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3c, h4c⟩))))))
    · rcases h₃ with h3a | h3b | h3c
      · exact Or.inl (Or.inr (Or.inl ⟨h1a, h3a⟩))
      · rcases h₄ with h4a | h4b | h4c
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h1a, h4a⟩)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3b, h4b⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2c, h4c⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2c, h3c⟩)))))
  · rcases h₂ with h2a | h2b | h2c
    · rcases h₃ with h3a | h3b | h3c
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2a, h3a⟩))))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h1b, h3b⟩)))
      · rcases h₄ with h4a | h4b | h4c
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2a, h4a⟩)))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1b, h4b⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3c, h4c⟩))))))
    · exact Or.inr (Or.inl (Or.inl ⟨h1b, h2b⟩))
    · rcases h₃ with h3a | h3b | h3c
      · rcases h₄ with h4a | h4b | h4c
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3a, h4a⟩)))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1b, h4b⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2c, h4c⟩))))))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h1b, h3b⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2c, h3c⟩)))))
  · rcases h₂ with h2a | h2b | h2c
    · rcases h₃ with h3a | h3b | h3c
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2a, h3a⟩))))
      · rcases h₄ with h4a | h4b | h4c
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2a, h4a⟩)))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3b, h4b⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1c, h4c⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1c, h3c⟩)))
    · rcases h₃ with h3a | h3b | h3c
      · rcases h₄ with h4a | h4b | h4c
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3a, h4a⟩)))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2b, h4b⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1c, h4c⟩))))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2b, h3b⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1c, h3c⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h1c, h2c⟩))

#print axioms kks_four_exterior_points_edge_pigeonhole

/-- **KKS $(3, 3, 3)$ Same-Edge Exterior Pair Convex 4-Gon Lemma**:
If two exterior points $u, v$ lie in the open exterior half-plane of $p_2 \to p_1$ and $p_2, p_1$
lie on the same open side of $u \leftrightarrow v$, then $\{p_2, p_1, u, v\}$ is `ConvexIndep`. -/
theorem kks_three_three_three_edge_pair_convexIndep_four {p₁ p₂ u v : ℝ²}
    (hu : 0 < lineSide p₂ p₁ u) (hv : 0 < lineSide p₂ p₁ v)
    (hside : (0 < lineSide u v p₂ ∧ 0 < lineSide u v p₁) ∨
      (lineSide u v p₂ < 0 ∧ lineSide u v p₁ < 0)) :
    ConvexIndep ({p₂, p₁, u, v} : Set ℝ²) :=
  convexIndep_four_of_same_open_side hu hv hside

#print axioms kks_three_three_three_edge_pair_convexIndep_four

/-- **KKS $(3, 3, 3)$ Wedge-Pigeonhole Pentagon Reduction**:
In the $(3, 3, 3)$ configuration with innermost triangle $(p_1, p_2, p_3)$ and any four exterior
vertices $x_1, x_2, x_3, x_4 \in H \cup H_2$, `HasConvexNGon 5 P` reduces to pentagon forcing for
pairs $u, v$ lying in the same open exterior edge half-plane $E_{12}, E_{23}$, or $E_{31}$. -/
theorem kks_three_three_three_wedge_pentagon_reduction {P : Set ℝ²} {p₁ p₂ p₃ x₁ x₂ x₃ x₄ : ℝ²}
    (h₁ : 0 < lineSide p₂ p₁ x₁ ∨ 0 < lineSide p₃ p₂ x₁ ∨ 0 < lineSide p₁ p₃ x₁)
    (h₂ : 0 < lineSide p₂ p₁ x₂ ∨ 0 < lineSide p₃ p₂ x₂ ∨ 0 < lineSide p₁ p₃ x₂)
    (h₃ : 0 < lineSide p₂ p₁ x₃ ∨ 0 < lineSide p₃ p₂ x₃ ∨ 0 < lineSide p₁ p₃ x₃)
    (h₄ : 0 < lineSide p₂ p₁ x₄ ∨ 0 < lineSide p₃ p₂ x₄ ∨ 0 < lineSide p₁ p₃ x₄)
    (he₁₂ : ∀ u v, u ∈ ({x₁, x₂, x₃, x₄} : Set ℝ²) → v ∈ ({x₁, x₂, x₃, x₄} : Set ℝ²) →
      0 < lineSide p₂ p₁ u → 0 < lineSide p₂ p₁ v → HasConvexNGon 5 P)
    (he₂₃ : ∀ u v, u ∈ ({x₁, x₂, x₃, x₄} : Set ℝ²) → v ∈ ({x₁, x₂, x₃, x₄} : Set ℝ²) →
      0 < lineSide p₃ p₂ u → 0 < lineSide p₃ p₂ v → HasConvexNGon 5 P)
    (he₃₁ : ∀ u v, u ∈ ({x₁, x₂, x₃, x₄} : Set ℝ²) → v ∈ ({x₁, x₂, x₃, x₄} : Set ℝ²) →
      0 < lineSide p₁ p₃ u → 0 < lineSide p₁ p₃ v → HasConvexNGon 5 P) :
    HasConvexNGon 5 P := by
  rcases kks_four_exterior_points_edge_pigeonhole
      (E₁ := fun x => 0 < lineSide p₂ p₁ x)
      (E₂ := fun x => 0 < lineSide p₃ p₂ x)
      (E₃ := fun x => 0 < lineSide p₁ p₃ x)
      h₁ h₂ h₃ h₄ with hE1 | hE2 | hE3
  · exact hasPairInBucket_elim hE1 he₁₂
  · exact hasPairInBucket_elim hE2 he₂₃
  · exact hasPairInBucket_elim hE3 he₃₁

#print axioms kks_three_three_three_wedge_pentagon_reduction

/-- **KKS $(3, 6)$-Layer Complete Pentagon Reduction**:
For any 9-point set $P$ with outer triangle $H \subseteq P$ ($|H| = 3$) and inner sub-hull
$H_2 \subseteq P \setminus H$ ($3 \le |H_2|$, `ConvexIndep H₂`), `HasConvexNGon 5 (P : Set ℝ²)`
holds whenever the two sub-cases $(3, 4, 2)$ and $(3, 3, 3)$ force a convex pentagon. -/
theorem kks_three_six_layer_complete_reduction {P H H₂ : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH3 : H.card = 3)
    (hH₂ : H₂ ⊆ P \ H) (hH₂3 : 3 ≤ H₂.card) (hconv₂ : ConvexIndep (H₂ : Set ℝ²))
    (h342 : H₂.card = 4 → ((P \ H) \ H₂).card = 2 → HasConvexNGon 5 (P : Set ℝ²))
    (h333 : H₂.card = 3 → ((P \ H) \ H₂).card = 3 → HasConvexNGon 5 (P : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) := by
  rcases kks_nine_point_layer_three_six_subhull_dichotomy hP hHP hH3 hH₂ hH₂3 hconv₂ with
    h5 | ⟨h4, h2⟩ | ⟨h3, h3'⟩
  · exact h5
  · exact h342 h4 h2
  · exact h333 h3 h3'

#print axioms kks_three_six_layer_complete_reduction

/-! ## Section 4: Positive and Negative Controls -/

/-- **Negative Control 1 (Raw $x$-Coordinate Injectivity Fails on Axis-Aligned Convex 4-Gons)**:
The convex-independent inner square `{sqPP, sqNP, sqNN, sqPN}` does NOT have injective $x$-coordinates
before horizontal shearing, because `sqPP = (1, 1)` and `sqPN = (1, -1)` share $x = 1$. -/
theorem not_injOn_x_innerSquare :
    ¬ Set.InjOn (fun p : ℝ² => p 0) ({sqPP, sqNP, sqNN, sqPN} : Set ℝ²) := by
  intro hinj
  have hmem1 : sqPP ∈ ({sqPP, sqNP, sqNN, sqPN} : Set ℝ²) := by simp
  have hmem2 : sqPN ∈ ({sqPP, sqNP, sqNN, sqPN} : Set ℝ²) := by simp
  have hx : sqPP 0 = sqPN 0 := by simp [sqPP, sqPN]
  have heq : sqPP = sqPN := hinj hmem1 hmem2 hx
  have hy : sqPP 1 = sqPN 1 := congrArg (fun p : ℝ² => p 1) heq
  simp [sqPP, sqPN] at hy
  linarith

#print axioms not_injOn_x_innerSquare

/-- **Positive Control 1 (Horizontal Shear Preserves Convex Independence of `innerSquare`)**:
Applying `shearPt m` for any $m \in \mathbb{R}$ to `{sqPP, sqNP, sqNN, sqPN}` preserves `ConvexIndep`. -/
theorem innerSquare_shearPt_convexIndep (m : ℝ) :
    ConvexIndep (shearPt m '' ({sqPP, sqNP, sqNN, sqPN} : Set ℝ²)) :=
  convexIndep_image_shearPt m innerSquare_convexIndep

#print axioms innerSquare_shearPt_convexIndep

/-- **Negative Control 2 (Collinear Vertical Triples Remain Collinear Under Every Horizontal Shear)**:
For any $m \in \mathbb{R}$, the vertical collinear triple `(0, 0), (0, 1), (0, 2)` maps under `shearPt m`
to `(0, 0), (m, 1), (2m, 2)`, which remains `Collinear ℝ` (confirming that `NonTrilinear` cannot be
omitted in `hasConvexNGon_of_nonTrilinear_and_card_ge`). -/
theorem collinear_shearPt_vertical_triple (m : ℝ) :
    Collinear ℝ ({shearPt m (mkPt 0 0), shearPt m (mkPt 0 1), shearPt m (mkPt 0 2)} : Set ℝ²) := by
  apply collinear_of_lineSide_eq_zero
  rw [lineSide_shearPt]
  dsimp [lineSide]
  simp only [mkPt_zero, mkPt_one]
  ring

#print axioms collinear_shearPt_vertical_triple

end Erdos107
