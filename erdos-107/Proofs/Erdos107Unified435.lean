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

public import Mathlib
@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators


open Filter
open EuclideanGeometry
open Set

namespace Erdos107

/-- Two-dimensional Euclidean plane $\mathbb{R}^2$. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

scoped notation "ℝ²" => Plane

/-- A point set $A \subseteq \mathbb{R}^2$ is non-trilinear if no three distinct points of $A$ are collinear. -/
def NonTrilinear (A : Set ℝ²) : Prop :=
  ∀ ⦃x : ℝ²⦄, x ∈ A → ∀ ⦃y : ℝ²⦄, y ∈ A → ∀ ⦃z : ℝ²⦄, z ∈ A →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set ℝ²)

theorem nonTrilinear_mono {P Q : Set ℝ²} (hPQ : P ⊆ Q) (hQ : NonTrilinear Q) :
    NonTrilinear P :=
  fun _ hx _ hy _ hz hxy hyz hxz => hQ (hPQ hx) (hPQ hy) (hPQ hz) hxy hyz hxz

#print axioms nonTrilinear_mono

/-- A point set $S \subseteq \mathbb{R}^2$ is convex independent if no point lies in the convex hull of the remaining points. -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- The point set $P \subseteq \mathbb{R}^2$ contains the vertices of a convex $n$-gon. -/
def HasConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ (S : Set ℝ²) ⊆ P ∧ ConvexIndep (S : Set ℝ²)

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) : Set ℕ :=
  { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) → HasConvexNGon n pts }

/-- The minimal number $f(n)$ of points in general position guaranteed to contain a convex $n$-gon. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/-- Coordinate constructor for a point $(x, y) \in \mathbb{R}^2$. -/
def mkPt (x y : ℝ) : ℝ² :=
  EuclideanSpace.single (0 : Fin 2) x + EuclideanSpace.single (1 : Fin 2) y

@[simp]
theorem mkPt_zero (x y : ℝ) : mkPt x y 0 = x := by
  simp [mkPt]

#print axioms mkPt_zero

@[simp]
theorem mkPt_one (x y : ℝ) : mkPt x y 1 = y := by
  simp [mkPt]

#print axioms mkPt_one

theorem mkPt_ext {x₁ y₁ x₂ y₂ : ℝ} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    mkPt x₁ y₁ = mkPt x₂ y₂ := by
  rw [hx, hy]

#print axioms mkPt_ext

/-- Collinear triples in $\mathbb{R}^2$ have vanishing 2D cross product. -/
theorem cross_eq_zero_of_collinear {a b c : ℝ²} (h : Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  rw [collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set ℝ²))] at h
  rcases h with ⟨v, hv⟩
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  have hb0 : b 0 = rb * v 0 + a 0 := by
    have := congrArg (fun w : ℝ² => w 0) hrb
    simpa using this
  have hb1 : b 1 = rb * v 1 + a 1 := by
    have := congrArg (fun w : ℝ² => w 1) hrb
    simpa using this
  have hc0 : c 0 = rc * v 0 + a 0 := by
    have := congrArg (fun w : ℝ² => w 0) hrc
    simpa using this
  have hc1 : c 1 = rc * v 1 + a 1 := by
    have := congrArg (fun w : ℝ² => w 1) hrc
    simpa using this
  rw [hb0, hb1, hc0, hc1]
  ring

#print axioms cross_eq_zero_of_collinear

/-- Non-vanishing 2D cross product certifies non-collinearity of three points in $\mathbb{R}^2$. -/
theorem not_collinear_of_cross_ne_zero {a b c : ℝ²}
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
  fun hcoll => h (cross_eq_zero_of_collinear hcoll)

#print axioms not_collinear_of_cross_ne_zero

/-- Integer points on the parabola $(i, i^2)$ in $\mathbb{R}^2$. -/
def parabolaPt (i : ℕ) : ℝ² :=
  mkPt (i : ℝ) ((i : ℝ) ^ 2)

theorem parabolaPt_injective : Function.Injective parabolaPt := by
  intro i j hij
  have h0 := congrArg (fun w : ℝ² => w 0) hij
  simp [parabolaPt] at h0
  exact h0

#print axioms parabolaPt_injective

/-- The canonical $N$-point parabola configuration in general position. -/
def parabolaFinset (N : ℕ) : Finset ℝ² :=
  (Finset.range N).image parabolaPt

theorem parabolaFinset_card (N : ℕ) : (parabolaFinset N).card = N := by
  simp [parabolaFinset, Finset.card_image_of_injOn parabolaPt_injective.injOn]

#print axioms parabolaFinset_card

/-- Every finite subset of the integer parabola is in general position (`NonTrilinear`). -/
theorem parabolaFinset_nonTrilinear (N : ℕ) :
    NonTrilinear ((parabolaFinset N : Finset ℝ²) : Set ℝ²) := by
  intro a ha b hb c hc hab hbc hac hcoll
  simp only [parabolaFinset, Finset.coe_image, Set.mem_image] at ha hb hc
  rcases ha with ⟨i, _, rfl⟩
  rcases hb with ⟨j, _, rfl⟩
  rcases hc with ⟨k, _, rfl⟩
  have hij : (j : ℝ) - (i : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast fun h : j = i => hab (congrArg parabolaPt h.symm))
  have hjk : (k : ℝ) - (j : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast fun h : k = j => hbc (congrArg parabolaPt h.symm))
  have hik : (k : ℝ) - (i : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast fun h : k = i => hac (congrArg parabolaPt h.symm))
  have hcross := cross_eq_zero_of_collinear hcoll
  simp only [parabolaPt, mkPt_zero, mkPt_one] at hcross
  have hfac : ((j : ℝ) - i) * ((k : ℝ) ^ 2 - (i : ℝ) ^ 2) -
      ((j : ℝ) ^ 2 - (i : ℝ) ^ 2) * ((k : ℝ) - i) =
      ((j : ℝ) - i) * ((k : ℝ) - i) * ((k : ℝ) - j) := by ring
  rw [hfac] at hcross
  exact mul_ne_zero (mul_ne_zero hij hik) hjk hcross

#print axioms parabolaFinset_nonTrilinear

/-- Any $N \in \text{cardSet}(n)$ satisfies $n \le N$. -/
theorem le_of_mem_cardSet {n N : ℕ} (hN : N ∈ cardSet n) : n ≤ N := by
  obtain ⟨S, hScard, hSsub, _⟩ :=
    hN (parabolaFinset N) (parabolaFinset_card N) (parabolaFinset_nonTrilinear N)
  have hle : S.card ≤ (parabolaFinset N).card :=
    Finset.card_le_card (Finset.coe_subset.mp hSsub)
  have hNcard := parabolaFinset_card N
  omega

#print axioms le_of_mem_cardSet

/-- Whenever $\text{cardSet}(n)$ is nonempty, $n \le f(n)$. -/
theorem le_f_of_nonempty {n : ℕ} (hne : (cardSet n).Nonempty) : n ≤ f n :=
  le_csInf hne fun _ hN => le_of_mem_cardSet hN

#print axioms le_f_of_nonempty

/-- Convex independence is hereditary under subset inclusion. -/
theorem convexIndep_mono {S T : Set ℝ²} (hST : S ⊆ T) (hT : ConvexIndep T) :
    ConvexIndep S := by
  intro a ha hmem
  exact hT a (hST ha) (convexHull_mono (Set.diff_subset_diff_left hST) hmem)

#print axioms convexIndep_mono

/-- Containing a convex $n$-gon is monotone decreasing in $n$. -/
theorem hasConvexNGon_mono_n {n₁ n₂ : ℕ} {pts : Set ℝ²}
    (h : HasConvexNGon n₂ pts) (hle : n₁ ≤ n₂) : HasConvexNGon n₁ pts := by
  rcases h with ⟨S₂, hcard₂, hsub₂, hconv₂⟩
  obtain ⟨S₁, hS₁sub, hcard₁⟩ := Finset.exists_subset_card_eq (hle.trans_eq hcard₂.symm)
  have hcoe : (S₁ : Set ℝ²) ⊆ (S₂ : Set ℝ²) := Finset.coe_subset.mpr hS₁sub
  exact ⟨S₁, hcard₁, hcoe.trans hsub₂, convexIndep_mono hcoe hconv₂⟩

#print axioms hasConvexNGon_mono_n

/-- Containing a convex $n$-gon is monotone increasing in the ambient point set. -/
theorem hasConvexNGon_mono_pts {n : ℕ} {P Q : Set ℝ²}
    (h : HasConvexNGon n P) (hPQ : P ⊆ Q) : HasConvexNGon n Q := by
  rcases h with ⟨S, hcard, hsub, hconv⟩
  exact ⟨S, hcard, hsub.trans hPQ, hconv⟩

#print axioms hasConvexNGon_mono_pts

/-- Upward closure of `cardSet n`: if $N_1 \le N_2$ and $N_1 \in \text{cardSet}(n)$, then $N_2 \in \text{cardSet}(n)$. -/
theorem cardSet_upward_closed {n N₁ N₂ : ℕ}
    (hle : N₁ ≤ N₂) (hN₁ : N₁ ∈ cardSet n) : N₂ ∈ cardSet n := by
  intro pts hcard hnontri
  obtain ⟨pts₁, hsub, hcard₁⟩ := Finset.exists_subset_card_eq (hle.trans_eq hcard.symm)
  have hcoe : (pts₁ : Set ℝ²) ⊆ (pts : Set ℝ²) := Finset.coe_subset.mpr hsub
  have hnontri₁ : NonTrilinear (pts₁ : Set ℝ²) := nonTrilinear_mono hcoe hnontri
  exact hasConvexNGon_mono_pts (hN₁ pts₁ hcard₁ hnontri₁) hcoe

#print axioms cardSet_upward_closed

/-- Antitonicity of `cardSet` in $n$: if $n_1 \le n_2$, then $\text{cardSet}(n_2) \subseteq \text{cardSet}(n_1)$. -/
theorem cardSet_antitone_n {n₁ n₂ N : ℕ}
    (hle : n₁ ≤ n₂) (hN : N ∈ cardSet n₂) : N ∈ cardSet n₁ := by
  intro pts hcard hnontri
  exact hasConvexNGon_mono_n (hN pts hcard hnontri) hle

#print axioms cardSet_antitone_n

/-- Monotonicity of $f$ under nonemptiness of the upper `cardSet`. -/
theorem f_mono_of_nonempty {n₁ n₂ : ℕ}
    (hle : n₁ ≤ n₂) (hne : (cardSet n₂).Nonempty) : f n₁ ≤ f n₂ := by
  refine le_csInf hne fun N hN => ?_
  exact Nat.sInf_le (cardSet_antitone_n hle hN)

#print axioms f_mono_of_nonempty

/-- Every point set of cardinality at most $2$ is convex independent. -/
theorem convexIndep_of_card_le_two {S : Finset ℝ²} (hcard : S.card ≤ 2) :
    ConvexIndep (S : Set ℝ²) := by
  intro x hx hmem
  have hsub : ((S : Set ℝ²) \ {x}) = ((S.erase x : Finset ℝ²) : Set ℝ²) := by
    ext y
    simp [Finset.mem_erase, and_comm]
  rw [hsub] at hmem
  have herase : (S.erase x).card ≤ 1 := by
    have hxS : x ∈ S := Finset.mem_coe.mp hx
    have := Finset.card_erase_of_mem hxS
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp herase with h0 | h1
  · rw [Finset.card_eq_zero.mp h0] at hmem
    simp at hmem
  · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
    have hy_ne : x ≠ y := by
      intro hxy
      subst hxy
      have hmem_erase : x ∈ S.erase x := hy ▸ Finset.mem_singleton_self x
      simp at hmem_erase
    rw [hy] at hmem
    simp [convexHull_singleton] at hmem
    exact hy_ne hmem

#print axioms convexIndep_of_card_le_two

/-- Three distinct non-collinear points in $\mathbb{R}^2$ form a convex-independent set. -/
theorem convexIndep_triple_of_not_collinear {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    ConvexIndep ({a, b, c} : Set ℝ²) := by
  intro x hx hmem
  apply hcoll
  have hx_aff : x ∈ affineSpan ℝ (({a, b, c} : Set ℝ²) \ {x}) :=
    convexHull_subset_affineSpan _ hmem
  rw [show ({a, b, c} : Set ℝ²) = insert x (({a, b, c} : Set ℝ²) \ {x}) from
        (Set.insert_sdiff_self_of_mem hx).symm,
      collinear_insert_iff_of_mem_affineSpan hx_aff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show ({x, b, c} : Set ℝ²) \ {x} = ({b, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ b c
  · rw [show ({a, x, c} : Set ℝ²) \ {x} = ({a, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a c
  · rw [show ({a, b, x} : Set ℝ²) \ {x} = ({a, b} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a b

#print axioms convexIndep_triple_of_not_collinear

/-- For $n \le 3$, $n \in \text{cardSet}(n)$. -/
theorem self_mem_cardSet_of_le_three {n : ℕ} (hn : n ≤ 3) : n ∈ cardSet n := by
  intro pts hpts hnontri
  rcases le_or_gt n 2 with hn2 | hn3
  · exact ⟨pts, hpts, subset_refl _, convexIndep_of_card_le_two (hpts ▸ hn2)⟩
  · have hn_eq : n = 3 := by omega
    subst hn_eq
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_⟩
    have hcoerce : (({a, b, c} : Finset ℝ²) : Set ℝ²) = ({a, b, c} : Set ℝ²) := by simp
    have hmem : ∀ {y : ℝ²}, y ∈ ({a, b, c} : Set ℝ²) →
        y ∈ (({a, b, c} : Finset ℝ²) : Set ℝ²) := fun h => hcoerce ▸ h
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
      hnontri (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) hab hbc hac
    rw [hcoerce]
    exact convexIndep_triple_of_not_collinear hab hac hbc hnc

#print axioms self_mem_cardSet_of_le_three

/-- For every $n \le 3$, $f(n) = n$. -/
theorem f_eq_self_of_le_three {n : ℕ} (hn : n ≤ 3) : f n = n := by
  have hmem := self_mem_cardSet_of_le_three hn
  exact le_antisymm (Nat.sInf_le hmem) (le_f_of_nonempty ⟨n, hmem⟩)

#print axioms f_eq_self_of_le_three

theorem f_zero_eq : f 0 = 0 :=
  f_eq_self_of_le_three (by decide)

#print axioms f_zero_eq

theorem f_one_eq : f 1 = 1 :=
  f_eq_self_of_le_three (by decide)

#print axioms f_one_eq

theorem f_two_eq : f 2 = 2 :=
  f_eq_self_of_le_three (by decide)

#print axioms f_two_eq

theorem f_three_eq : f 3 = 3 :=
  f_eq_self_of_le_three (by decide)

#print axioms f_three_eq


/-! ## Happy-ending small cases and cup–cap bounds -/

/-!
# Happy Ending Small Cases and Erdős–Szekeres Cup–Cap Bounds (Problem #107)

This module establishes:
1. **Explicit 4-point general-position non-convex configuration**
   $\{(0,0), (3,0), (0,3), (1,1)\}$, where $(1,1) = \frac{1}{3}(0,0) + \frac{1}{3}(3,0) + \frac{1}{3}(0,3)$
   lies in the convex hull of the outer triangle while no three points are collinear.
   This proves $4 \notin \text{cardSet}(4)$ and hence $5 \le f(4)$ whenever $\text{cardSet}(4)$ is nonempty.
2. **Slope dichotomy on $x$-monotone general-position point sequences**, proving that any three
   indices $i < j < k$ determine either a strict cup turn (`slopeLt`) or a strict cap turn (`slopeGt`).
3. **Combinatorial Erdős–Szekeres cup–cap theorem and recursion**:
   defining $g(r, s) = \binom{r+s-4}{r-2} + 1$, proving its boundary identities, symmetry, and
   Pascal recurrence $g(r+1, s+1) + 1 = g(r, s+1) + g(r+1, s)$, and proving by endpoint-filtering
   pigeonhole induction that any $x$-monotone non-trilinear set of size at least $\binom{m+k}{m} + 1$
   contains either an $(m+2)$-cup or a $(k+2)$-cap.
4. **Universal binomial-vs-exponential bound comparison**:
   proving $2^{n-2} + 1 \le \binom{2n-4}{n-2} + 1$ for all $n \in \mathbb{N}$, equality at $n = 3$
   with $f(3) = 3 = 2^{3-2} + 1 = \binom{2\cdot 3 - 4}{3 - 2} + 1$, and strict inequality
   $2^{n-2} + 1 < \binom{2n-4}{n-2} + 1$ for all $n \ge 4$.
-/

/-! ## Section 1: Explicit 4-Point Non-Convex Configuration and $5 \le f(4)$ -/

/-- Origin vertex $(0, 0)$ of the outer triangle. -/
def ptO : ℝ² := mkPt 0 0

/-- Right vertex $(3, 0)$ of the outer triangle. -/
def ptA : ℝ² := mkPt 3 0

/-- Top vertex $(0, 3)$ of the outer triangle. -/
def ptB : ℝ² := mkPt 0 3

/-- Interior centroid $(1, 1)$ of the outer triangle. -/
def ptC : ℝ² := mkPt 1 1

/-- The 4-point Esther Klein witness $\{(0,0), (3,0), (0,3), (1,1)\}$ in general position
forming a triangle with an interior point. -/
def kleinFourPts : Finset ℝ² := {ptO, ptA, ptB, ptC}

theorem ptO_ne_ptA : ptO ≠ ptA := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptO, ptA] at h0

#print axioms ptO_ne_ptA

theorem ptO_ne_ptB : ptO ≠ ptB := by
  intro h
  have h1 := congrArg (fun w : ℝ² => w 1) h
  simp [ptO, ptB] at h1

#print axioms ptO_ne_ptB

theorem ptO_ne_ptC : ptO ≠ ptC := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptO, ptC] at h0

#print axioms ptO_ne_ptC

theorem ptA_ne_ptB : ptA ≠ ptB := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptA, ptB] at h0

#print axioms ptA_ne_ptB

theorem ptA_ne_ptC : ptA ≠ ptC := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptA, ptC] at h0

#print axioms ptA_ne_ptC

theorem ptB_ne_ptC : ptB ≠ ptC := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptB, ptC] at h0

#print axioms ptB_ne_ptC

theorem kleinFourPts_card : kleinFourPts.card = 4 := by
  simp [kleinFourPts, ptO_ne_ptA, ptO_ne_ptB, ptO_ne_ptC, ptA_ne_ptB, ptA_ne_ptC, ptB_ne_ptC]

#print axioms kleinFourPts_card

/-- Exact barycentric representation of $(1, 1)$ as a convex combination of $(0, 0), (3, 0), (0, 3)$. -/
theorem ptC_eq_barycentric :
    ptC = (1 / 3 : ℝ) • ptO + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • ptA + (1 / 2 : ℝ) • ptB) := by
  ext i
  fin_cases i <;> simp [ptO, ptA, ptB, ptC, mkPt] <;> norm_num

#print axioms ptC_eq_barycentric

/-- The centroid $(1, 1)$ lies in the convex hull of the three outer vertices. -/
theorem ptC_mem_convexHull_triangle :
    ptC ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) := by
  have hconv : Convex ℝ (convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²)) :=
    convex_convexHull ℝ _
  have hO : ptO ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hA : ptA ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hB : ptB ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hAB : (1 / 2 : ℝ) • ptA + (1 / 2 : ℝ) • ptB ∈
      convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    hconv hA hB (by norm_num) (by norm_num) (by norm_num)
  rw [ptC_eq_barycentric]
  exact hconv hO hAB (by norm_num) (by norm_num) (by norm_num)

#print axioms ptC_mem_convexHull_triangle

/-- The 4-point configuration `kleinFourPts` is not convex independent. -/
theorem not_convexIndep_kleinFourPts :
    ¬ ConvexIndep (kleinFourPts : Set ℝ²) := by
  intro hci
  have hC : ptC ∈ (kleinFourPts : Set ℝ²) := by simp [kleinFourPts]
  refine hci ptC hC (convexHull_mono ?_ ptC_mem_convexHull_triangle)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · simp [kleinFourPts, ptO_ne_ptC]
  · simp [kleinFourPts, ptA_ne_ptC]
  · simp [kleinFourPts, ptB_ne_ptC]

#print axioms not_convexIndep_kleinFourPts

/-- No three points of `kleinFourPts` are collinear. -/
theorem kleinFourPts_nonTrilinear :
    NonTrilinear (kleinFourPts : Set ℝ²) := by
  intro x hx y hy z hz hxy hyz hxz
  simp only [kleinFourPts, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hxy rfl)
    | exact False.elim (hyz rfl)
    | exact False.elim (hxz rfl)
    | (apply not_collinear_of_cross_ne_zero; norm_num [ptO, ptA, ptB, ptC, mkPt_zero, mkPt_one])

#print axioms kleinFourPts_nonTrilinear

/-- $4 \notin \text{cardSet}(4)$: four points in general position need not form a convex quadrilateral. -/
theorem four_not_mem_cardSet_four : (4 : ℕ) ∉ cardSet 4 := by
  intro h4
  obtain ⟨S, hScard, hSsub, hSconv⟩ :=
    h4 kleinFourPts kleinFourPts_card kleinFourPts_nonTrilinear
  have hkcard := kleinFourPts_card
  have hSeq : S = kleinFourPts :=
    Finset.eq_of_subset_of_card_le (Finset.coe_subset.mp hSsub) (by omega)
  subst hSeq
  exact not_convexIndep_kleinFourPts hSconv

#print axioms four_not_mem_cardSet_four

/-- Every member of $\text{cardSet}(4)$ is at least $5$. -/
theorem five_le_of_mem_cardSet_four {N : ℕ} (hN : N ∈ cardSet 4) : 5 ≤ N := by
  have h4le : 4 ≤ N := le_of_mem_cardSet hN
  have hne4 : N ≠ 4 := fun h => four_not_mem_cardSet_four (h ▸ hN)
  omega

#print axioms five_le_of_mem_cardSet_four

/-- Lower bound $5 \le f(4)$ (i.e. $2^{4-2} + 1 \le f(4)$) whenever $\text{cardSet}(4)$ is nonempty. -/
theorem five_le_f_four (hne : (cardSet 4).Nonempty) : 5 ≤ f 4 :=
  le_csInf hne fun _ hN => five_le_of_mem_cardSet_four hN

#print axioms five_le_f_four

/-! ## Section 2: Slope Dichotomy and Cup–Cap Chains on $x$-Monotone Point Sequences -/

/-- Strict upward turn (cup step) for three points ordered by $x$-coordinate. -/
def slopeLt (a b c : ℝ²) : Prop :=
  (b 1 - a 1) * (c 0 - b 0) < (c 1 - b 1) * (b 0 - a 0)

/-- Strict downward turn (cap step) for three points ordered by $x$-coordinate. -/
def slopeGt (a b c : ℝ²) : Prop :=
  (c 1 - b 1) * (b 0 - a 0) < (b 1 - a 1) * (c 0 - b 0)

/-- If two points have distinct $x$-coordinates and the 2D cross product with a third point vanishes,
the three points are collinear. -/
theorem collinear_of_cross_eq_zero {a b c : ℝ²} (hab : a 0 ≠ b 0)
    (hcross : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0) :
    Collinear ℝ ({a, b, c} : Set ℝ²) := by
  rw [collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set ℝ²))]
  refine ⟨b - a, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hba0 : b 0 - a 0 ≠ 0 := sub_ne_zero.mpr hab.symm
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      have h0 : (p 0 - a 0) / (b 0 - a 0) * (b 0 - a 0) = p 0 - a 0 :=
        div_mul_cancel₀ _ hba0
      linarith
    · simp only [Fin.mk_one, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      have h1 : (p 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) = p 1 - a 1 := by
        rw [div_mul_eq_mul_div, div_eq_iff hba0]
        linarith
      linarith

#print axioms collinear_of_cross_eq_zero

/-- Exact collinearity equivalence via the 2D cross product when $a_0 \ne b_0$. -/
theorem collinear_iff_cross_eq_zero {a b c : ℝ²} (hab : a 0 ≠ b 0) :
    Collinear ℝ ({a, b, c} : Set ℝ²) ↔
      (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 :=
  ⟨cross_eq_zero_of_collinear, collinear_of_cross_eq_zero hab⟩

#print axioms collinear_iff_cross_eq_zero

/-- Any three non-collinear points with $a_0 \ne b_0$ form either a strict cup turn or a strict cap turn. -/
theorem slopeLt_or_slopeGt_of_not_collinear {a b c : ℝ²}
    (hab : a 0 ≠ b 0) (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    slopeLt a b c ∨ slopeGt a b c := by
  rcases lt_trichotomy ((b 1 - a 1) * (c 0 - b 0)) ((c 1 - b 1) * (b 0 - a 0)) with hlt | heq | hgt
  · exact Or.inl hlt
  · exfalso
    apply hnc
    apply collinear_of_cross_eq_zero hab
    linarith
  · exact Or.inr hgt

#print axioms slopeLt_or_slopeGt_of_not_collinear

/-- A point sequence $P : \mathbb{N} \to \mathbb{R}^2$ is $x$-monotone if its $x$-coordinates are strictly increasing. -/
def IsXMonotone (P : ℕ → ℝ²) : Prop :=
  StrictMono (fun i => P i 0)

/-- A point sequence $P : \mathbb{N} \to \mathbb{R}^2$ is non-trilinear if no three strictly increasing indices are collinear. -/
def IsSeqNonTrilinear (P : ℕ → ℝ²) : Prop :=
  ∀ ⦃i j k : ℕ⦄, i < j → j < k → ¬ Collinear ℝ ({P i, P j, P k} : Set ℝ²)

/-- `CupChainEnding P S m a b` means $S$ contains an $(m + 2)$-cup whose last two indices are $a < b$. -/
def CupChainEnding (P : ℕ → ℝ²) (S : Finset ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, a, b => a ∈ S ∧ b ∈ S ∧ a < b
  | m + 1, b, c => b ∈ S ∧ c ∈ S ∧ b < c ∧ ∃ a, CupChainEnding P S m a b ∧ slopeLt (P a) (P b) (P c)

/-- `CapChainStarting P S k b c` means $S$ contains a $(k + 2)$-cap whose first two indices are $b < c$. -/
def CapChainStarting (P : ℕ → ℝ²) (S : Finset ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, b, c => b ∈ S ∧ c ∈ S ∧ b < c
  | k + 1, a, b => a ∈ S ∧ b ∈ S ∧ a < b ∧ ∃ c, slopeGt (P a) (P b) (P c) ∧ CapChainStarting P S k b c

/-- `HasCup P S m` means $S$ contains an $(m + 2)$-cup. -/
def HasCup (P : ℕ → ℝ²) (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ a b, CupChainEnding P S m a b

/-- `HasCap P S k` means $S$ contains a $(k + 2)$-cap. -/
def HasCap (P : ℕ → ℝ²) (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ b c, CapChainStarting P S k b c

theorem cupChainEnding_left_mem {P : ℕ → ℝ²} {S : Finset ℕ} {m a b : ℕ}
    (h : CupChainEnding P S m a b) : a ∈ S := by
  cases m with
  | zero => exact h.1
  | succ _ => exact h.1

#print axioms cupChainEnding_left_mem

theorem cupChainEnding_right_mem {P : ℕ → ℝ²} {S : Finset ℕ} {m a b : ℕ}
    (h : CupChainEnding P S m a b) : b ∈ S := by
  cases m with
  | zero => exact h.2.1
  | succ _ => exact h.2.1

#print axioms cupChainEnding_right_mem

theorem cupChainEnding_lt {P : ℕ → ℝ²} {S : Finset ℕ} {m a b : ℕ}
    (h : CupChainEnding P S m a b) : a < b := by
  cases m with
  | zero => exact h.2.2
  | succ _ => exact h.2.2.1

#print axioms cupChainEnding_lt

theorem capChainStarting_left_mem {P : ℕ → ℝ²} {S : Finset ℕ} {k b c : ℕ}
    (h : CapChainStarting P S k b c) : b ∈ S := by
  cases k with
  | zero => exact h.1
  | succ _ => exact h.1

#print axioms capChainStarting_left_mem

theorem capChainStarting_right_mem {P : ℕ → ℝ²} {S : Finset ℕ} {k b c : ℕ}
    (h : CapChainStarting P S k b c) : c ∈ S := by
  cases k with
  | zero => exact h.2.1
  | succ _ => exact h.2.1

#print axioms capChainStarting_right_mem

theorem capChainStarting_lt {P : ℕ → ℝ²} {S : Finset ℕ} {k b c : ℕ}
    (h : CapChainStarting P S k b c) : b < c := by
  cases k with
  | zero => exact h.2.2
  | succ _ => exact h.2.2.1

#print axioms capChainStarting_lt

theorem cupChainEnding_mono {P : ℕ → ℝ²} {S T : Finset ℕ} (hST : S ⊆ T) :
    ∀ {m a b : ℕ}, CupChainEnding P S m a b → CupChainEnding P T m a b
  | 0, _, _, ⟨ha, hb, hab⟩ => ⟨hST ha, hST hb, hab⟩
  | _ + 1, _, _, ⟨hb, hc, hbc, a, hcup, hsl⟩ =>
      ⟨hST hb, hST hc, hbc, a, cupChainEnding_mono hST hcup, hsl⟩

#print axioms cupChainEnding_mono

theorem capChainStarting_mono {P : ℕ → ℝ²} {S T : Finset ℕ} (hST : S ⊆ T) :
    ∀ {k b c : ℕ}, CapChainStarting P S k b c → CapChainStarting P T k b c
  | 0, _, _, ⟨hb, hc, hbc⟩ => ⟨hST hb, hST hc, hbc⟩
  | _ + 1, _, _, ⟨ha, hb, hab, c, hsg, hcap⟩ =>
      ⟨hST ha, hST hb, hab, c, hsg, capChainStarting_mono hST hcap⟩

#print axioms capChainStarting_mono

theorem hasCup_mono {P : ℕ → ℝ²} {S T : Finset ℕ} {m : ℕ}
    (hST : S ⊆ T) (h : HasCup P S m) : HasCup P T m := by
  rcases h with ⟨a, b, hab⟩
  exact ⟨a, b, cupChainEnding_mono hST hab⟩

#print axioms hasCup_mono

theorem hasCap_mono {P : ℕ → ℝ²} {S T : Finset ℕ} {k : ℕ}
    (hST : S ⊆ T) (h : HasCap P S k) : HasCap P T k := by
  rcases h with ⟨b, c, hbc⟩
  exact ⟨b, c, capChainStarting_mono hST hbc⟩

#print axioms hasCap_mono

/-- Every $(m + 2)$-cup chain in $S$ ending at $(a, b)$ witnesses a subset $C \subseteq S$ of cardinality $m + 2$
with maximum element $b$. -/
theorem cupChainEnding_exists_finset {P : ℕ → ℝ²} {S : Finset ℕ} :
    ∀ {m a b : ℕ}, CupChainEnding P S m a b →
      ∃ C : Finset ℕ, C ⊆ S ∧ C.card = m + 2 ∧ a ∈ C ∧ b ∈ C ∧ ∀ x ∈ C, x ≤ b
  | 0, a, b, ⟨ha, hb, hab⟩ => by
      refine ⟨{a, b}, ?_, ?_, by simp, by simp, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · have hne : a ≠ b := ne_of_lt hab
        simp [hne]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
  | _ + 1, b, c, ⟨_, hc, hbc, _, hcup, _⟩ => by
      obtain ⟨C₀, hC₀sub, hC₀card, _, hbC₀, hC₀le⟩ := cupChainEnding_exists_finset hcup
      have hc_not_mem : c ∉ C₀ := fun hcC₀ => by
        have := hC₀le c hcC₀
        omega
      refine ⟨insert c C₀, ?_, ?_, by simp [hbC₀], by simp, ?_⟩
      · exact Finset.insert_subset_iff.mpr ⟨hc, hC₀sub⟩
      · rw [Finset.card_insert_of_notMem hc_not_mem, hC₀card]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · exact le_rfl
        · exact le_trans (hC₀le x hx₀) (le_of_lt hbc)

#print axioms cupChainEnding_exists_finset

/-- Every $(k + 2)$-cap chain in $S$ starting at $(b, c)$ witnesses a subset $C \subseteq S$ of cardinality $k + 2$
with minimum element $b$. -/
theorem capChainStarting_exists_finset {P : ℕ → ℝ²} {S : Finset ℕ} :
    ∀ {k b c : ℕ}, CapChainStarting P S k b c →
      ∃ C : Finset ℕ, C ⊆ S ∧ C.card = k + 2 ∧ b ∈ C ∧ c ∈ C ∧ ∀ x ∈ C, b ≤ x
  | 0, b, c, ⟨hb, hc, hbc⟩ => by
      refine ⟨{b, c}, ?_, ?_, by simp, by simp, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · have hne : b ≠ c := ne_of_lt hbc
        simp [hne]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
  | _ + 1, a, b, ⟨ha, _, hab, _, _, hcap⟩ => by
      obtain ⟨C₀, hC₀sub, hC₀card, hbC₀, _, hC₀ge⟩ := capChainStarting_exists_finset hcap
      have ha_not_mem : a ∉ C₀ := fun haC₀ => by
        have := hC₀ge a haC₀
        omega
      refine ⟨insert a C₀, ?_, ?_, by simp, by simp [hbC₀], ?_⟩
      · exact Finset.insert_subset_iff.mpr ⟨ha, hC₀sub⟩
      · rw [Finset.card_insert_of_notMem ha_not_mem, hC₀card]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · exact le_rfl
        · exact le_trans (le_of_lt hab) (hC₀ge x hx₀)

#print axioms capChainStarting_exists_finset

/-! ## Section 3: The Erdős–Szekeres Cup–Cap Pigeonhole Proof and Recursion -/

/-- **Endpoint-Gluing Lemma (Erdős–Szekeres 1935)**:
If an $(m + 2)$-cup ends at vertex $b$ and a $(k + 2)$-cap starts at the same vertex $b$,
then slope dichotomy at the shared vertex $b$ extends either the cup to size $m + 3$
or the cap to size $k + 3$. -/
theorem cup_end_meets_cap_start {P : ℕ → ℝ²} {S : Finset ℕ} {m k a b c : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcup : CupChainEnding P S m a b) (hcap : CapChainStarting P S k b c) :
    HasCup P S (m + 1) ∨ HasCap P S (k + 1) := by
  have hab : a < b := cupChainEnding_lt hcup
  have hbc : b < c := capChainStarting_lt hcap
  have haS : a ∈ S := cupChainEnding_left_mem hcup
  have hbS : b ∈ S := cupChainEnding_right_mem hcup
  have hcS : c ∈ S := capChainStarting_right_mem hcap
  have hxne : P a 0 ≠ P b 0 := ne_of_lt (hmono hab)
  have hnc : ¬ Collinear ℝ ({P a, P b, P c} : Set ℝ²) := hnontri hab hbc
  rcases slopeLt_or_slopeGt_of_not_collinear hxne hnc with hsl | hsg
  · exact Or.inl ⟨b, c, hbS, hcS, hbc, a, hcup, hsl⟩
  · exact Or.inr ⟨a, b, haS, hbS, hab, c, hsg, hcap⟩

#print axioms cup_end_meets_cap_start

/-- **Erdős–Szekeres Cup–Cap Theorem (1935)**:
In any $x$-monotone non-trilinear point sequence $P$, any finite index set $S$ of cardinality
at least $\binom{m+k}{m} + 1$ contains either an $(m + 2)$-cup or a $(k + 2)$-cap. -/
theorem erdos_szekeres_cup_cap_theorem {P : ℕ → ℝ²}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P) :
    ∀ (m k : ℕ) (S : Finset ℕ),
      (m + k).choose m + 1 ≤ S.card → HasCup P S m ∨ HasCap P S k
  | 0, _, S, hcard => by
      simp only [Nat.zero_add, Nat.choose_zero_right] at hcard
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inl ⟨x, y, hx, hy, hlt⟩
      · exact Or.inl ⟨y, x, hy, hx, hgt⟩
  | _ + 1, 0, S, hcard => by
      simp only [Nat.add_zero, Nat.choose_self] at hcard
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inr ⟨x, y, hx, hy, hlt⟩
      · exact Or.inr ⟨y, x, hy, hx, hgt⟩
  | m + 1, k + 1, S, hcard => by
      classical
      let E : Finset ℕ := S.filter (fun b => ∃ a, CupChainEnding P S m a b)
      have hES : E ⊆ S := Finset.filter_subset _ _
      have hpart : (S \ E).card + E.card = S.card := Finset.card_sdiff_add_card_eq_card hES
      have hchoose : ((m + 1) + (k + 1)).choose (m + 1) =
          (m + (k + 1)).choose m + ((m + 1) + k).choose (m + 1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.choose_succ_succ (m + k + 1) m
      by_cases hSE : (m + (k + 1)).choose m + 1 ≤ (S \ E).card
      · rcases erdos_szekeres_cup_cap_theorem hmono hnontri m (k + 1) (S \ E) hSE with hcup | hcap
        · rcases hcup with ⟨a, b, hab⟩
          have hb_mem : b ∈ S \ E := cupChainEnding_right_mem hab
          have hb_cup : CupChainEnding P S m a b := cupChainEnding_mono Finset.sdiff_subset hab
          rw [Finset.mem_sdiff, Finset.mem_filter] at hb_mem
          exact False.elim (hb_mem.2 ⟨hb_mem.1, a, hb_cup⟩)
        · exact Or.inr (hasCap_mono Finset.sdiff_subset hcap)
      · have hE_card : ((m + 1) + k).choose (m + 1) + 1 ≤ E.card := by omega
        rcases erdos_szekeres_cup_cap_theorem hmono hnontri (m + 1) k E hE_card with hcupE | hcapE
        · exact Or.inl (hasCup_mono hES hcupE)
        · rcases hcapE with ⟨b, c, hcap⟩
          have hbE : b ∈ E := capChainStarting_left_mem hcap
          rw [Finset.mem_filter] at hbE
          rcases hbE.2 with ⟨a, hcup⟩
          have hcapS : CapChainStarting P S k b c := capChainStarting_mono hES hcap
          exact cup_end_meets_cap_start hmono hnontri hcup hcapS

#print axioms erdos_szekeres_cup_cap_theorem

/-- The Erdős–Szekeres cup–cap threshold function $g(r, s) = \binom{r+s-4}{r-2} + 1$. -/
def cupCapBound (r s : ℕ) : ℕ :=
  (r + s - 4).choose (r - 2) + 1

/-- The Erdős–Szekeres diagonal upper bound $\binom{2n-4}{n-2} + 1$ for $f(n)$. -/
def erdosSzekeresUpper (n : ℕ) : ℕ :=
  (2 * n - 4).choose (n - 2) + 1

/-- The Erdős–Szekeres conjectured value $2^{n-2} + 1$ for $f(n)$. -/
def erdosSzekeresConjectured (n : ℕ) : ℕ :=
  2 ^ (n - 2) + 1

theorem cupCapBound_base_left (s : ℕ) : cupCapBound 2 s = 2 := by
  simp [cupCapBound]

#print axioms cupCapBound_base_left

theorem cupCapBound_base_right {r : ℕ} (hr : 2 ≤ r) : cupCapBound r 2 = 2 := by
  dsimp [cupCapBound]
  have h1 : r + 2 - 4 = r - 2 := by omega
  rw [h1, Nat.choose_self]

#print axioms cupCapBound_base_right

theorem cupCapBound_three_left {s : ℕ} (hs : 2 ≤ s) : cupCapBound 3 s = s := by
  dsimp [cupCapBound]
  have h1 : 3 + s - 4 = s - 1 := by omega
  rw [h1, Nat.choose_one_right]
  omega

#print axioms cupCapBound_three_left

theorem cupCapBound_three_right {r : ℕ} (hr : 2 ≤ r) : cupCapBound r 3 = r := by
  dsimp [cupCapBound]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have h1 : m + 2 + 3 - 4 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, h2, Nat.choose_succ_self_right]

#print axioms cupCapBound_three_right

theorem cupCapBound_symm {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    cupCapBound r s = cupCapBound s r := by
  dsimp [cupCapBound]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  have h1 : m + 2 + (k + 2) - 4 = m + k := by omega
  have h2 : k + 2 + (m + 2) - 4 = m + k := by omega
  have h3 : m + 2 - 2 = m := by omega
  have h4 : k + 2 - 2 = k := by omega
  rw [h1, h2, h3, h4]
  have hsymm := Nat.choose_symm_add (a := m) (b := k)
  omega

#print axioms cupCapBound_symm

/-- The Erdős–Szekeres Pascal recurrence $g(r + 1, s + 1) + 1 = g(r, s + 1) + g(r + 1, s)$ for $r, s \ge 2$. -/
theorem cupCapBound_recurrence {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    cupCapBound (r + 1) (s + 1) + 1 = cupCapBound r (s + 1) + cupCapBound (r + 1) s := by
  dsimp [cupCapBound]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  have h1 : m + 2 + 1 + (k + 2 + 1) - 4 = m + k + 1 + 1 := by omega
  have h2 : m + 2 + 1 - 2 = m + 1 := by omega
  have h3 : m + 2 + (k + 2 + 1) - 4 = m + k + 1 := by omega
  have h4 : m + 2 - 2 = m := by omega
  have h5 : m + 2 + 1 + (k + 2) - 4 = m + k + 1 := by omega
  rw [h1, h2, h3, h4, h5, Nat.choose_succ_succ']
  omega

#print axioms cupCapBound_recurrence

theorem erdosSzekeresUpper_eq_cupCapBound (n : ℕ) :
    erdosSzekeresUpper n = cupCapBound n n := by
  dsimp [erdosSzekeresUpper, cupCapBound]
  have h : 2 * n - 4 = n + n - 4 := by omega
  rw [h]

#print axioms erdosSzekeresUpper_eq_cupCapBound

/-- Indexed form of the Erdős–Szekeres cup–cap theorem for $r, s \ge 2$ using `cupCapBound r s`. -/
theorem erdos_szekeres_cup_cap_of_ge_two {P : ℕ → ℝ²}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (S : Finset ℕ)
    (hcard : cupCapBound r s ≤ S.card) :
    HasCup P S (r - 2) ∨ HasCap P S (s - 2) := by
  have hsum : (r - 2) + (s - 2) = r + s - 4 := by omega
  apply erdos_szekeres_cup_cap_theorem hmono hnontri (r - 2) (s - 2) S
  rw [hsum]
  exact hcard

#print axioms erdos_szekeres_cup_cap_of_ge_two

/-- Diagonal Erdős–Szekeres cup–cap theorem: any $x$-monotone non-trilinear set of size at least
$\binom{2n-4}{n-2} + 1$ ($n \ge 2$) contains either an $n$-cup or an $n$-cap. -/
theorem erdos_szekeres_diagonal_cup_cap {P : ℕ → ℝ²}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    {n : ℕ} (hn : 2 ≤ n) (S : Finset ℕ)
    (hcard : erdosSzekeresUpper n ≤ S.card) :
    HasCup P S (n - 2) ∨ HasCap P S (n - 2) := by
  rw [erdosSzekeresUpper_eq_cupCapBound] at hcard
  exact erdos_szekeres_cup_cap_of_ge_two hmono hnontri hn hn S hcard

#print axioms erdos_szekeres_diagonal_cup_cap

/-! ## Section 4: Universal Comparison Between $2^{n-2} + 1$ and $\binom{2n-4}{n-2} + 1$ -/

/-- Doubling inequality for central binomial coefficients: $2 \binom{2k}{k} \le \binom{2(k+1)}{k+1}$. -/
theorem two_mul_choose_central_le_succ (k : ℕ) :
    2 * (2 * k).choose k ≤ (2 * (k + 1)).choose (k + 1) := by
  cases k with
  | zero => decide
  | succ m =>
    have h0 : 2 * (m + 1 + 1) = 2 * m + 2 + 1 + 1 := by omega
    have h0b : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h0, h0b]
    have h1 := Nat.choose_succ_succ' (2 * m + 2 + 1) (m + 1)
    have h2 := Nat.choose_succ_succ' (2 * m + 2) m
    have h3 := Nat.choose_succ_succ' (2 * m + 2) (m + 1)
    omega

#print axioms two_mul_choose_central_le_succ

/-- Universal exponential lower bound for central binomial coefficients: $2^k \le \binom{2k}{k}$. -/
theorem two_pow_le_central_binom (k : ℕ) : 2 ^ k ≤ (2 * k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := two_mul_choose_central_le_succ k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

#print axioms two_pow_le_central_binom

/-- Strict exponential lower bound for central binomial coefficients when $k \ge 2$: $2^k < \binom{2k}{k}$. -/
theorem two_pow_lt_central_binom_of_ge_two {k : ℕ} (hk : 2 ≤ k) :
    2 ^ k < (2 * k).choose k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  induction m with
  | zero => decide
  | succ m ih =>
    change 2 ^ (m + 2 + 1) < (2 * (m + 2 + 1)).choose (m + 2 + 1)
    have hstep := two_mul_choose_central_le_succ (m + 2)
    have hlt : 2 ^ (m + 2) < (2 * (m + 2)).choose (m + 2) := ih (by omega)
    have hpow : 2 ^ (m + 2 + 1) = 2 * 2 ^ (m + 2) := by ring
    omega

#print axioms two_pow_lt_central_binom_of_ge_two

/-- For every $n \in \mathbb{N}$, the conjectured Erdős–Szekeres value $2^{n-2} + 1$ is bounded above
by the Erdős–Szekeres binomial upper bound $\binom{2n-4}{n-2} + 1$. -/
theorem erdosSzekeresConjectured_le_upper (n : ℕ) :
    erdosSzekeresConjectured n ≤ erdosSzekeresUpper n := by
  dsimp [erdosSzekeresConjectured, erdosSzekeresUpper]
  rcases le_or_gt n 2 with hn | hn
  · have h1 : n - 2 = 0 := by omega
    have h2 : 2 * n - 4 = 0 := by omega
    rw [h1, h2]
    decide
  · have h2n : 2 * n - 4 = 2 * (n - 2) := by omega
    rw [h2n]
    have := two_pow_le_central_binom (n - 2)
    omega

#print axioms erdosSzekeresConjectured_le_upper

/-- For every $n \ge 4$, the conjectured Erdős–Szekeres bound $2^{n-2} + 1$ is strictly smaller than
the Erdős–Szekeres cup–cap upper bound $\binom{2n-4}{n-2} + 1$. -/
theorem erdosSzekeresConjectured_lt_upper_of_ge_four {n : ℕ} (hn : 4 ≤ n) :
    erdosSzekeresConjectured n < erdosSzekeresUpper n := by
  dsimp [erdosSzekeresConjectured, erdosSzekeresUpper]
  have h2n : 2 * n - 4 = 2 * (n - 2) := by omega
  rw [h2n]
  have := two_pow_lt_central_binom_of_ge_two (k := n - 2) (by omega)
  omega

#print axioms erdosSzekeresConjectured_lt_upper_of_ge_four

/-- At $n = 3$, $f(3)$ coincides with both the conjectured value $2^{3-2} + 1 = 3$ and the
Erdős–Szekeres upper bound $\binom{2\cdot 3 - 4}{3 - 2} + 1 = 3$. -/
theorem f_three_eq_conjectured_and_upper :
    f 3 = erdosSzekeresConjectured 3 ∧ erdosSzekeresConjectured 3 = erdosSzekeresUpper 3 := by
  refine ⟨?_, rfl⟩
  rw [f_three_eq]
  rfl

#print axioms f_three_eq_conjectured_and_upper

/-- At $n = 4$, the conjectured value $2^{4-2} + 1 = 5$ is a verified lower bound on $f(4)$
(assuming $\text{cardSet}(4)$ is nonempty) and is strictly below the diagonal cup–cap bound $7$. -/
theorem f_four_conjectured_lower_and_upper_gap (hne : (cardSet 4).Nonempty) :
    erdosSzekeresConjectured 4 ≤ f 4 ∧ erdosSzekeresConjectured 4 < erdosSzekeresUpper 4 :=
  ⟨five_le_f_four hne, erdosSzekeresConjectured_lt_upper_of_ge_four (by decide)⟩

#print axioms f_four_conjectured_lower_and_upper_gap


/-!
# Erdős–Szekeres Cup–Cap Identities, Half-Plane Separation, and Happy Ending Reductions (#107)

This module advances Erdős Problem #107 (`erdos_107`) on three complementary fronts:

1. **Universal Strict Affine Half-Plane Separation and Convex Independence in $\mathbb{R}^2$**:
   - Proves that every closed affine half-plane $\{p \in \mathbb{R}^2 \mid u p_0 + v p_1 \le c\}$ is convex,
     hence contains the `convexHull ℝ` of any subset lying inside it (`convexHull_subset_halfPlaneLe`).
   - Deduces the universal strict separation exclusion principle (`not_mem_convexHull_of_strict_linear_sep`),
     pointwise extreme-point characterization of `ConvexIndep` (`convexIndep_of_pointwise_strict_sep`),
     and the 4-point convex quadrilateral criterion (`convexIndep_four_of_strict_sep`).
   - Proves both cases of the 5-point Happy Ending configuration geometry on explicit witnesses:
     (a) the 4-extreme-point extension `kleinFivePts` $= \{(0,0),(3,0),(0,3),(1,1),(2,4)\}$ of Esther Klein's
         non-convex 4-point configuration `kleinFourPts`, certifying `NonTrilinear` and `HasConvexNGon 4`;
     (b) the 3-outer-hull + 2-interior-point configuration `kleinFiveInnerPts`
         $= \{(0,0),(6,0),(0,6),(2,2),(3,1)\}$, proving both $(2,2)$ and $(3,1)$ lie in the convex hull of the
         outer triangle while the line $x + y = 4$ through $(2,2)$ and $(3,1)$ places $(6,0)$ and $(0,6)$ on
         the same side to form the convex 4-gon $\{(6,0),(0,6),(2,2),(3,1)\}$.

2. **Universal Parabolic Convexity and 3-Cup / 3-Cap Convex Independence**:
   - Proves via tangent-line separation $2 i x - y \le i^2 - 1 < i^2$ ($j \ne i$) that the $N$-point
     integer parabola `parabolaFinset N` is globally convex independent for every $N \in \mathbb{N}$
     (`parabolaFinset_convexIndep`), and hence contains a convex $n$-gon for every $n \le N$
     (`parabolaFinset_hasConvexNGon`).
   - Proves that every 3-point cup (`slopeLt`) and every 3-point cap (`slopeGt`) in an $x$-monotone sequence
     is non-collinear and convex independent (`cup_three_convexIndep`, `cap_three_convexIndep`).

3. **Universal Cup–Cap Hockey-Stick Summation, Anti-Diagonal $2^{n-2}$ Block Decomposition, and Tóth–Valtr Bounds**:
   - Proves strict diagonal monotonicity of `cupCapBound`, the universal hockey-stick identity
     $\sum_{i=0}^{m} (f(i+2, k+2) - 1) = f(m+2, k+3) - 1$, and the Erdős–Szekeres (1960) anti-diagonal
     block decomposition $\sum_{j=0}^{n-2} (f(j+2, n-j) - 1) = 2^{n-2}$.
   - Formalizes the Tóth–Valtr / Kleitman–Pachter bound `tothValtrUpper n` $= \binom{2n-5}{n-2} + 1$,
     proves the exact halving identity $\text{erdosSzekeresUpper}(n) + 1 = 2 \cdot \text{tothValtrUpper}(n)$
     for all $n \ge 3$, and proves the universal strict hierarchy
     $\text{erdosSzekeresConjectured}(n) < \text{tothValtrUpper}(n) < \text{erdosSzekeresUpper}(n)$ for all $n \ge 5$.
-/

/-! ## Section 1: Universal Half-Plane Separation and Convex Independence in $\mathbb{R}^2$ -/

/-- Closed affine half-plane $\{p \in \mathbb{R}^2 \mid u p_0 + v p_1 \le c\}$. -/
def halfPlaneLe (u v c : ℝ) : Set ℝ² :=
  { p : ℝ² | u * p 0 + v * p 1 ≤ c }

/-- Every closed affine half-plane in $\mathbb{R}^2$ is convex. -/
theorem convex_halfPlaneLe (u v c : ℝ) : Convex ℝ (halfPlaneLe u v c) := by
  intro x hx y hy a b ha hb hab
  change u * x 0 + v * x 1 ≤ c at hx
  change u * y 0 + v * y 1 ≤ c at hy
  change u * (a • x + b • y) 0 + v * (a • x + b • y) 1 ≤ c
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
  rw [h0, h1]
  have hax : a * (u * x 0 + v * x 1) ≤ a * c := mul_le_mul_of_nonneg_left hx ha
  have hby : b * (u * y 0 + v * y 1) ≤ b * c := mul_le_mul_of_nonneg_left hy hb
  have hc : a * c + b * c = c := by linear_combination c * hab
  linarith

#print axioms convex_halfPlaneLe

/-- If a point set $S \subseteq \mathbb{R}^2$ lies in a closed affine half-plane, so does its convex hull. -/
theorem convexHull_subset_halfPlaneLe {u v c : ℝ} {S : Set ℝ²}
    (hS : ∀ y ∈ S, u * y 0 + v * y 1 ≤ c) :
    convexHull ℝ S ⊆ halfPlaneLe u v c :=
  convexHull_min hS (convex_halfPlaneLe u v c)

#print axioms convexHull_subset_halfPlaneLe

/-- Universal strict linear separation exclusion: if $u y_0 + v y_1 \le c$ for all $y \in S$
and $c < u x_0 + v x_1$, then $x \notin \mathrm{convexHull}\,\mathbb{R}\,S$. -/
theorem not_mem_convexHull_of_strict_linear_sep {u v c : ℝ} {S : Set ℝ²} {x : ℝ²}
    (hS : ∀ y ∈ S, u * y 0 + v * y 1 ≤ c)
    (hx : c < u * x 0 + v * x 1) :
    x ∉ convexHull ℝ S := by
  intro hmem
  have hle : u * x 0 + v * x 1 ≤ c := convexHull_subset_halfPlaneLe hS hmem
  linarith

#print axioms not_mem_convexHull_of_strict_linear_sep

/-- Universal pointwise linear separation criterion for `ConvexIndep`. -/
theorem convexIndep_of_pointwise_strict_sep {S : Set ℝ²}
    (hsep : ∀ x ∈ S, ∃ u v c : ℝ,
      (∀ y ∈ S \ {x}, u * y 0 + v * y 1 ≤ c) ∧ c < u * x 0 + v * x 1) :
    ConvexIndep S := by
  intro x hx
  rcases hsep x hx with ⟨u, v, c, hle, hlt⟩
  exact not_mem_convexHull_of_strict_linear_sep hle hlt

#print axioms convexIndep_of_pointwise_strict_sep

/-- Universal 4-point strict-separation criterion for convex quadrilaterals in $\mathbb{R}^2$. -/
theorem convexIndep_four_of_strict_sep {p₁ p₂ p₃ p₄ : ℝ²}
    (h₁ : ∃ u v c : ℝ, u * p₂ 0 + v * p₂ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₁ 0 + v * p₁ 1)
    (h₂ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₂ 0 + v * p₂ 1)
    (h₃ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₃ 0 + v * p₃ 1)
    (h₄ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ c < u * p₄ 0 + v * p₄ 1) :
    ConvexIndep ({p₁, p₂, p₃, p₄} : Set ℝ²) := by
  apply convexIndep_of_pointwise_strict_sep
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rcases h₁ with ⟨u, v, c, hp₂, hp₃, hp₄, hp₁⟩
    refine ⟨u, v, c, ?_, hp₁⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact False.elim (hy_ne rfl)
    · exact hp₂
    · exact hp₃
    · exact hp₄
  · rcases h₂ with ⟨u, v, c, hp₁, hp₃, hp₄, hp₂⟩
    refine ⟨u, v, c, ?_, hp₂⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact hp₁
    · exact False.elim (hy_ne rfl)
    · exact hp₃
    · exact hp₄
  · rcases h₃ with ⟨u, v, c, hp₁, hp₂, hp₄, hp₃⟩
    refine ⟨u, v, c, ?_, hp₃⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact False.elim (hy_ne rfl)
    · exact hp₄
  · rcases h₄ with ⟨u, v, c, hp₁, hp₂, hp₃, hp₄⟩
    refine ⟨u, v, c, ?_, hp₄⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact hp₃
    · exact False.elim (hy_ne rfl)

#print axioms convexIndep_four_of_strict_sep

/-- Universal 4-extreme-point reduction: any point set $P \subseteq \mathbb{R}^2$ containing four
pairwise distinct points that are each strictly separated from the other three contains a convex 4-gon. -/
theorem hasConvexFourGon_of_four_extreme {P : Set ℝ²} {p₁ p₂ p₃ p₄ : ℝ²}
    (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (hp₃ : p₃ ∈ P) (hp₄ : p₄ ∈ P)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₁₄ : p₁ ≠ p₄)
    (h₂₃ : p₂ ≠ p₃) (h₂₄ : p₂ ≠ p₄) (h₃₄ : p₃ ≠ p₄)
    (hsep₁ : ∃ u v c : ℝ, u * p₂ 0 + v * p₂ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₁ 0 + v * p₁ 1)
    (hsep₂ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₂ 0 + v * p₂ 1)
    (hsep₃ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₃ 0 + v * p₃ 1)
    (hsep₄ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ c < u * p₄ 0 + v * p₄ 1) :
    HasConvexNGon 4 P := by
  refine ⟨{p₁, p₂, p₃, p₄}, ?_, ?_, ?_⟩
  · simp [h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · simpa using convexIndep_four_of_strict_sep hsep₁ hsep₂ hsep₃ hsep₄

#print axioms hasConvexFourGon_of_four_extreme

/-! ## Section 2: Happy Ending 5-Point Case-Split Witnesses (4-Hull and 3-Hull + 2-Interior) -/

/-- Fifth point $(2, 4)$ extending `kleinFourPts` in general position. -/
def ptD : ℝ² := mkPt 2 4

/-- The 5-point general-position extension $\{(0,0), (3,0), (0,3), (1,1), (2,4)\}$ of `kleinFourPts`. -/
def kleinFivePts : Finset ℝ² := {ptO, ptA, ptB, ptC, ptD}

theorem ptO_ne_ptD : ptO ≠ ptD := by
  intro h; have h0 := congrArg (fun w : ℝ² => w 0) h; simp [ptO, ptD] at h0

#print axioms ptO_ne_ptD

theorem ptA_ne_ptD : ptA ≠ ptD := by
  intro h; have h0 := congrArg (fun w : ℝ² => w 0) h; simp [ptA, ptD] at h0

#print axioms ptA_ne_ptD

theorem ptB_ne_ptD : ptB ≠ ptD := by
  intro h; have h0 := congrArg (fun w : ℝ² => w 0) h; simp [ptB, ptD] at h0

#print axioms ptB_ne_ptD

theorem ptC_ne_ptD : ptC ≠ ptD := by
  intro h; have h0 := congrArg (fun w : ℝ² => w 0) h; simp [ptC, ptD] at h0

#print axioms ptC_ne_ptD

theorem kleinFivePts_card : kleinFivePts.card = 5 := by
  simp [kleinFivePts, ptO_ne_ptA, ptO_ne_ptB, ptO_ne_ptC, ptO_ne_ptD,
    ptA_ne_ptB, ptA_ne_ptC, ptA_ne_ptD, ptB_ne_ptC, ptB_ne_ptD, ptC_ne_ptD]

#print axioms kleinFivePts_card

/-- Positive control: no three points of the 5-point extension `kleinFivePts` are collinear. -/
theorem kleinFivePts_nonTrilinear :
    NonTrilinear (kleinFivePts : Set ℝ²) := by
  intro x hx y hy z hz hxy hyz hxz
  simp only [kleinFivePts, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hxy rfl)
    | exact False.elim (hyz rfl)
    | exact False.elim (hxz rfl)
    | (apply not_collinear_of_cross_ne_zero; norm_num [ptO, ptA, ptB, ptC, ptD, mkPt_zero, mkPt_one])

#print axioms kleinFivePts_nonTrilinear

/-- The 4-element outer hull $\{(0,0), (3,0), (0,3), (2,4)\}$ of `kleinFivePts` is convex independent. -/
theorem kleinFiveOuterQuad_convexIndep :
    ConvexIndep ({ptO, ptA, ptB, ptD} : Set ℝ²) := by
  apply convexIndep_four_of_strict_sep
  · refine ⟨-1, -1, -1, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptO, ptA, ptB, ptD, mkPt_zero, mkPt_one]
  · refine ⟨1, -1, 2, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptO, ptA, ptB, ptD, mkPt_zero, mkPt_one]
  · refine ⟨-2, 1, 2, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptO, ptA, ptB, ptD, mkPt_zero, mkPt_one]
  · refine ⟨1, 1, 5, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptO, ptA, ptB, ptD, mkPt_zero, mkPt_one]

#print axioms kleinFiveOuterQuad_convexIndep

/-- While `kleinFourPts` has no convex 4-gon, its 5-point extension `kleinFivePts` contains a convex 4-gon. -/
theorem kleinFivePts_hasConvexFourGon :
    HasConvexNGon 4 (kleinFivePts : Set ℝ²) := by
  refine ⟨{ptO, ptA, ptB, ptD}, ?_, ?_, ?_⟩
  · simp [ptO_ne_ptA, ptO_ne_ptB, ptO_ne_ptD, ptA_ne_ptB, ptA_ne_ptD, ptB_ne_ptD]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [kleinFivePts]
  · simpa using kleinFiveOuterQuad_convexIndep

#print axioms kleinFivePts_hasConvexFourGon

/-- Outer right vertex $(6, 0)$ for the 2-interior-point Happy Ending witness. -/
def ptA6 : ℝ² := mkPt 6 0

/-- Outer top vertex $(0, 6)$ for the 2-interior-point Happy Ending witness. -/
def ptB6 : ℝ² := mkPt 0 6

/-- First interior point $(2, 2)$ of the triangle $\{(0,0), (6,0), (0,6)\}$. -/
def ptP : ℝ² := mkPt 2 2

/-- Second interior point $(3, 1)$ of the triangle $\{(0,0), (6,0), (0,6)\}$. -/
def ptQ : ℝ² := mkPt 3 1

theorem ptP_eq_barycentric_outer6 :
    ptP = (1 / 3 : ℝ) • ptO + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • ptA6 + (1 / 2 : ℝ) • ptB6) := by
  ext i
  fin_cases i <;> simp [ptO, ptA6, ptB6, ptP, mkPt] <;> norm_num

#print axioms ptP_eq_barycentric_outer6

theorem ptQ_eq_barycentric_outer6 :
    ptQ = (1 / 3 : ℝ) • ptO + (2 / 3 : ℝ) • ((3 / 4 : ℝ) • ptA6 + (1 / 4 : ℝ) • ptB6) := by
  ext i
  fin_cases i <;> simp [ptO, ptA6, ptB6, ptQ, mkPt] <;> norm_num

#print axioms ptQ_eq_barycentric_outer6

/-- First interior point $(2, 2)$ lies in the convex hull of the outer triangle $\{(0,0), (6,0), (0,6)\}$. -/
theorem ptP_mem_convexHull_outer6 :
    ptP ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) := by
  have hconv : Convex ℝ (convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²)) :=
    convex_convexHull ℝ _
  have hO : ptO ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hA : ptA6 ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hB : ptB6 ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hAB : (1 / 2 : ℝ) • ptA6 + (1 / 2 : ℝ) • ptB6 ∈
      convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    hconv hA hB (by norm_num) (by norm_num) (by norm_num)
  rw [ptP_eq_barycentric_outer6]
  exact hconv hO hAB (by norm_num) (by norm_num) (by norm_num)

#print axioms ptP_mem_convexHull_outer6

/-- Second interior point $(3, 1)$ also lies in the convex hull of the outer triangle $\{(0,0), (6,0), (0,6)\}$. -/
theorem ptQ_mem_convexHull_outer6 :
    ptQ ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) := by
  have hconv : Convex ℝ (convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²)) :=
    convex_convexHull ℝ _
  have hO : ptO ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hA : ptA6 ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hB : ptB6 ∈ convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hAB : (3 / 4 : ℝ) • ptA6 + (1 / 4 : ℝ) • ptB6 ∈
      convexHull ℝ ({ptO, ptA6, ptB6} : Set ℝ²) :=
    hconv hA hB (by norm_num) (by norm_num) (by norm_num)
  rw [ptQ_eq_barycentric_outer6]
  exact hconv hO hAB (by norm_num) (by norm_num) (by norm_num)

#print axioms ptQ_mem_convexHull_outer6

/-- In the 3-hull + 2-interior case, the two interior points $(2,2), (3,1)$ together with the two
outer vertices $(6,0), (0,6)$ on the same side of the line $x + y = 4$ form a convex quadrilateral. -/
theorem innerQuad6_convexIndep :
    ConvexIndep ({ptA6, ptB6, ptP, ptQ} : Set ℝ²) := by
  apply convexIndep_four_of_strict_sep
  · refine ⟨1, -1, 3, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptA6, ptB6, ptP, ptQ, mkPt_zero, mkPt_one]
  · refine ⟨-1, 1, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptA6, ptB6, ptP, ptQ, mkPt_zero, mkPt_one]
  · refine ⟨-5, -3, -18, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptA6, ptB6, ptP, ptQ, mkPt_zero, mkPt_one]
  · refine ⟨-1, -2, -6, ?_, ?_, ?_, ?_⟩ <;> norm_num [ptA6, ptB6, ptP, ptQ, mkPt_zero, mkPt_one]

#print axioms innerQuad6_convexIndep

/-! ## Section 3: Universal Parabolic Convex Independence and 3-Cup / 3-Cap Convexity -/

/-- For distinct natural numbers $i \ne j$, $((j : \mathbb{R}) - (i : \mathbb{R}))^2 \ge 1$. -/
theorem nat_cast_sub_sq_ge_one_of_ne {i j : ℕ} (hne : i ≠ j) :
    (1 : ℝ) ≤ ((j : ℝ) - (i : ℝ)) ^ 2 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    nlinarith
  · have h1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    nlinarith

#print axioms nat_cast_sub_sq_ge_one_of_ne

/-- Tangent-line separation for integer parabola points: for $i \ne j$,
$2 i \cdot x_j - y_j = i^2 - (j - i)^2 \le i^2 - 1$. -/
theorem parabolaPt_tangent_sep {i j : ℕ} (hne : i ≠ j) :
    2 * (i : ℝ) * (parabolaPt j 0) + (-1 : ℝ) * (parabolaPt j 1) ≤ (i : ℝ) ^ 2 - 1 := by
  simp only [parabolaPt, mkPt_zero, mkPt_one]
  have hsq : (1 : ℝ) ≤ ((j : ℝ) - (i : ℝ)) ^ 2 := nat_cast_sub_sq_ge_one_of_ne hne
  linarith

#print axioms parabolaPt_tangent_sep

/-- Every $N$-point integer parabola configuration `parabolaFinset N` is globally convex independent. -/
theorem parabolaFinset_convexIndep (N : ℕ) :
    ConvexIndep ((parabolaFinset N : Finset ℝ²) : Set ℝ²) := by
  apply convexIndep_of_pointwise_strict_sep
  intro x hx
  simp only [parabolaFinset, Finset.coe_image, Set.mem_image] at hx
  rcases hx with ⟨i, _, rfl⟩
  refine ⟨2 * (i : ℝ), -1, (i : ℝ) ^ 2 - 1, ?_, ?_⟩
  · intro y ⟨hy_mem, hy_ne⟩
    simp only [parabolaFinset, Finset.coe_image, Set.mem_image] at hy_mem
    rcases hy_mem with ⟨j, _, rfl⟩
    have hne : i ≠ j := fun h => hy_ne (congrArg parabolaPt h.symm)
    exact parabolaPt_tangent_sep hne
  · simp only [parabolaPt, mkPt_zero, mkPt_one]
    linarith

#print axioms parabolaFinset_convexIndep

/-- Every $N$-point integer parabola configuration contains a convex $n$-gon for every $n \le N$. -/
theorem parabolaFinset_hasConvexNGon {n N : ℕ} (hle : n ≤ N) :
    HasConvexNGon n ((parabolaFinset N : Finset ℝ²) : Set ℝ²) :=
  hasConvexNGon_mono_n
    ⟨parabolaFinset N, parabolaFinset_card N, subset_refl _, parabolaFinset_convexIndep N⟩
    hle

#print axioms parabolaFinset_hasConvexNGon

/-- Strict upward slope turn (`slopeLt`) implies non-collinearity. -/
theorem not_collinear_of_slopeLt {a b c : ℝ²} (hsl : slopeLt a b c) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) := by
  intro hcoll
  have hcross := cross_eq_zero_of_collinear hcoll
  unfold slopeLt at hsl
  linarith

#print axioms not_collinear_of_slopeLt

/-- Strict downward slope turn (`slopeGt`) implies non-collinearity. -/
theorem not_collinear_of_slopeGt {a b c : ℝ²} (hsg : slopeGt a b c) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) := by
  intro hcoll
  have hcross := cross_eq_zero_of_collinear hcoll
  unfold slopeGt at hsg
  linarith

#print axioms not_collinear_of_slopeGt

/-- Strictly increasing indices in an $x$-monotone sequence map to distinct points. -/
theorem xMonotone_ne_of_lt {P : ℕ → ℝ²} (hmono : IsXMonotone P) {i j : ℕ} (hij : i < j) :
    P i ≠ P j := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  exact (ne_of_lt (hmono hij)) h0

#print axioms xMonotone_ne_of_lt

/-- Every 3-point cup in an $x$-monotone sequence is convex independent. -/
theorem cup_three_convexIndep {P : ℕ → ℝ²} (hmono : IsXMonotone P)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) (hsl : slopeLt (P a) (P b) (P c)) :
    ConvexIndep ({P a, P b, P c} : Set ℝ²) :=
  convexIndep_triple_of_not_collinear
    (xMonotone_ne_of_lt hmono hab)
    (xMonotone_ne_of_lt hmono (lt_trans hab hbc))
    (xMonotone_ne_of_lt hmono hbc)
    (not_collinear_of_slopeLt hsl)

#print axioms cup_three_convexIndep

/-- Every 3-point cap in an $x$-monotone sequence is convex independent. -/
theorem cap_three_convexIndep {P : ℕ → ℝ²} (hmono : IsXMonotone P)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) (hsg : slopeGt (P a) (P b) (P c)) :
    ConvexIndep ({P a, P b, P c} : Set ℝ²) :=
  convexIndep_triple_of_not_collinear
    (xMonotone_ne_of_lt hmono hab)
    (xMonotone_ne_of_lt hmono (lt_trans hab hbc))
    (xMonotone_ne_of_lt hmono hbc)
    (not_collinear_of_slopeGt hsg)

#print axioms cap_three_convexIndep

/-! ## Section 4: Cup–Cap Hockey-Stick Summation, Anti-Diagonal $2^{n-2}$ Block Decomposition, and Tóth–Valtr Bounds -/

theorem cupCapBound_sub_one (r s : ℕ) :
    cupCapBound r s - 1 = (r + s - 4).choose (r - 2) := by
  simp [cupCapBound]

#print axioms cupCapBound_sub_one

/-- Strict right-step monotonicity of `cupCapBound` for $r \ge 3$ and $s \ge 2$:
$f(r, s) < f(r, s + 1)$. -/
theorem cupCapBound_lt_succ_right {r s : ℕ} (hr : 3 ≤ r) (hs : 2 ≤ s) :
    cupCapBound r s < cupCapBound r (s + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 + 1 := ⟨r - 3, by omega⟩
  have hrec := cupCapBound_recurrence (r := m + 2) (s := s) (by omega) hs
  have hpos : 2 ≤ cupCapBound (m + 2) (s + 1) := by
    dsimp [cupCapBound]
    have hch : 0 < (m + 2 + (s + 1) - 4).choose (m + 2 - 2) :=
      Nat.choose_pos (by omega)
    omega
  omega

#print axioms cupCapBound_lt_succ_right

/-- Strict left-step monotonicity of `cupCapBound` for $r \ge 2$ and $s \ge 3$:
$f(r, s) < f(r + 1, s)$. -/
theorem cupCapBound_lt_succ_left {r s : ℕ} (hr : 2 ≤ r) (hs : 3 ≤ s) :
    cupCapBound r s < cupCapBound (r + 1) s := by
  rw [cupCapBound_symm hr (by omega : 2 ≤ s), cupCapBound_symm (by omega : 2 ≤ r + 1) (by omega : 2 ≤ s)]
  exact cupCapBound_lt_succ_right hs hr

#print axioms cupCapBound_lt_succ_left

/-- Strict diagonal monotonicity of the Erdős–Szekeres cup–cap threshold:
for $r \ge 3$ and $s \ge 2$, $f(r, s) < f(r + 1, s + 1)$. -/
theorem cupCapBound_strictMono_diag {r s : ℕ} (hr : 3 ≤ r) (hs : 2 ≤ s) :
    cupCapBound r s < cupCapBound (r + 1) (s + 1) := by
  exact lt_trans (cupCapBound_lt_succ_right hr hs)
    (cupCapBound_lt_succ_left (by omega) (by omega))

#print axioms cupCapBound_strictMono_diag

/-- Universal hockey-stick column summation for the Erdős–Szekeres cup–cap function:
$\sum_{i=0}^{m} (f(i+2, k+2) - 1) = f(m+2, k+3) - 1$. -/
theorem sum_cupCapBound_sub_one_left (m k : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (cupCapBound (i + 2) (k + 2) - 1) =
      cupCapBound (m + 2) (k + 3) - 1 := by
  induction m with
  | zero =>
    simp [cupCapBound]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : cupCapBound (m + 1 + 2) (k + 3) + 1 =
        cupCapBound (m + 2) (k + 3) + cupCapBound (m + 1 + 2) (k + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        cupCapBound_recurrence (r := m + 2) (s := k + 2) (by omega) (by omega)
    have hpos : 1 ≤ cupCapBound (m + 2) (k + 3) := by
      dsimp [cupCapBound]; omega
    have hpos2 : 1 ≤ cupCapBound (m + 1 + 2) (k + 2) := by
      dsimp [cupCapBound]; omega
    omega

#print axioms sum_cupCapBound_sub_one_left

/-- Universal Erdős–Szekeres (1960) anti-diagonal block decomposition of $2^m$:
the extremal $(m+2)$-gon-free construction partitions $2^m$ points into $m+1$ blocks
of sizes $f(j+2, m+2-j) - 1 = \binom{m}{j}$ ($0 \le j \le m$), each avoiding $(j+2)$-cups
and $(m+2-j)$-caps. -/
theorem sum_cupCapBound_antidiag_sub_one (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (cupCapBound (j + 2) (m + 2 - j) - 1) = 2 ^ m := by
  have hcongr :
      ∑ j ∈ Finset.range (m + 1), (cupCapBound (j + 2) (m + 2 - j) - 1) =
        ∑ j ∈ Finset.range (m + 1), m.choose j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    dsimp [cupCapBound]
    have h1 : j + 2 + (m + 2 - j) - 4 = m := by omega
    have h2 : j + 2 - 2 = j := by omega
    rw [h1, h2]
  rw [hcongr, Nat.sum_range_choose]

#print axioms sum_cupCapBound_antidiag_sub_one

/-- For every $n \ge 2$, one plus the sum of the anti-diagonal cup–cap block capacities
$\sum_{j=0}^{n-2} (f(j+2, n-j) - 1)$ equals the conjectured threshold $2^{n-2} + 1$. -/
theorem sum_cupCapBound_antidiag_eq_conjectured {n : ℕ} (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n - 1), (cupCapBound (j + 2) (n - j) - 1)) + 1 =
      erdosSzekeresConjectured n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, sum_cupCapBound_antidiag_sub_one m]
  simp [erdosSzekeresConjectured, h2]

#print axioms sum_cupCapBound_antidiag_eq_conjectured

/-- The Chung–Graham / Kleitman–Pachter / Tóth–Valtr upper bound $\binom{2n-5}{n-2} + 1$. -/
def tothValtrUpper (n : ℕ) : ℕ :=
  (2 * n - 5).choose (n - 2) + 1

/-- Universal halving identity: for every $n \ge 3$,
$\text{erdosSzekeresUpper}(n) + 1 = 2 \cdot \text{tothValtrUpper}(n)$. -/
theorem erdosSzekeresUpper_add_one_eq_two_mul_tothValtrUpper {n : ℕ} (hn : 3 ≤ n) :
    erdosSzekeresUpper n + 1 = 2 * tothValtrUpper n := by
  dsimp [erdosSzekeresUpper, tothValtrUpper]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : 2 * (m + 3) - 4 = (2 * m + 1) + 1 := by omega
  have h2 : m + 3 - 2 = m + 1 := by omega
  have h3 : 2 * (m + 3) - 5 = 2 * m + 1 := by omega
  rw [h1, h2, h3, Nat.choose_succ_succ' (2 * m + 1) m]
  have hsymm : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
    have hs := Nat.choose_symm_add (a := m) (b := m + 1)
    have hsum : m + (m + 1) = 2 * m + 1 := by omega
    simpa [hsum] using hs
  omega

#print axioms erdosSzekeresUpper_add_one_eq_two_mul_tothValtrUpper

/-- For every $n \ge 4$, `tothValtrUpper n` is strictly smaller than `erdosSzekeresUpper n`. -/
theorem tothValtrUpper_lt_erdosSzekeresUpper_of_ge_four {n : ℕ} (hn : 4 ≤ n) :
    tothValtrUpper n < erdosSzekeresUpper n := by
  have hhalve := erdosSzekeresUpper_add_one_eq_two_mul_tothValtrUpper (by omega : 3 ≤ n)
  have hgt : 5 < erdosSzekeresUpper n := by
    have hlt := erdosSzekeresConjectured_lt_upper_of_ge_four hn
    have hge : 5 ≤ erdosSzekeresConjectured n := by
      dsimp [erdosSzekeresConjectured]
      have : 2 ^ 2 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega
  omega

#print axioms tothValtrUpper_lt_erdosSzekeresUpper_of_ge_four

theorem two_pow_add_three_lt_choose_two_mul_add_five (m : ℕ) :
    2 ^ (m + 3) < (2 * m + 5).choose (m + 3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h0 : 2 * (m + 1) + 5 = 2 * m + 5 + 1 + 1 := by omega
    have h0b : m + 1 + 3 = m + 3 + 1 := by omega
    rw [h0, h0b]
    have c1 := Nat.choose_succ_succ' (2 * m + 5 + 1) (m + 3)
    have c2 := Nat.choose_succ_succ' (2 * m + 5) (m + 2)
    have c3 := Nat.choose_succ_succ' (2 * m + 5) (m + 3)
    have hc1 : (2 * m + 5 + 1).choose (m + 2 + 1) = (2 * m + 5 + 1).choose (m + 3) := rfl
    have hc2 : (2 * m + 5).choose (m + 2 + 1) = (2 * m + 5).choose (m + 3) := rfl
    have hsymm : (2 * m + 5).choose (m + 2) = (2 * m + 5).choose (m + 3) := by
      have hs := Nat.choose_symm_add (a := m + 2) (b := m + 3)
      have hsum : (m + 2) + (m + 3) = 2 * m + 5 := by omega
      simpa [hsum] using hs
    have hpow : 2 ^ (m + 3 + 1) = 2 * 2 ^ (m + 3) := by ring
    omega

#print axioms two_pow_add_three_lt_choose_two_mul_add_five

/-- For every $n \ge 5$, the conjectured value $2^{n-2} + 1$ is strictly smaller than `tothValtrUpper n`. -/
theorem conjectured_lt_tothValtrUpper_of_ge_five {n : ℕ} (hn : 5 ≤ n) :
    erdosSzekeresConjectured n < tothValtrUpper n := by
  dsimp [erdosSzekeresConjectured, tothValtrUpper]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h1 : m + 5 - 2 = m + 3 := by omega
  have h2 : 2 * (m + 5) - 5 = 2 * m + 5 := by omega
  rw [h1, h2]
  have hlt := two_pow_add_three_lt_choose_two_mul_add_five m
  omega

#print axioms conjectured_lt_tothValtrUpper_of_ge_five

/-- Universal strict hierarchy for $n \ge 5$:
$2^{n-2} + 1 < \binom{2n-5}{n-2} + 1 < \binom{2n-4}{n-2} + 1$. -/
theorem conjectured_lt_tothValtr_lt_erdosSzekeres_of_ge_five {n : ℕ} (hn : 5 ≤ n) :
    erdosSzekeresConjectured n < tothValtrUpper n ∧
      tothValtrUpper n < erdosSzekeresUpper n :=
  ⟨conjectured_lt_tothValtrUpper_of_ge_five hn,
    tothValtrUpper_lt_erdosSzekeresUpper_of_ge_four (by omega)⟩

#print axioms conjectured_lt_tothValtr_lt_erdosSzekeres_of_ge_five

/-- Conditional closure of the 5-point Happy Ending theorem: once $5 \in \text{cardSet}(4)$ is supplied,
$f(4) = 5 = 2^{4-2} + 1$ follows immediately by combining `Nat.sInf_le` with our unconditional
4-point lower bound `five_le_f_four`. -/
theorem f_four_eq_five_of_mem_cardSet (h5 : (5 : ℕ) ∈ cardSet 4) :
    f 4 = 5 ∧ f 4 = erdosSzekeresConjectured 4 := by
  have hle : f 4 ≤ 5 := Nat.sInf_le h5
  have hge : 5 ≤ f 4 := five_le_f_four ⟨5, h5⟩
  have heq : f 4 = 5 := le_antisymm hle hge
  exact ⟨heq, heq⟩

#print axioms f_four_eq_five_of_mem_cardSet

/-- Conditional bridge from `erdosSzekeresUpper n ∈ cardSet n` to `f n ≤ erdosSzekeresUpper n`. -/
theorem f_le_erdosSzekeresUpper_of_mem_cardSet {n : ℕ}
    (hmem : erdosSzekeresUpper n ∈ cardSet n) :
    f n ≤ erdosSzekeresUpper n :=
  Nat.sInf_le hmem

#print axioms f_le_erdosSzekeresUpper_of_mem_cardSet


/-!
# Universal 5-Point Line-Separation Pigeonhole, 3-Outer + 2-Interior Convex 4-Gons, and 4-Cup / 4-Cap Convexity (#107)

This module develops the universal 5-point line-separation pigeonhole reduction and bridges 4-point cups and caps in
$x$-monotone sequences to `ConvexIndep` and `HasConvexNGon 4`:

1. **Oriented Cross-Product Functional (`lineSide`) and Unconditional Collinearity Criterion**:
   - Defines the signed 2D area functional `lineSide p q r` and its affine-linear decomposition
     `lineNormX p q * r 0 + lineNormY p q * r 1 = lineConst p q + lineSide p q r`.
   - Proves alternating/cyclic permutation laws (`lineSide_swap_left`, `lineSide_swap_right`,
     `lineSide_cycle`) and removes the $p_0 \ne q_0$ coordinate restriction from collinearity,
     establishing unconditionally that `lineSide p q r = 0 → Collinear ℝ {p, q, r}`
     (`collinear_of_lineSide_eq_zero`) and `¬ Collinear ℝ {p, q, r} → 0 < lineSide p q r ∨ lineSide p q r < 0`
     (`lineSide_pos_or_neg_of_not_collinear`).

2. **Crossing-Diagonal Separation, Mutual Open-Side Quadrilaterals, and the Universal 5-Point Pigeonhole Lemma**:
   - Proves that any directed line $a \to b$ with `lineSide a b c ≤ 0` and `0 < lineSide a b d`
     strictly separates $d$ from $\{a, b, c\}$ (`lineSide_sep_of_neg_pos`).
   - Deduces that opposite-side crossing diagonals certify `ConvexIndep` (`convexIndep_four_of_opposite_diagonals`)
     and that any 4 points $a, b, p, q$ where $p, q$ lie on the positive open side of $a \to b$ while $a, b$
     lie on the same open side of $p \leftrightarrow q$ form a convex quadrilateral (`convexIndep_four_of_same_open_side`).
   - Proves the universal 5-point line-separation pigeonhole theorem (`three_vertices_same_open_side_of_line`)
     and the universal 3-outer + 2-interior Happy Ending theorem (`hasConvexFourGon_of_triangle_two_interior`).

3. **Universal 4-Cup and 4-Cap Convex Independence and Unconditional 7-Point Convex 4-Gon Theorem**:
   - Proves the exact 4-point secant syzygies (`lineSide_four_step_syzygy_left`, `lineSide_four_step_syzygy_right`),
     slope transitivity (`slopeLt_trans_left_and_right`), and universal convex independence of every 4-cup
     (`cup_four_convexIndep`) and every 4-cap (`cap_four_convexIndep`).
   - Combines `cup_four_convexIndep`, `cap_four_convexIndep`, and `erdos_szekeres_diagonal_cup_cap` to prove
     unconditionally that any $x$-monotone non-trilinear set of size at least `erdosSzekeresUpper 4 = 7`
     contains a convex 4-gon (`erdos_szekeres_seven_points_hasConvexFourGon`).

4. **Tóth–Valtr Asymmetric Cup–Cap Reduction**:
   - Proves `tothValtrUpper n = cupCapBound (n - 1) n = cupCapBound n (n - 1)` for all $n \ge 3$ and deduces
     the asymmetric cup-cap guarantee `HasCup P S (n - 3) ∨ HasCap P S (n - 2)` (`tothValtr_asymmetric_cup_cap`).
-/

/-! ## Section 1: Oriented Cross-Product Functional and Unconditional Collinearity Criterion -/

/-- Signed 2D area (oriented cross product) of the triple $(p, q, r)$ in $\mathbb{R}^2$. -/
def lineSide (p q r : ℝ²) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- First coordinate of the normal vector to the directed line $p \to q$. -/
def lineNormX (p q : ℝ²) : ℝ :=
  -(q 1 - p 1)

/-- Second coordinate of the normal vector to the directed line $p \to q$. -/
def lineNormY (p q : ℝ²) : ℝ :=
  q 0 - p 0

/-- Affine constant of the directed line $p \to q$. -/
def lineConst (p q : ℝ²) : ℝ :=
  p 1 * q 0 - p 0 * q 1

/-- The oriented cross product vanishes at the first base point $p$. -/
theorem lineSide_self_left (p q : ℝ²) : lineSide p q p = 0 := by
  dsimp [lineSide]
  ring

#print axioms lineSide_self_left

/-- The oriented cross product vanishes at the second base point $q$. -/
theorem lineSide_self_right (p q : ℝ²) : lineSide p q q = 0 := by
  dsimp [lineSide]
  ring

#print axioms lineSide_self_right

/-- Swapping the two base points negates `lineSide`. -/
theorem lineSide_swap_left (p q r : ℝ²) : lineSide q p r = - lineSide p q r := by
  dsimp [lineSide]
  ring

#print axioms lineSide_swap_left

/-- Swapping the second and third points negates `lineSide`. -/
theorem lineSide_swap_right (p q r : ℝ²) : lineSide p r q = - lineSide p q r := by
  dsimp [lineSide]
  ring

#print axioms lineSide_swap_right

/-- Cyclic permutation of $(p, q, r)$ preserves `lineSide`. -/
theorem lineSide_cycle (p q r : ℝ²) : lineSide q r p = lineSide p q r := by
  dsimp [lineSide]
  ring

#print axioms lineSide_cycle

/-- Universal affine-linear decomposition of `lineSide p q r` in the test point $r$. -/
theorem lineSide_affine_decomp (p q r : ℝ²) :
    lineNormX p q * r 0 + lineNormY p q * r 1 = lineConst p q + lineSide p q r := by
  dsimp [lineNormX, lineNormY, lineConst, lineSide]
  ring

#print axioms lineSide_affine_decomp

/-- Unconditional converse of `cross_eq_zero_of_collinear`: vanishing `lineSide p q r = 0`
implies `Collinear ℝ {p, q, r}` for all $p, q, r \in \mathbb{R}^2$ without any coordinate restriction. -/
theorem collinear_of_lineSide_eq_zero {p q r : ℝ²} (h : lineSide p q r = 0) :
    Collinear ℝ ({p, q, r} : Set ℝ²) := by
  by_cases hpq0 : p 0 = q 0
  · by_cases hpq1 : p 1 = q 1
    · have hpq : p = q := by
        ext i
        fin_cases i
        · exact hpq0
        · exact hpq1
      subst hpq
      have hpair : ({p, p, r} : Set ℝ²) = ({p, r} : Set ℝ²) := by ext; simp
      rw [hpair]
      exact collinear_pair ℝ p r
    · rw [collinear_iff_of_mem (by simp : p ∈ ({p, q, r} : Set ℝ²))]
      refine ⟨q - p, fun x hx => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hqp1 : q 1 - p 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq1)
      have hr0 : r 0 = p 0 := by
        dsimp [lineSide] at h
        have h0 : q 0 - p 0 = 0 := by linarith
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact False.elim (hqp1 h1)
        · linarith
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(x 1 - p 1) / (q 1 - p 1), ?_⟩
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
            PiLp.sub_apply, smul_eq_mul]
          have hsub0 : q 0 - p 0 = 0 := by linarith
          rw [hsub0, mul_zero, zero_add]
          linarith
        · simp only [Fin.mk_one, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
            PiLp.sub_apply, smul_eq_mul]
          have hmul : (x 1 - p 1) / (q 1 - p 1) * (q 1 - p 1) = x 1 - p 1 :=
            div_mul_cancel₀ _ hqp1
          linarith
  · exact collinear_of_cross_eq_zero hpq0 h

#print axioms collinear_of_lineSide_eq_zero

/-- Any three non-collinear points in $\mathbb{R}^2$ have strictly positive or strictly negative `lineSide`. -/
theorem lineSide_pos_or_neg_of_not_collinear {p q r : ℝ²}
    (hnc : ¬ Collinear ℝ ({p, q, r} : Set ℝ²)) :
    0 < lineSide p q r ∨ lineSide p q r < 0 := by
  rcases lt_trichotomy 0 (lineSide p q r) with hpos | heq | hneg
  · exact Or.inl hpos
  · exact False.elim (hnc (collinear_of_lineSide_eq_zero heq.symm))
  · exact Or.inr hneg

#print axioms lineSide_pos_or_neg_of_not_collinear

/-! ## Section 2: Crossing-Diagonal Separation, Mutual Open-Side Quadrilaterals, and Universal 5-Point Pigeonhole -/

/-- If $c$ lies on the non-positive side of the directed line $a \to b$ and $d$ lies on its
strictly positive side, then the affine functional of $a \to b$ strictly separates $d$ from $\{a, b, c\}$. -/
theorem lineSide_sep_of_neg_pos {a b c d : ℝ²}
    (hc : lineSide a b c ≤ 0) (hd : 0 < lineSide a b d) :
    ∃ u v k : ℝ,
      u * a 0 + v * a 1 ≤ k ∧
      u * b 0 + v * b 1 ≤ k ∧
      u * c 0 + v * c 1 ≤ k ∧
      k < u * d 0 + v * d 1 := by
  refine ⟨lineNormX a b, lineNormY a b, lineConst a b, ?_, ?_, ?_, ?_⟩
  · rw [lineSide_affine_decomp, lineSide_self_left]; linarith
  · rw [lineSide_affine_decomp, lineSide_self_right]; linarith
  · rw [lineSide_affine_decomp]; linarith
  · rw [lineSide_affine_decomp]; linarith

#print axioms lineSide_sep_of_neg_pos

/-- **Universal Crossing-Diagonal Convex Quadrilateral Criterion**:
If the diagonal $p_1 p_3$ strictly separates $p_2$ and $p_4$ and the diagonal $p_2 p_4$ strictly
separates $p_1$ and $p_3$, then $\{p_1, p_2, p_3, p_4\}$ is convex independent. -/
theorem convexIndep_four_of_opposite_diagonals {p₁ p₂ p₃ p₄ : ℝ²}
    (hd₁ : lineSide p₁ p₃ p₄ < 0 ∧ 0 < lineSide p₁ p₃ p₂)
    (hd₂ : lineSide p₂ p₄ p₁ < 0 ∧ 0 < lineSide p₂ p₄ p₃) :
    ConvexIndep ({p₁, p₂, p₃, p₄} : Set ℝ²) := by
  apply convexIndep_four_of_strict_sep
  · have hc : lineSide p₄ p₂ p₃ ≤ 0 := by
      rw [lineSide_swap_left]; linarith [hd₂.2]
    have hd : 0 < lineSide p₄ p₂ p₁ := by
      rw [lineSide_swap_left]; linarith [hd₂.1]
    rcases lineSide_sep_of_neg_pos hc hd with ⟨u, v, k, h₄, h₂, h₃, h₁⟩
    exact ⟨u, v, k, h₂, h₃, h₄, h₁⟩
  · rcases lineSide_sep_of_neg_pos (le_of_lt hd₁.1) hd₁.2 with ⟨u, v, k, h₁, h₃, h₄, h₂⟩
    exact ⟨u, v, k, h₁, h₃, h₄, h₂⟩
  · rcases lineSide_sep_of_neg_pos (le_of_lt hd₂.1) hd₂.2 with ⟨u, v, k, h₂, h₄, h₁, h₃⟩
    exact ⟨u, v, k, h₁, h₂, h₄, h₃⟩
  · have hc : lineSide p₃ p₁ p₂ ≤ 0 := by
      rw [lineSide_swap_left]; linarith [hd₁.2]
    have hd : 0 < lineSide p₃ p₁ p₄ := by
      rw [lineSide_swap_left]; linarith [hd₁.1]
    rcases lineSide_sep_of_neg_pos hc hd with ⟨u, v, k, h₃, h₁, h₂, h₄⟩
    exact ⟨u, v, k, h₁, h₂, h₃, h₄⟩

#print axioms convexIndep_four_of_opposite_diagonals

/-- If $p, q$ lie on the positive open side of $a \to b$ and $a, b$ lie on the positive open side
of $p \to q$, then $\{a, b, p, q\}$ is convex independent. -/
theorem convexIndep_four_of_pos_same_open_side {a b p q : ℝ²}
    (habp : 0 < lineSide a b p) (habq : 0 < lineSide a b q)
    (hpqa : 0 < lineSide p q a) (hpqb : 0 < lineSide p q b) :
    ConvexIndep ({a, b, p, q} : Set ℝ²) := by
  have hset : ({a, b, p, q} : Set ℝ²) = ({a, q, p, b} : Set ℝ²) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  apply convexIndep_four_of_opposite_diagonals
  · refine ⟨?_, ?_⟩
    · have h : lineSide a p b = - lineSide a b p := by
        dsimp [lineSide]; ring
      linarith
    · have h : lineSide a p q = lineSide p q a := by
        dsimp [lineSide]; ring
      linarith
  · refine ⟨?_, ?_⟩
    · have h : lineSide q b a = - lineSide a b q := by
        dsimp [lineSide]; ring
      linarith
    · have h : lineSide q b p = lineSide p q b := by
        dsimp [lineSide]; ring
      linarith

#print axioms convexIndep_four_of_pos_same_open_side

/-- **Universal Mutual Open-Side Convex Quadrilateral Theorem**:
If $p, q$ lie on the positive open side of $a \to b$ and $a, b$ lie on the same open side
of $p \leftrightarrow q$ (either both positive or both negative), then $\{a, b, p, q\}$ is convex independent. -/
theorem convexIndep_four_of_same_open_side {a b p q : ℝ²}
    (habp : 0 < lineSide a b p) (habq : 0 < lineSide a b q)
    (hsame : (0 < lineSide p q a ∧ 0 < lineSide p q b) ∨
      (lineSide p q a < 0 ∧ lineSide p q b < 0)) :
    ConvexIndep ({a, b, p, q} : Set ℝ²) := by
  rcases hsame with ⟨hpqa, hpqb⟩ | ⟨hpqa, hpqb⟩
  · exact convexIndep_four_of_pos_same_open_side habp habq hpqa hpqb
  · have hset : ({a, b, p, q} : Set ℝ²) = ({a, b, q, p} : Set ℝ²) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    apply convexIndep_four_of_pos_same_open_side habq habp
    · rw [lineSide_swap_left]; linarith
    · rw [lineSide_swap_left]; linarith

#print axioms convexIndep_four_of_same_open_side

/-- **Universal 3-Sign Pigeonhole Principle**:
Among any three nonzero real numbers $x, y, z$, at least one of the three pairs
$(x, y)$, $(y, z)$, $(z, x)$ shares the same strict sign. -/
theorem pigeonhole_three_signs {x y z : ℝ}
    (hx : 0 < x ∨ x < 0) (hy : 0 < y ∨ y < 0) (hz : 0 < z ∨ z < 0) :
    ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∨
    ((0 < y ∧ 0 < z) ∨ (y < 0 ∧ z < 0)) ∨
    ((0 < z ∧ 0 < x) ∨ (z < 0 ∧ x < 0)) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact Or.inl (Or.inl ⟨hx, hy⟩)
  · exact Or.inl (Or.inl ⟨hx, hy⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hz, hx⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hy, hz⟩))
  · exact Or.inr (Or.inl (Or.inl ⟨hy, hz⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, hx⟩))
  · exact Or.inl (Or.inr ⟨hx, hy⟩)
  · exact Or.inl (Or.inr ⟨hx, hy⟩)

#print axioms pigeonhole_three_signs

/-- **Universal 5-Point Line-Separation Pigeonhole Lemma**:
For any two points $p, q \in \mathbb{R}^2$ and any three points $a, b, c \in \mathbb{R}^2$ each
non-collinear with $\{p, q\}$, at least two of $\{a, b, c\}$ lie on the same open side of the line $pq$. -/
theorem three_vertices_same_open_side_of_line {p q a b c : ℝ²}
    (ha : ¬ Collinear ℝ ({p, q, a} : Set ℝ²))
    (hb : ¬ Collinear ℝ ({p, q, b} : Set ℝ²))
    (hc : ¬ Collinear ℝ ({p, q, c} : Set ℝ²)) :
    ((0 < lineSide p q a ∧ 0 < lineSide p q b) ∨ (lineSide p q a < 0 ∧ lineSide p q b < 0)) ∨
    ((0 < lineSide p q b ∧ 0 < lineSide p q c) ∨ (lineSide p q b < 0 ∧ lineSide p q c < 0)) ∨
    ((0 < lineSide p q c ∧ 0 < lineSide p q a) ∨ (lineSide p q c < 0 ∧ lineSide p q a < 0)) :=
  pigeonhole_three_signs
    (lineSide_pos_or_neg_of_not_collinear ha)
    (lineSide_pos_or_neg_of_not_collinear hb)
    (lineSide_pos_or_neg_of_not_collinear hc)

#print axioms three_vertices_same_open_side_of_line

/-- Any two outer vertices $u, v \in P$ and two distinct points $p, q \in P$ lying on the positive open
side of $u \to v$ such that $u, v$ lie on the same open side of $p \leftrightarrow q$ form a convex 4-gon in $P$. -/
theorem hasConvexFourGon_of_same_open_side_edge {P : Set ℝ²} {u v p q : ℝ²}
    (huP : u ∈ P) (hvP : v ∈ P) (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (huvp : 0 < lineSide u v p) (huvq : 0 < lineSide u v q)
    (hsame : (0 < lineSide p q u ∧ 0 < lineSide p q v) ∨
      (lineSide p q u < 0 ∧ lineSide p q v < 0)) :
    HasConvexNGon 4 P := by
  have huv : u ≠ v := by
    intro h; subst h; dsimp [lineSide] at huvp; linarith
  have hup : u ≠ p := by
    intro h; subst h; dsimp [lineSide] at huvp; linarith
  have huq : u ≠ q := by
    intro h; subst h; dsimp [lineSide] at huvq; linarith
  have hvp : v ≠ p := by
    intro h; subst h; dsimp [lineSide] at huvp; linarith
  have hvq : v ≠ q := by
    intro h; subst h; dsimp [lineSide] at huvq; linarith
  refine ⟨{u, v, p, q}, ?_, ?_, ?_⟩
  · simp [huv, hup, huq, hvp, hvq, hpq]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · simpa using convexIndep_four_of_same_open_side huvp huvq hsame

#print axioms hasConvexFourGon_of_same_open_side_edge

/-- **Universal 5-Point 3-Outer + 2-Interior Happy Ending Theorem**:
In any point set $P \subseteq \mathbb{R}^2$, if $a, b, c \in P$ form a positively oriented triangle
containing two distinct interior points $p, q \in P$ such that none of $a, b, c$ is collinear with
$\{p, q\}$, then $P$ contains the vertices of a convex 4-gon (`HasConvexNGon 4 P`). -/
theorem hasConvexFourGon_of_triangle_two_interior {P : Set ℝ²} {a b c p q : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (habp : 0 < lineSide a b p) (habq : 0 < lineSide a b q)
    (hbcp : 0 < lineSide b c p) (hbcq : 0 < lineSide b c q)
    (hcap : 0 < lineSide c a p) (hcaq : 0 < lineSide c a q)
    (hnca : ¬ Collinear ℝ ({p, q, a} : Set ℝ²))
    (hncb : ¬ Collinear ℝ ({p, q, b} : Set ℝ²))
    (hncc : ¬ Collinear ℝ ({p, q, c} : Set ℝ²)) :
    HasConvexNGon 4 P := by
  rcases three_vertices_same_open_side_of_line hnca hncb hncc with hab | hbc | hca
  · exact hasConvexFourGon_of_same_open_side_edge haP hbP hpP hqP hpq habp habq hab
  · exact hasConvexFourGon_of_same_open_side_edge hbP hcP hpP hqP hpq hbcp hbcq hbc
  · exact hasConvexFourGon_of_same_open_side_edge hcP haP hpP hqP hpq hcap hcaq hca

#print axioms hasConvexFourGon_of_triangle_two_interior

/-! ## Section 3: Universal 4-Cup and 4-Cap Convex Independence and 7-Point Convex 4-Gon Theorem -/

/-- `slopeLt a b c` is equivalent to `0 < lineSide a b c`. -/
theorem slopeLt_iff_lineSide_pos (a b c : ℝ²) :
    slopeLt a b c ↔ 0 < lineSide a b c := by
  dsimp [slopeLt, lineSide]
  constructor <;> intro h <;> linarith

#print axioms slopeLt_iff_lineSide_pos

/-- `slopeGt a b c` is equivalent to `lineSide a b c < 0`. -/
theorem slopeGt_iff_lineSide_neg (a b c : ℝ²) :
    slopeGt a b c ↔ lineSide a b c < 0 := by
  dsimp [slopeGt, lineSide]
  constructor <;> intro h <;> linarith

#print axioms slopeGt_iff_lineSide_neg

/-- Universal 4-point secant syzygy for `lineSide a b d` in terms of `lineSide a b c` and `lineSide b c d`. -/
theorem lineSide_four_step_syzygy_left (a b c d : ℝ²) :
    (c 0 - b 0) * lineSide a b d =
      (d 0 - b 0) * lineSide a b c + (b 0 - a 0) * lineSide b c d := by
  dsimp [lineSide]
  ring

#print axioms lineSide_four_step_syzygy_left

/-- Universal 4-point secant syzygy for `lineSide a c d` in terms of `lineSide a b c` and `lineSide b c d`. -/
theorem lineSide_four_step_syzygy_right (a b c d : ℝ²) :
    (c 0 - b 0) * lineSide a c d =
      (d 0 - c 0) * lineSide a b c + (c 0 - a 0) * lineSide b c d := by
  dsimp [lineSide]
  ring

#print axioms lineSide_four_step_syzygy_right

/-- Slope-turn transitivity on 4 points with $a_0 < b_0 < c_0 < d_0$:
if $(a, b, c)$ and $(b, c, d)$ are strict cup turns, then $(a, b, d)$ and $(a, c, d)$ are strict cup turns. -/
theorem slopeLt_trans_left_and_right {a b c d : ℝ²}
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (h₁ : slopeLt a b c) (h₂ : slopeLt b c d) :
    slopeLt a b d ∧ slopeLt a c d := by
  rw [slopeLt_iff_lineSide_pos] at h₁ h₂ ⊢
  rw [slopeLt_iff_lineSide_pos]
  have hcb : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hdb : 0 < d 0 - b 0 := by linarith
  have hba : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hdc : 0 < d 0 - c 0 := sub_pos.mpr hcd
  have hca : 0 < c 0 - a 0 := by linarith
  have hsyz₁ := lineSide_four_step_syzygy_left a b c d
  have hsyz₂ := lineSide_four_step_syzygy_right a b c d
  have hpos₁ : 0 < (c 0 - b 0) * lineSide a b d := by
    rw [hsyz₁]
    positivity
  have hpos₂ : 0 < (c 0 - b 0) * lineSide a c d := by
    rw [hsyz₂]
    positivity
  exact ⟨pos_of_mul_pos_right hpos₁ (le_of_lt hcb),
    pos_of_mul_pos_right hpos₂ (le_of_lt hcb)⟩

#print axioms slopeLt_trans_left_and_right

/-- **Universal 4-Cup Convex Independence Theorem**:
Every 4-point cup $a < b < c < d$ in an $x$-monotone sequence $P$ is convex independent. -/
theorem cup_four_convexIndep {P : ℕ → ℝ²} (hmono : IsXMonotone P)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h₁ : slopeLt (P a) (P b) (P c)) (h₂ : slopeLt (P b) (P c) (P d)) :
    ConvexIndep ({P a, P b, P c, P d} : Set ℝ²) := by
  obtain ⟨habd, hacd⟩ :=
    slopeLt_trans_left_and_right (hmono hab) (hmono hbc) (hmono hcd) h₁ h₂
  rw [slopeLt_iff_lineSide_pos] at h₁ h₂ habd hacd
  apply convexIndep_four_of_pos_same_open_side h₁ habd
  · rw [lineSide_cycle]; exact hacd
  · rw [lineSide_cycle]; exact h₂

#print axioms cup_four_convexIndep

/-- **Universal 4-Cap Convex Independence Theorem**:
Every 4-point cap $a < b < c < d$ in an $x$-monotone sequence $P$ is convex independent. -/
theorem cap_four_convexIndep {P : ℕ → ℝ²} (hmono : IsXMonotone P)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h₁ : slopeGt (P a) (P b) (P c)) (h₂ : slopeGt (P b) (P c) (P d)) :
    ConvexIndep ({P a, P b, P c, P d} : Set ℝ²) := by
  rw [slopeGt_iff_lineSide_neg] at h₁ h₂
  have hcb : 0 < P c 0 - P b 0 := sub_pos.mpr (hmono hbc)
  have hdb : 0 < P d 0 - P b 0 := sub_pos.mpr (hmono (lt_trans hbc hcd))
  have hba : 0 < P b 0 - P a 0 := sub_pos.mpr (hmono hab)
  have hdc : 0 < P d 0 - P c 0 := sub_pos.mpr (hmono hcd)
  have hca : 0 < P c 0 - P a 0 := sub_pos.mpr (hmono (lt_trans hab hbc))
  have hsyz₁ := lineSide_four_step_syzygy_left (P a) (P b) (P c) (P d)
  have hsyz₂ := lineSide_four_step_syzygy_right (P a) (P b) (P c) (P d)
  have hneg₁ : (P c 0 - P b 0) * lineSide (P a) (P b) (P d) < 0 := by
    rw [hsyz₁]; nlinarith
  have hneg₂ : (P c 0 - P b 0) * lineSide (P a) (P c) (P d) < 0 := by
    rw [hsyz₂]; nlinarith
  have habd : lineSide (P a) (P b) (P d) < 0 := by nlinarith
  have hacd : lineSide (P a) (P c) (P d) < 0 := by nlinarith
  have hset : ({P a, P b, P c, P d} : Set ℝ²) = ({P b, P a, P c, P d} : Set ℝ²) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  apply convexIndep_four_of_same_open_side
  · rw [lineSide_swap_left]; linarith
  · rw [lineSide_swap_left]; linarith
  · right
    refine ⟨?_, ?_⟩
    · rw [lineSide_cycle]; exact h₂
    · rw [lineSide_cycle]; exact hacd

#print axioms cap_four_convexIndep

/-- Any $x$-monotone sequence $P$ on a finite index set $S$ with `HasCup P S 2 ∨ HasCap P S 2`
contains a convex 4-gon in its image $P(S)$. -/
theorem hasConvexFourGon_of_hasCup_or_hasCap_two {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (h : HasCup P S 2 ∨ HasCap P S 2) :
    HasConvexNGon 4 (P '' (S : Set ℕ)) := by
  rcases h with ⟨c, d, hcS, hdS, hcd, b, ⟨hbS, _, hbc, a, ⟨haS, _, hab⟩, hsl₁⟩, hsl₂⟩ |
    ⟨a, b, haS, hbS, hab, c, hsg₁, ⟨_, hcS, hbc, d, hsg₂, ⟨_, hdS, hcd⟩⟩⟩
  · have hac : a < c := lt_trans hab hbc
    have had : a < d := lt_trans hac hcd
    have hbd : b < d := lt_trans hbc hcd
    have hne_ab := xMonotone_ne_of_lt hmono hab
    have hne_ac := xMonotone_ne_of_lt hmono hac
    have hne_ad := xMonotone_ne_of_lt hmono had
    have hne_bc := xMonotone_ne_of_lt hmono hbc
    have hne_bd := xMonotone_ne_of_lt hmono hbd
    have hne_cd := xMonotone_ne_of_lt hmono hcd
    refine ⟨{P a, P b, P c, P d}, ?_, ?_, ?_⟩
    · simp [hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd]
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨a, haS, rfl⟩
      · exact ⟨b, hbS, rfl⟩
      · exact ⟨c, hcS, rfl⟩
      · exact ⟨d, hdS, rfl⟩
    · simpa using cup_four_convexIndep hmono hab hbc hcd hsl₁ hsl₂
  · have hac : a < c := lt_trans hab hbc
    have had : a < d := lt_trans hac hcd
    have hbd : b < d := lt_trans hbc hcd
    have hne_ab := xMonotone_ne_of_lt hmono hab
    have hne_ac := xMonotone_ne_of_lt hmono hac
    have hne_ad := xMonotone_ne_of_lt hmono had
    have hne_bc := xMonotone_ne_of_lt hmono hbc
    have hne_bd := xMonotone_ne_of_lt hmono hbd
    have hne_cd := xMonotone_ne_of_lt hmono hcd
    refine ⟨{P a, P b, P c, P d}, ?_, ?_, ?_⟩
    · simp [hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd]
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨a, haS, rfl⟩
      · exact ⟨b, hbS, rfl⟩
      · exact ⟨c, hcS, rfl⟩
      · exact ⟨d, hdS, rfl⟩
    · simpa using cap_four_convexIndep hmono hab hbc hcd hsg₁ hsg₂

#print axioms hasConvexFourGon_of_hasCup_or_hasCap_two

/-- **Unconditional 7-Point Erdős–Szekeres Convex 4-Gon Theorem**:
Every $x$-monotone non-trilinear finite point sequence $P$ on an index set $S$ of cardinality
at least `erdosSzekeresUpper 4` ($= \binom{4}{2} + 1 = 7$) contains the vertices of a convex 4-gon. -/
theorem erdos_szekeres_seven_points_hasConvexFourGon {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : erdosSzekeresUpper 4 ≤ S.card) :
    HasConvexNGon 4 (P '' (S : Set ℕ)) :=
  hasConvexFourGon_of_hasCup_or_hasCap_two hmono
    (erdos_szekeres_diagonal_cup_cap hmono hnontri (by decide : 2 ≤ 4) S hcard)

#print axioms erdos_szekeres_seven_points_hasConvexFourGon

/-! ## Section 4: Tóth–Valtr Asymmetric Cup–Cap Reduction -/

/-- For every $n \ge 3$, the Tóth–Valtr bound `tothValtrUpper n` equals both asymmetric
off-diagonal cup-cap thresholds `cupCapBound (n - 1) n` and `cupCapBound n (n - 1)`. -/
theorem tothValtrUpper_eq_cupCapBound_asymmetric {n : ℕ} (hn : 3 ≤ n) :
    tothValtrUpper n = cupCapBound (n - 1) n ∧
      tothValtrUpper n = cupCapBound n (n - 1) := by
  have hright : tothValtrUpper n = cupCapBound n (n - 1) := by
    dsimp [tothValtrUpper, cupCapBound]
    have h : 2 * n - 5 = n + (n - 1) - 4 := by omega
    rw [h]
  have hsymm : cupCapBound (n - 1) n = cupCapBound n (n - 1) :=
    cupCapBound_symm (by omega) (by omega)
  exact ⟨hright.trans hsymm.symm, hright⟩

#print axioms tothValtrUpper_eq_cupCapBound_asymmetric

/-- **Tóth–Valtr Asymmetric Cup–Cap Theorem**:
In any $x$-monotone non-trilinear sequence $P$, any finite index set $S$ of cardinality at least
`tothValtrUpper n` ($n \ge 3$) contains either an $(n - 1)$-cup (`HasCup P S (n - 3)`)
or an $n$-cap (`HasCap P S (n - 2)`). -/
theorem tothValtr_asymmetric_cup_cap {P : ℕ → ℝ²}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    {n : ℕ} (hn : 3 ≤ n) (S : Finset ℕ)
    (hcard : tothValtrUpper n ≤ S.card) :
    HasCup P S (n - 3) ∨ HasCap P S (n - 2) := by
  rw [(tothValtrUpper_eq_cupCapBound_asymmetric hn).1] at hcard
  have h := erdos_szekeres_cup_cap_of_ge_two hmono hnontri (r := n - 1) (s := n)
    (by omega) (by omega) S hcard
  have hsub : n - 1 - 2 = n - 3 := by omega
  rw [hsub] at h
  exact h

#print axioms tothValtr_asymmetric_cup_cap

/-- At $n = 5$, any $x$-monotone non-trilinear sequence $P$ on an index set $S$ of cardinality
at least `tothValtrUpper 5` ($= 11$) contains either a convex 4-gon in $P(S)$ or a 5-cap. -/
theorem tothValtr_eleven_points_hasConvexFourGon_or_fiveCap {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : tothValtrUpper 5 ≤ S.card) :
    HasConvexNGon 4 (P '' (S : Set ℕ)) ∨ HasCap P S 3 := by
  rcases tothValtr_asymmetric_cup_cap hmono hnontri (by decide : 3 ≤ 5) S hcard with hcup | hcap
  · exact Or.inl (hasConvexFourGon_of_hasCup_or_hasCap_two hmono (Or.inl hcup))
  · exact Or.inr hcap

#print axioms tothValtr_eleven_points_hasConvexFourGon_or_fiveCap


/-! ## Section 1: Universal 5-Point Strict Separation & 5-Cup / 5-Cap All-Triple Orientation Theorems -/

/-- Universal 5-point strict affine separation criterion for `ConvexIndep` in $\mathbb{R}^2$. -/
theorem convexIndep_five_of_strict_sep {p₁ p₂ p₃ p₄ p₅ : ℝ²}
    (h₁ : ∃ u v c : ℝ, u * p₂ 0 + v * p₂ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₁ 0 + v * p₁ 1)
    (h₂ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₂ 0 + v * p₂ 1)
    (h₃ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₃ 0 + v * p₃ 1)
    (h₄ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₄ 0 + v * p₄ 1)
    (h₅ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₅ 0 + v * p₅ 1) :
    ConvexIndep ({p₁, p₂, p₃, p₄, p₅} : Set ℝ²) := by
  apply convexIndep_of_pointwise_strict_sep
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rcases h₁ with ⟨u, v, c, hp₂, hp₃, hp₄, hp₅, hp₁⟩
    refine ⟨u, v, c, ?_, hp₁⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hy_ne rfl)
    · exact hp₂
    · exact hp₃
    · exact hp₄
    · exact hp₅
  · rcases h₂ with ⟨u, v, c, hp₁, hp₃, hp₄, hp₅, hp₂⟩
    refine ⟨u, v, c, ?_, hp₂⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl | rfl
    · exact hp₁
    · exact False.elim (hy_ne rfl)
    · exact hp₃
    · exact hp₄
    · exact hp₅
  · rcases h₃ with ⟨u, v, c, hp₁, hp₂, hp₄, hp₅, hp₃⟩
    refine ⟨u, v, c, ?_, hp₃⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact False.elim (hy_ne rfl)
    · exact hp₄
    · exact hp₅
  · rcases h₄ with ⟨u, v, c, hp₁, hp₂, hp₃, hp₅, hp₄⟩
    refine ⟨u, v, c, ?_, hp₄⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact hp₃
    · exact False.elim (hy_ne rfl)
    · exact hp₅
  · rcases h₅ with ⟨u, v, c, hp₁, hp₂, hp₃, hp₄, hp₅⟩
    refine ⟨u, v, c, ?_, hp₅⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact hp₃
    · exact hp₄
    · exact False.elim (hy_ne rfl)

#print axioms convexIndep_five_of_strict_sep

/-- Universal 5-extreme-point reduction: any point set $P \subseteq \mathbb{R}^2$ containing five
pairwise distinct points that are each strictly separated from the other four contains a convex pentagon. -/
theorem hasConvexFiveGon_of_five_extreme {P : Set ℝ²} {p₁ p₂ p₃ p₄ p₅ : ℝ²}
    (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (hp₃ : p₃ ∈ P) (hp₄ : p₄ ∈ P) (hp₅ : p₅ ∈ P)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₁₄ : p₁ ≠ p₄) (h₁₅ : p₁ ≠ p₅)
    (h₂₃ : p₂ ≠ p₃) (h₂₄ : p₂ ≠ p₄) (h₂₅ : p₂ ≠ p₅)
    (h₃₄ : p₃ ≠ p₄) (h₃₅ : p₃ ≠ p₅) (h₄₅ : p₄ ≠ p₅)
    (hsep₁ : ∃ u v c : ℝ, u * p₂ 0 + v * p₂ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₁ 0 + v * p₁ 1)
    (hsep₂ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₂ 0 + v * p₂ 1)
    (hsep₃ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₃ 0 + v * p₃ 1)
    (hsep₄ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ u * p₅ 0 + v * p₅ 1 ≤ c ∧ c < u * p₄ 0 + v * p₄ 1)
    (hsep₅ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₅ 0 + v * p₅ 1) :
    HasConvexNGon 5 P := by
  refine ⟨{p₁, p₂, p₃, p₄, p₅}, ?_, ?_, ?_⟩
  · simp [h₁₂, h₁₃, h₁₄, h₁₅, h₂₃, h₂₄, h₂₅, h₃₄, h₃₅, h₄₅]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · simpa using convexIndep_five_of_strict_sep hsep₁ hsep₂ hsep₃ hsep₄ hsep₅

#print axioms hasConvexFiveGon_of_five_extreme

/-- If $c, d$ lie on the non-positive side of the directed line $a \to b$ and $e$ lies on its
strictly positive side, then the affine functional of $a \to b$ strictly separates $e$ from $\{a, b, c, d\}$. -/
theorem lineSide_sep_five_of_le_pos {a b c d e : ℝ²}
    (hc : lineSide a b c ≤ 0) (hd : lineSide a b d ≤ 0) (he : 0 < lineSide a b e) :
    ∃ u v k : ℝ,
      u * a 0 + v * a 1 ≤ k ∧
      u * b 0 + v * b 1 ≤ k ∧
      u * c 0 + v * c 1 ≤ k ∧
      u * d 0 + v * d 1 ≤ k ∧
      k < u * e 0 + v * e 1 := by
  refine ⟨lineNormX a b, lineNormY a b, lineConst a b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lineSide_affine_decomp, lineSide_self_left]; linarith
  · rw [lineSide_affine_decomp, lineSide_self_right]; linarith
  · rw [lineSide_affine_decomp]; linarith
  · rw [lineSide_affine_decomp]; linarith
  · rw [lineSide_affine_decomp]; linarith

#print axioms lineSide_sep_five_of_le_pos

/-- Slope-turn transitivity on 4 points with $a_0 < b_0 < c_0 < d_0$ for cap turns:
if $(a, b, c)$ and $(b, c, d)$ are strict cap turns, then $(a, b, d)$ and $(a, c, d)$ are strict cap turns. -/
theorem slopeGt_trans_left_and_right {a b c d : ℝ²}
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (h₁ : slopeGt a b c) (h₂ : slopeGt b c d) :
    slopeGt a b d ∧ slopeGt a c d := by
  rw [slopeGt_iff_lineSide_neg] at h₁ h₂ ⊢
  rw [slopeGt_iff_lineSide_neg]
  have hcb : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hdb : 0 < d 0 - b 0 := by linarith
  have hba : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hdc : 0 < d 0 - c 0 := sub_pos.mpr hcd
  have hca : 0 < c 0 - a 0 := by linarith
  have hsyz₁ := lineSide_four_step_syzygy_left a b c d
  have hsyz₂ := lineSide_four_step_syzygy_right a b c d
  have hneg₁ : (c 0 - b 0) * lineSide a b d < 0 := by rw [hsyz₁]; nlinarith
  have hneg₂ : (c 0 - b 0) * lineSide a c d < 0 := by rw [hsyz₂]; nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

#print axioms slopeGt_trans_left_and_right

/-- **Universal 5-Cup All-Triple Orientation Theorem**:
In any 5-point chain $p_1, p_2, p_3, p_4, p_5 \in \mathbb{R}^2$ with strictly increasing $x$-coordinates
and three adjacent strict cup turns, all $\binom{5}{3} = 10$ ordered triples have strictly positive `lineSide`. -/
theorem five_cup_all_triples_lineSide_pos {p₁ p₂ p₃ p₄ p₅ : ℝ²}
    (h₁₂ : p₁ 0 < p₂ 0) (h₂₃ : p₂ 0 < p₃ 0) (h₃₄ : p₃ 0 < p₄ 0) (h₄₅ : p₄ 0 < p₅ 0)
    (ht₁ : slopeLt p₁ p₂ p₃) (ht₂ : slopeLt p₂ p₃ p₄) (ht₃ : slopeLt p₃ p₄ p₅) :
    0 < lineSide p₁ p₂ p₃ ∧ 0 < lineSide p₁ p₂ p₄ ∧ 0 < lineSide p₁ p₂ p₅ ∧
    0 < lineSide p₁ p₃ p₄ ∧ 0 < lineSide p₁ p₃ p₅ ∧ 0 < lineSide p₁ p₄ p₅ ∧
    0 < lineSide p₂ p₃ p₄ ∧ 0 < lineSide p₂ p₃ p₅ ∧ 0 < lineSide p₂ p₄ p₅ ∧
    0 < lineSide p₃ p₄ p₅ := by
  obtain ⟨h124, h134⟩ := slopeLt_trans_left_and_right h₁₂ h₂₃ h₃₄ ht₁ ht₂
  obtain ⟨h235, h245⟩ := slopeLt_trans_left_and_right h₂₃ h₃₄ h₄₅ ht₂ ht₃
  obtain ⟨h125, h145⟩ := slopeLt_trans_left_and_right h₁₂ (lt_trans h₂₃ h₃₄) h₄₅ h124 h245
  obtain ⟨h135, _⟩ := slopeLt_trans_left_and_right (lt_trans h₁₂ h₂₃) h₃₄ h₄₅ h134 ht₃
  rw [slopeLt_iff_lineSide_pos] at ht₁ ht₂ ht₃ h124 h134 h235 h245 h125 h145 h135
  exact ⟨ht₁, h124, h125, h134, h135, h145, ht₂, h235, h245, ht₃⟩

#print axioms five_cup_all_triples_lineSide_pos

/-- **Universal 5-Cap All-Triple Orientation Theorem**:
In any 5-point chain $p_1, p_2, p_3, p_4, p_5 \in \mathbb{R}^2$ with strictly increasing $x$-coordinates
and three adjacent strict cap turns, all $\binom{5}{3} = 10$ ordered triples have strictly negative `lineSide`. -/
theorem five_cap_all_triples_lineSide_neg {p₁ p₂ p₃ p₄ p₅ : ℝ²}
    (h₁₂ : p₁ 0 < p₂ 0) (h₂₃ : p₂ 0 < p₃ 0) (h₃₄ : p₃ 0 < p₄ 0) (h₄₅ : p₄ 0 < p₅ 0)
    (ht₁ : slopeGt p₁ p₂ p₃) (ht₂ : slopeGt p₂ p₃ p₄) (ht₃ : slopeGt p₃ p₄ p₅) :
    lineSide p₁ p₂ p₃ < 0 ∧ lineSide p₁ p₂ p₄ < 0 ∧ lineSide p₁ p₂ p₅ < 0 ∧
    lineSide p₁ p₃ p₄ < 0 ∧ lineSide p₁ p₃ p₅ < 0 ∧ lineSide p₁ p₄ p₅ < 0 ∧
    lineSide p₂ p₃ p₄ < 0 ∧ lineSide p₂ p₃ p₅ < 0 ∧ lineSide p₂ p₄ p₅ < 0 ∧
    lineSide p₃ p₄ p₅ < 0 := by
  obtain ⟨h124, h134⟩ := slopeGt_trans_left_and_right h₁₂ h₂₃ h₃₄ ht₁ ht₂
  obtain ⟨h235, h245⟩ := slopeGt_trans_left_and_right h₂₃ h₃₄ h₄₅ ht₂ ht₃
  obtain ⟨h125, h145⟩ := slopeGt_trans_left_and_right h₁₂ (lt_trans h₂₃ h₃₄) h₄₅ h124 h245
  obtain ⟨h135, _⟩ := slopeGt_trans_left_and_right (lt_trans h₁₂ h₂₃) h₃₄ h₄₅ h134 ht₃
  rw [slopeGt_iff_lineSide_neg] at ht₁ ht₂ ht₃ h124 h134 h235 h245 h125 h145 h135
  exact ⟨ht₁, h124, h125, h134, h135, h145, ht₂, h235, h245, ht₃⟩

#print axioms five_cap_all_triples_lineSide_neg

/-! ## Section 2: Universal 5-Cup and 5-Cap Convex Pentagon Forcing and Unconditional 21-Point Convex Pentagon Theorem -/

/-- **Universal 5-Cup Convex Pentagon Forcing Theorem**:
Every 5-point cup $a < b < c < d < e$ in an $x$-monotone sequence $P$ is convex independent. -/
theorem cup_five_convexIndep {P : ℕ → ℝ²} (hmono : IsXMonotone P)
    {a b c d e : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (h₁ : slopeLt (P a) (P b) (P c))
    (h₂ : slopeLt (P b) (P c) (P d))
    (h₃ : slopeLt (P c) (P d) (P e)) :
    ConvexIndep ({P a, P b, P c, P d, P e} : Set ℝ²) := by
  have hxab := hmono hab
  have hxbc := hmono hbc
  have hxcd := hmono hcd
  have hxde := hmono hde
  obtain ⟨h123, h124, _, h134, h135, _, h234, h235, h245, h345⟩ :=
    five_cup_all_triples_lineSide_pos hxab hxbc hxcd hxde h₁ h₂ h₃
  apply convexIndep_five_of_strict_sep
  · refine ⟨-1, 0, -(P b 0), by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · have hc_le : lineSide (P c) (P a) (P d) ≤ 0 := by
      have h : lineSide (P c) (P a) (P d) = - lineSide (P a) (P c) (P d) := lineSide_swap_left _ _ _
      linarith
    have hd_le : lineSide (P c) (P a) (P e) ≤ 0 := by
      have h : lineSide (P c) (P a) (P e) = - lineSide (P a) (P c) (P e) := lineSide_swap_left _ _ _
      linarith
    have hb_pos : 0 < lineSide (P c) (P a) (P b) := by
      have h : lineSide (P c) (P a) (P b) = lineSide (P a) (P b) (P c) := by
        dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos hc_le hd_le hb_pos with ⟨u, v, k, h_c, h_a, h_d, h_e, h_b⟩
    exact ⟨u, v, k, h_a, h_c, h_d, h_e, h_b⟩
  · have ha_le : lineSide (P d) (P b) (P a) ≤ 0 := by
      have h : lineSide (P d) (P b) (P a) = - lineSide (P a) (P b) (P d) := by
        dsimp [lineSide]; ring
      linarith
    have he_le : lineSide (P d) (P b) (P e) ≤ 0 := by
      have h : lineSide (P d) (P b) (P e) = - lineSide (P b) (P d) (P e) := lineSide_swap_left _ _ _
      linarith
    have hc_pos : 0 < lineSide (P d) (P b) (P c) := by
      have h : lineSide (P d) (P b) (P c) = lineSide (P b) (P c) (P d) := by
        dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos ha_le he_le hc_pos with ⟨u, v, k, h_d, h_b, h_a, h_e, h_c⟩
    exact ⟨u, v, k, h_a, h_b, h_d, h_e, h_c⟩
  · have ha_le : lineSide (P e) (P c) (P a) ≤ 0 := by
      have h : lineSide (P e) (P c) (P a) = - lineSide (P a) (P c) (P e) := by
        dsimp [lineSide]; ring
      linarith
    have hb_le : lineSide (P e) (P c) (P b) ≤ 0 := by
      have h : lineSide (P e) (P c) (P b) = - lineSide (P b) (P c) (P e) := by
        dsimp [lineSide]; ring
      linarith
    have hd_pos : 0 < lineSide (P e) (P c) (P d) := by
      have h : lineSide (P e) (P c) (P d) = lineSide (P c) (P d) (P e) := by
        dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos ha_le hb_le hd_pos with ⟨u, v, k, h_e, h_c, h_a, h_b, h_d⟩
    exact ⟨u, v, k, h_a, h_b, h_c, h_e, h_d⟩
  · refine ⟨1, 0, P d 0, by linarith, by linarith, by linarith, by linarith, by linarith⟩

#print axioms cup_five_convexIndep

/-- **Universal 5-Cap Convex Pentagon Forcing Theorem**:
Every 5-point cap $a < b < c < d < e$ in an $x$-monotone sequence $P$ is convex independent. -/
theorem cap_five_convexIndep {P : ℕ → ℝ²} (hmono : IsXMonotone P)
    {a b c d e : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (h₁ : slopeGt (P a) (P b) (P c))
    (h₂ : slopeGt (P b) (P c) (P d))
    (h₃ : slopeGt (P c) (P d) (P e)) :
    ConvexIndep ({P a, P b, P c, P d, P e} : Set ℝ²) := by
  have hxab := hmono hab
  have hxbc := hmono hbc
  have hxcd := hmono hcd
  have hxde := hmono hde
  obtain ⟨h123, h124, _, h134, h135, _, h234, h235, h245, h345⟩ :=
    five_cap_all_triples_lineSide_neg hxab hxbc hxcd hxde h₁ h₂ h₃
  apply convexIndep_five_of_strict_sep
  · refine ⟨-1, 0, -(P b 0), by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · have hd_le : lineSide (P a) (P c) (P d) ≤ 0 := le_of_lt h134
    have he_le : lineSide (P a) (P c) (P e) ≤ 0 := le_of_lt h135
    have hb_pos : 0 < lineSide (P a) (P c) (P b) := by
      have h : lineSide (P a) (P c) (P b) = - lineSide (P a) (P b) (P c) := by
        dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos hd_le he_le hb_pos with ⟨u, v, k, h_a, h_c, h_d, h_e, h_b⟩
    exact ⟨u, v, k, h_a, h_c, h_d, h_e, h_b⟩
  · have ha_le : lineSide (P b) (P d) (P a) ≤ 0 := by
      have h : lineSide (P b) (P d) (P a) = lineSide (P a) (P b) (P d) := by
        dsimp [lineSide]; ring
      linarith
    have he_le : lineSide (P b) (P d) (P e) ≤ 0 := le_of_lt h245
    have hc_pos : 0 < lineSide (P b) (P d) (P c) := by
      have h : lineSide (P b) (P d) (P c) = - lineSide (P b) (P c) (P d) := by
        dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos ha_le he_le hc_pos with ⟨u, v, k, h_b, h_d, h_a, h_e, h_c⟩
    exact ⟨u, v, k, h_a, h_b, h_d, h_e, h_c⟩
  · have ha_le : lineSide (P c) (P e) (P a) ≤ 0 := by
      have h : lineSide (P c) (P e) (P a) = lineSide (P a) (P c) (P e) := by
        dsimp [lineSide]; ring
      linarith
    have hb_le : lineSide (P c) (P e) (P b) ≤ 0 := by
      have h : lineSide (P c) (P e) (P b) = lineSide (P b) (P c) (P e) := by
        dsimp [lineSide]; ring
      linarith
    have hd_pos : 0 < lineSide (P c) (P e) (P d) := by
      have h : lineSide (P c) (P e) (P d) = - lineSide (P c) (P d) (P e) := by
        dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos ha_le hb_le hd_pos with ⟨u, v, k, h_c, h_e, h_a, h_b, h_d⟩
    exact ⟨u, v, k, h_a, h_b, h_c, h_e, h_d⟩
  · refine ⟨1, 0, P d 0, by linarith, by linarith, by linarith, by linarith, by linarith⟩

#print axioms cap_five_convexIndep

/-- Explicit 5-index unpacking of a 5-cup chain (`CupChainEnding P S 3 d e`). -/
theorem cupChainEnding_three_iff {P : ℕ → ℝ²} {S : Finset ℕ} {d e : ℕ} :
    CupChainEnding P S 3 d e ↔
      ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ e ∈ S ∧
        a < b ∧ b < c ∧ c < d ∧ d < e ∧
        slopeLt (P a) (P b) (P c) ∧
        slopeLt (P b) (P c) (P d) ∧
        slopeLt (P c) (P d) (P e) := by
  constructor
  · rintro ⟨hdS, heS, hde, c, ⟨hcS, _, hcd, b, ⟨hbS, _, hbc, a, ⟨haS, _, hab⟩, hsl₁⟩, hsl₂⟩, hsl₃⟩
    exact ⟨a, b, c, haS, hbS, hcS, hdS, heS, hab, hbc, hcd, hde, hsl₁, hsl₂, hsl₃⟩
  · rintro ⟨a, b, c, haS, hbS, hcS, hdS, heS, hab, hbc, hcd, hde, hsl₁, hsl₂, hsl₃⟩
    exact ⟨hdS, heS, hde, c, ⟨hcS, hdS, hcd, b, ⟨hbS, hcS, hbc, a, ⟨haS, hbS, hab⟩, hsl₁⟩, hsl₂⟩, hsl₃⟩

#print axioms cupChainEnding_three_iff

/-- Explicit 5-index unpacking of a 5-cap chain (`CapChainStarting P S 3 a b`). -/
theorem capChainStarting_three_iff {P : ℕ → ℝ²} {S : Finset ℕ} {a b : ℕ} :
    CapChainStarting P S 3 a b ↔
      ∃ c d e, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ e ∈ S ∧
        a < b ∧ b < c ∧ c < d ∧ d < e ∧
        slopeGt (P a) (P b) (P c) ∧
        slopeGt (P b) (P c) (P d) ∧
        slopeGt (P c) (P d) (P e) := by
  constructor
  · rintro ⟨haS, hbS, hab, c, hsg₁, ⟨_, hcS, hbc, d, hsg₂, ⟨_, hdS, hcd, e, hsg₃, ⟨_, heS, hde⟩⟩⟩⟩
    exact ⟨c, d, e, haS, hbS, hcS, hdS, heS, hab, hbc, hcd, hde, hsg₁, hsg₂, hsg₃⟩
  · rintro ⟨c, d, e, haS, hbS, hcS, hdS, heS, hab, hbc, hcd, hde, hsg₁, hsg₂, hsg₃⟩
    exact ⟨haS, hbS, hab, c, hsg₁, ⟨hbS, hcS, hbc, d, hsg₂, ⟨hcS, hdS, hcd, e, hsg₃, ⟨hdS, heS, hde⟩⟩⟩⟩

#print axioms capChainStarting_three_iff

/-- Any $x$-monotone sequence $P$ on a finite index set $S$ with `HasCup P S 3`
contains a convex pentagon in its image $P(S)$. -/
theorem hasConvexFiveGon_of_hasCup_three {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hcup : HasCup P S 3) :
    HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  rcases hcup with ⟨d, e, hde_chain⟩
  rw [cupChainEnding_three_iff] at hde_chain
  rcases hde_chain with ⟨a, b, c, haS, hbS, hcS, hdS, heS, hab, hbc, hcd, hde, hsl₁, hsl₂, hsl₃⟩
  have hac : a < c := lt_trans hab hbc
  have had : a < d := lt_trans hac hcd
  have hae : a < e := lt_trans had hde
  have hbd : b < d := lt_trans hbc hcd
  have hbe : b < e := lt_trans hbd hde
  have hce : c < e := lt_trans hcd hde
  have hne_ab := xMonotone_ne_of_lt hmono hab
  have hne_ac := xMonotone_ne_of_lt hmono hac
  have hne_ad := xMonotone_ne_of_lt hmono had
  have hne_ae := xMonotone_ne_of_lt hmono hae
  have hne_bc := xMonotone_ne_of_lt hmono hbc
  have hne_bd := xMonotone_ne_of_lt hmono hbd
  have hne_be := xMonotone_ne_of_lt hmono hbe
  have hne_cd := xMonotone_ne_of_lt hmono hcd
  have hne_ce := xMonotone_ne_of_lt hmono hce
  have hne_de := xMonotone_ne_of_lt hmono hde
  refine ⟨{P a, P b, P c, P d, P e}, ?_, ?_, ?_⟩
  · simp [hne_ab, hne_ac, hne_ad, hne_ae, hne_bc, hne_bd, hne_be, hne_cd, hne_ce, hne_de]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨a, haS, rfl⟩
    · exact ⟨b, hbS, rfl⟩
    · exact ⟨c, hcS, rfl⟩
    · exact ⟨d, hdS, rfl⟩
    · exact ⟨e, heS, rfl⟩
  · simpa using cup_five_convexIndep hmono hab hbc hcd hde hsl₁ hsl₂ hsl₃

#print axioms hasConvexFiveGon_of_hasCup_three

/-- Any $x$-monotone sequence $P$ on a finite index set $S$ with `HasCap P S 3`
contains a convex pentagon in its image $P(S)$. -/
theorem hasConvexFiveGon_of_hasCap_three {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hcap : HasCap P S 3) :
    HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  rcases hcap with ⟨a, b, hab_chain⟩
  rw [capChainStarting_three_iff] at hab_chain
  rcases hab_chain with ⟨c, d, e, haS, hbS, hcS, hdS, heS, hab, hbc, hcd, hde, hsg₁, hsg₂, hsg₃⟩
  have hac : a < c := lt_trans hab hbc
  have had : a < d := lt_trans hac hcd
  have hae : a < e := lt_trans had hde
  have hbd : b < d := lt_trans hbc hcd
  have hbe : b < e := lt_trans hbd hde
  have hce : c < e := lt_trans hcd hde
  have hne_ab := xMonotone_ne_of_lt hmono hab
  have hne_ac := xMonotone_ne_of_lt hmono hac
  have hne_ad := xMonotone_ne_of_lt hmono had
  have hne_ae := xMonotone_ne_of_lt hmono hae
  have hne_bc := xMonotone_ne_of_lt hmono hbc
  have hne_bd := xMonotone_ne_of_lt hmono hbd
  have hne_be := xMonotone_ne_of_lt hmono hbe
  have hne_cd := xMonotone_ne_of_lt hmono hcd
  have hne_ce := xMonotone_ne_of_lt hmono hce
  have hne_de := xMonotone_ne_of_lt hmono hde
  refine ⟨{P a, P b, P c, P d, P e}, ?_, ?_, ?_⟩
  · simp [hne_ab, hne_ac, hne_ad, hne_ae, hne_bc, hne_bd, hne_be, hne_cd, hne_ce, hne_de]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨a, haS, rfl⟩
    · exact ⟨b, hbS, rfl⟩
    · exact ⟨c, hcS, rfl⟩
    · exact ⟨d, hdS, rfl⟩
    · exact ⟨e, heS, rfl⟩
  · simpa using cap_five_convexIndep hmono hab hbc hcd hde hsg₁ hsg₂ hsg₃

#print axioms hasConvexFiveGon_of_hasCap_three

/-- Any $x$-monotone sequence $P$ on a finite index set $S$ with `HasCup P S 3 ∨ HasCap P S 3`
contains a convex pentagon in its image $P(S)$. -/
theorem hasConvexFiveGon_of_hasCup_or_hasCap_three {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (h : HasCup P S 3 ∨ HasCap P S 3) :
    HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  rcases h with hcup | hcap
  · exact hasConvexFiveGon_of_hasCup_three hmono hcup
  · exact hasConvexFiveGon_of_hasCap_three hmono hcap

#print axioms hasConvexFiveGon_of_hasCup_or_hasCap_three

/-- **Unconditional 21-Point Erdős–Szekeres Convex Pentagon Theorem**:
Every $x$-monotone non-trilinear finite point sequence $P$ on an index set $S$ of cardinality
at least `erdosSzekeresUpper 5` ($= \binom{6}{3} + 1 = 21$) contains the vertices of a convex pentagon. -/
theorem erdos_szekeres_twenty_one_points_hasConvexFiveGon {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : erdosSzekeresUpper 5 ≤ S.card) :
    HasConvexNGon 5 (P '' (S : Set ℕ)) :=
  hasConvexFiveGon_of_hasCup_or_hasCap_three hmono
    (erdos_szekeres_diagonal_cup_cap hmono hnontri (by decide : 2 ≤ 5) S hcard)

#print axioms erdos_szekeres_twenty_one_points_hasConvexFiveGon

/-! ## Section 3: Erdős–Szekeres $(4, 5)$ and $(5, 5)$ Recurrences, Dilworth Bounds, and Endpoint-Sharing Forcing -/

/-- The Erdős–Szekeres / Dilworth monotone subsequence threshold $(r - 1)(s - 1) + 1$. -/
def dilworthMonotoneBound (r s : ℕ) : ℕ :=
  (r - 1) * (s - 1) + 1

theorem dilworthMonotoneBound_symm (r s : ℕ) :
    dilworthMonotoneBound r s = dilworthMonotoneBound s r := by
  dsimp [dilworthMonotoneBound]
  ring

#print axioms dilworthMonotoneBound_symm

theorem dilworthMonotoneBound_step_left {r s : ℕ} (hr : 1 ≤ r) :
    dilworthMonotoneBound (r + 1) s = dilworthMonotoneBound r s + (s - 1) := by
  dsimp [dilworthMonotoneBound]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have h : m + 1 - 1 = m := by omega
  rw [h]
  ring

#print axioms dilworthMonotoneBound_step_left

theorem dilworthMonotoneBound_step_right {r s : ℕ} (hs : 1 ≤ s) :
    dilworthMonotoneBound r (s + 1) = dilworthMonotoneBound r s + (r - 1) := by
  dsimp [dilworthMonotoneBound]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have h : k + 1 - 1 = k := by omega
  rw [h]
  ring

#print axioms dilworthMonotoneBound_step_right

/-- Exact evaluation of the cup-cap recurrence, Tóth–Valtr bound, Dilworth product bound,
and Erdős–Szekeres bounds at $(4, 5)$ and $(5, 5)$. -/
theorem cupCap_and_dilworth_thresholds_four_five_and_five_five :
    cupCapBound 3 5 = 5 ∧
    cupCapBound 4 4 = 7 ∧
    cupCapBound 4 5 = 11 ∧
    cupCapBound 5 4 = 11 ∧
    tothValtrUpper 5 = 11 ∧
    dilworthMonotoneBound 4 5 = 13 ∧
    dilworthMonotoneBound 5 5 = 17 ∧
    erdosSzekeresConjectured 5 = 9 ∧
    erdosSzekeresUpper 5 = 21 ∧
    cupCapBound 4 5 + 1 = cupCapBound 3 5 + cupCapBound 4 4 ∧
    cupCapBound 5 5 + 1 = cupCapBound 4 5 + cupCapBound 5 4 := by
  decide

#print axioms cupCap_and_dilworth_thresholds_four_five_and_five_five

/-- **Endpoint-Sharing Pentagon Forcing Theorem**:
If a vertex $b \in S$ is simultaneously the right endpoint of a 4-cup (`CupChainEnding P S 2 a b`)
and the left endpoint of a 4-cap (`CapChainStarting P S 2 b c`), then $P(S)$ contains a convex pentagon. -/
theorem endpoint_sharing_four_cup_cap_forces_fiveGon {P : ℕ → ℝ²} {S : Finset ℕ} {a b c : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcup : CupChainEnding P S 2 a b) (hcap : CapChainStarting P S 2 b c) :
    HasConvexNGon 5 (P '' (S : Set ℕ)) :=
  hasConvexFiveGon_of_hasCup_or_hasCap_three hmono
    (cup_end_meets_cap_start hmono hnontri hcup hcap)

#print axioms endpoint_sharing_four_cup_cap_forces_fiveGon

/-- At the asymmetric threshold `cupCapBound 4 5 = 11`, any $x$-monotone non-trilinear sequence
contains either a 4-cup (`HasCup P S 2`) or a convex pentagon (`HasConvexNGon 5 (P '' (S : Set ℕ))`). -/
theorem eleven_points_cup_four_or_convexFiveGon {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : cupCapBound 4 5 ≤ S.card) :
    HasCup P S 2 ∨ HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  rcases erdos_szekeres_cup_cap_of_ge_two hmono hnontri (by decide : 2 ≤ 4) (by decide : 2 ≤ 5) S hcard with hcup | hcap
  · exact Or.inl hcup
  · exact Or.inr (hasConvexFiveGon_of_hasCap_three hmono hcap)

#print axioms eleven_points_cup_four_or_convexFiveGon

/-- At the dual asymmetric threshold `cupCapBound 5 4 = 11`, any $x$-monotone non-trilinear sequence
contains either a 4-cap (`HasCap P S 2`) or a convex pentagon (`HasConvexNGon 5 (P '' (S : Set ℕ))`). -/
theorem eleven_points_cap_four_or_convexFiveGon {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : cupCapBound 5 4 ≤ S.card) :
    HasCap P S 2 ∨ HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  rcases erdos_szekeres_cup_cap_of_ge_two hmono hnontri (by decide : 2 ≤ 5) (by decide : 2 ≤ 4) S hcard with hcup | hcap
  · exact Or.inr (hasConvexFiveGon_of_hasCup_three hmono hcup)
  · exact Or.inl hcap

#print axioms eleven_points_cap_four_or_convexFiveGon

/-- At `tothValtrUpper 5 = 11` points, any $x$-monotone non-trilinear sequence contains either
both a 4-cup and a 4-cap (hence a convex 4-gon in both orientations) or a convex pentagon. -/
theorem eleven_points_both_fourCup_fourCap_or_convexFiveGon {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : tothValtrUpper 5 ≤ S.card) :
    (HasCup P S 2 ∧ HasCap P S 2) ∨ HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  have h45 : cupCapBound 4 5 ≤ S.card := by
    rw [← (tothValtrUpper_eq_cupCapBound_asymmetric (by decide : 3 ≤ 5)).1]
    exact hcard
  have h54 : cupCapBound 5 4 ≤ S.card := by
    rw [← (tothValtrUpper_eq_cupCapBound_asymmetric (by decide : 3 ≤ 5)).2]
    exact hcard
  rcases eleven_points_cup_four_or_convexFiveGon hmono hnontri h45 with hcup | h5
  · rcases eleven_points_cap_four_or_convexFiveGon hmono hnontri h54 with hcap | h5
    · exact Or.inl ⟨hcup, hcap⟩
    · exact Or.inr h5
  · exact Or.inr h5

#print axioms eleven_points_both_fourCup_fourCap_or_convexFiveGon

/-- At the Dilworth $(4, 5)$ threshold `dilworthMonotoneBound 4 5 = 13` (and hence also at
`dilworthMonotoneBound 5 5 = 17`), any $x$-monotone non-trilinear sequence simultaneously satisfies
`HasCup P S 2 ∧ HasCap P S 2` or contains a convex pentagon. -/
theorem thirteen_points_simultaneous_four_five_cup_cap {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : dilworthMonotoneBound 4 5 ≤ S.card) :
    (HasCup P S 2 ∧ HasCap P S 2) ∨ HasConvexNGon 5 (P '' (S : Set ℕ)) := by
  have htv : tothValtrUpper 5 ≤ S.card := by
    have hle : tothValtrUpper 5 ≤ dilworthMonotoneBound 4 5 := by decide
    exact le_trans hle hcard
  exact eleven_points_both_fourCup_fourCap_or_convexFiveGon hmono hnontri htv

#print axioms thirteen_points_simultaneous_four_five_cup_cap

/-- At the Dilworth $(5, 5)$ threshold `dilworthMonotoneBound 5 5 = 17`, any $x$-monotone non-trilinear
sequence contains a convex 4-gon and either both a 4-cup and a 4-cap or a convex pentagon. -/
theorem seventeen_points_simultaneous_four_five_cup_cap {P : ℕ → ℝ²} {S : Finset ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcard : dilworthMonotoneBound 5 5 ≤ S.card) :
    HasConvexNGon 4 (P '' (S : Set ℕ)) ∧
      ((HasCup P S 2 ∧ HasCap P S 2) ∨ HasConvexNGon 5 (P '' (S : Set ℕ))) := by
  have h7 : erdosSzekeresUpper 4 ≤ S.card := by
    have hle : erdosSzekeresUpper 4 ≤ dilworthMonotoneBound 5 5 := by decide
    exact le_trans hle hcard
  have h13 : dilworthMonotoneBound 4 5 ≤ S.card := by
    have hle : dilworthMonotoneBound 4 5 ≤ dilworthMonotoneBound 5 5 := by decide
    exact le_trans hle hcard
  exact ⟨erdos_szekeres_seven_points_hasConvexFourGon hmono hnontri h7,
    thirteen_points_simultaneous_four_five_cup_cap hmono hnontri h13⟩

#print axioms seventeen_points_simultaneous_four_five_cup_cap

/-! ## Section 4: 9-Point Kalbfleisch–Kalbfleisch–Stanton Nested-Hull Reduction and Universal Corner-Wedge Obstruction -/

/-- **Kalbfleisch–Kalbfleisch–Stanton Outer Hull Layer Dichotomy for 9 Points**:
Given any 9-point set $P \subseteq \mathbb{R}^2$ and a convex-independent outer layer $H \subseteq P$
with $3 \le |H|$, either $P$ already contains a convex pentagon from $H$ ($|H| \ge 5$), or the outer/inner
layer cardinalities $(|H|, |P \setminus H|)$ equal $(4, 5)$ or $(3, 6)$. -/
theorem kks_nine_point_hull_layer_dichotomy {P H : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH3 : 3 ≤ H.card) (hconv : ConvexIndep (H : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) ∨
      (H.card = 4 ∧ (P \ H).card = 5) ∨
      (H.card = 3 ∧ (P \ H).card = 6) := by
  have hpart : (P \ H).card + H.card = P.card := Finset.card_sdiff_add_card_eq_card hHP
  by_cases h5 : 5 ≤ H.card
  · left
    have hH_ngon : HasConvexNGon H.card (H : Set ℝ²) := ⟨H, rfl, Set.Subset.rfl, hconv⟩
    have hH_five : HasConvexNGon 5 (H : Set ℝ²) := hasConvexNGon_mono_n hH_ngon h5
    exact hasConvexNGon_mono_pts hH_five (Finset.coe_subset.mpr hHP)
  · right
    have h43 : H.card = 4 ∨ H.card = 3 := by omega
    rcases h43 with h4 | h3
    · left; exact ⟨h4, by omega⟩
    · right; exact ⟨h3, by omega⟩

#print axioms kks_nine_point_hull_layer_dichotomy

/-- **Kalbfleisch–Kalbfleisch–Stanton $(4, 5)$ Inner Layer Sub-Dichotomy**:
When a 9-point set $P$ has an outer 4-gon $H \subseteq P$ ($|H| = 4$) and the 5 interior points $P \setminus H$
have a convex-independent sub-hull $H_2 \subseteq P \setminus H$ with $3 \le |H_2|$, either $H_2$ is itself
a convex pentagon ($|H_2| = 5$), or the nested layer profile $(|H|, |H_2|, |(P \setminus H) \setminus H_2|)$
is $(4, 4, 1)$ or $(4, 3, 2)$. -/
theorem kks_nine_point_layer_four_five_subhull_dichotomy {P H H₂ : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH4 : H.card = 4)
    (hH₂ : H₂ ⊆ P \ H) (hH₂3 : 3 ≤ H₂.card) (hconv₂ : ConvexIndep (H₂ : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) ∨
      (H₂.card = 4 ∧ ((P \ H) \ H₂).card = 1) ∨
      (H₂.card = 3 ∧ ((P \ H) \ H₂).card = 2) := by
  have hpart₁ : (P \ H).card + H.card = P.card := Finset.card_sdiff_add_card_eq_card hHP
  have hpart₂ : ((P \ H) \ H₂).card + H₂.card = (P \ H).card :=
    Finset.card_sdiff_add_card_eq_card hH₂
  by_cases h5 : 5 ≤ H₂.card
  · left
    have hH₂_ngon : HasConvexNGon H₂.card (H₂ : Set ℝ²) := ⟨H₂, rfl, Set.Subset.rfl, hconv₂⟩
    have hH₂_five : HasConvexNGon 5 (H₂ : Set ℝ²) := hasConvexNGon_mono_n hH₂_ngon h5
    have hsub : H₂ ⊆ P := Finset.Subset.trans hH₂ Finset.sdiff_subset
    exact hasConvexNGon_mono_pts hH₂_five (Finset.coe_subset.mpr hsub)
  · right
    have h43 : H₂.card = 4 ∨ H₂.card = 3 := by omega
    rcases h43 with h4 | h3
    · left; exact ⟨h4, by omega⟩
    · right; exact ⟨h3, by omega⟩

#print axioms kks_nine_point_layer_four_five_subhull_dichotomy

/-- **Kalbfleisch–Kalbfleisch–Stanton $(3, 6)$ Inner Layer Sub-Dichotomy**:
When a 9-point set $P$ has an outer triangle $H \subseteq P$ ($|H| = 3$) and the 6 interior points $P \setminus H$
have a convex-independent sub-hull $H_2 \subseteq P \setminus H$ with $3 \le |H_2|$, either $H_2$ contains a
convex pentagon ($|H_2| \ge 5$), or the nested layer profile $(|H|, |H_2|, |(P \setminus H) \setminus H_2|)$
is $(3, 4, 2)$ or $(3, 3, 3)$. -/
theorem kks_nine_point_layer_three_six_subhull_dichotomy {P H H₂ : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH3 : H.card = 3)
    (hH₂ : H₂ ⊆ P \ H) (hH₂3 : 3 ≤ H₂.card) (hconv₂ : ConvexIndep (H₂ : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) ∨
      (H₂.card = 4 ∧ ((P \ H) \ H₂).card = 2) ∨
      (H₂.card = 3 ∧ ((P \ H) \ H₂).card = 3) := by
  have hpart₁ : (P \ H).card + H.card = P.card := Finset.card_sdiff_add_card_eq_card hHP
  have hpart₂ : ((P \ H) \ H₂).card + H₂.card = (P \ H).card :=
    Finset.card_sdiff_add_card_eq_card hH₂
  by_cases h5 : 5 ≤ H₂.card
  · left
    have hH₂_ngon : HasConvexNGon H₂.card (H₂ : Set ℝ²) := ⟨H₂, rfl, Set.Subset.rfl, hconv₂⟩
    have hH₂_five : HasConvexNGon 5 (H₂ : Set ℝ²) := hasConvexNGon_mono_n hH₂_ngon h5
    have hsub : H₂ ⊆ P := Finset.Subset.trans hH₂ Finset.sdiff_subset
    exact hasConvexNGon_mono_pts hH₂_five (Finset.coe_subset.mpr hsub)
  · right
    have h43 : H₂.card = 4 ∨ H₂.card = 3 := by omega
    rcases h43 with h4 | h3
    · left; exact ⟨h4, by omega⟩
    · right; exact ⟨h3, by omega⟩

#print axioms kks_nine_point_layer_three_six_subhull_dichotomy

/-- **Universal Kalbfleisch–Kalbfleisch–Stanton 9-Point Pentagon Reduction**:
Any 9-point set $P \subseteq \mathbb{R}^2$ with a convex-independent outer layer $H \subseteq P$ ($3 \le |H|$)
contains a convex pentagon whenever the two remaining layer cases $(|H|, |P \setminus H|) = (4, 5)$ and $(3, 6)$
yield a convex pentagon. -/
theorem kks_nine_point_pentagon_reduction {P H : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH3 : 3 ≤ H.card) (hconv : ConvexIndep (H : Set ℝ²))
    (h45 : H.card = 4 → (P \ H).card = 5 → HasConvexNGon 5 (P : Set ℝ²))
    (h36 : H.card = 3 → (P \ H).card = 6 → HasConvexNGon 5 (P : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) := by
  rcases kks_nine_point_hull_layer_dichotomy hP hHP hH3 hconv with h5 | ⟨h4, hi5⟩ | ⟨h3, hi6⟩
  · exact h5
  · exact h45 h4 hi5
  · exact h36 h3 hi6

#print axioms kks_nine_point_pentagon_reduction

/-- Vertices of the canonical inner square $\{(1, 1), (-1, 1), (-1, -1), (1, -1)\} \subseteq \mathbb{R}^2$. -/
def sqPP : ℝ² := mkPt 1 1
def sqNP : ℝ² := mkPt (-1) 1
def sqNN : ℝ² := mkPt (-1) (-1)
def sqPN : ℝ² := mkPt 1 (-1)

/-- Canonical corner-wedge outer vertex $(4, 5)$ in the 8-point pentagon-free $(4, 4)$ configuration. -/
def outPP : ℝ² := mkPt 4 5

/-- The canonical inner square `{sqPP, sqNP, sqNN, sqPN}` is convex independent (`ConvexIndep`). -/
theorem innerSquare_convexIndep :
    ConvexIndep ({sqPP, sqNP, sqNN, sqPN} : Set ℝ²) := by
  apply convexIndep_four_of_strict_sep
  · refine ⟨1, 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [sqPP, sqNP, sqNN, sqPN]
  · refine ⟨-1, 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [sqPP, sqNP, sqNN, sqPN]
  · refine ⟨-1, -1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [sqPP, sqNP, sqNN, sqPN]
  · refine ⟨1, -1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [sqPP, sqNP, sqNN, sqPN]

#print axioms innerSquare_convexIndep

/-- **Universal Corner-Wedge Barycentric Identity**:
For every point $(x, y) \in \mathbb{R}^2$ with $x + y \ne 0$, the inner square corner $(1, 1)$ is the
affine combination $\frac{x - 1}{x + y}(-1, 1) + \frac{y - 1}{x + y}(1, -1) + \frac{2}{x + y}(x, y)$. -/
theorem sqPP_eq_barycentric_of_add_ne_zero {x y : ℝ} (hxy : x + y ≠ 0) :
    ((x - 1) / (x + y)) • sqNP + ((y - 1) / (x + y)) • sqPN + (2 / (x + y)) • mkPt x y = sqPP := by
  ext i
  fin_cases i <;> simp [sqPP, sqNP, sqPN, mkPt] <;> field_simp [hxy] <;> ring

#print axioms sqPP_eq_barycentric_of_add_ne_zero

/-- **Universal Corner-Wedge Convex-Hull Containment Theorem**:
For every $(x, y) \in \mathbb{R}^2$ in the open corner quadrant $1 < x \wedge 1 < y$, the inner square
corner `sqPP` $= (1, 1)$ lies in the convex hull of `{sqNP, sqPN, mkPt x y}`. -/
theorem sqPP_mem_convexHull_of_gt_one {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    sqPP ∈ convexHull ℝ ({sqNP, sqPN, mkPt x y} : Set ℝ²) := by
  have hxy : 0 < x + y := by linarith
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy
  have hsum12 : 0 < x + y - 2 := by linarith
  have hsum12_ne : x + y - 2 ≠ 0 := ne_of_gt hsum12
  rw [← sqPP_eq_barycentric_of_add_ne_zero hxy_ne]
  have hdecomp :
      ((x - 1) / (x + y)) • sqNP + ((y - 1) / (x + y)) • sqPN + (2 / (x + y)) • mkPt x y =
      ((x + y - 2) / (x + y)) •
        (((x - 1) / (x + y - 2)) • sqNP + ((y - 1) / (x + y - 2)) • sqPN) +
        (2 / (x + y)) • mkPt x y := by
    ext i
    fin_cases i <;> simp [sqNP, sqPN, mkPt] <;> field_simp [hxy_ne, hsum12_ne]
  rw [hdecomp]
  have h_conv := convex_convexHull ℝ ({sqNP, sqPN, mkPt x y} : Set ℝ²)
  have hNP : sqNP ∈ convexHull ℝ ({sqNP, sqPN, mkPt x y} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hPN : sqPN ∈ convexHull ℝ ({sqNP, sqPN, mkPt x y} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hOut : mkPt x y ∈ convexHull ℝ ({sqNP, sqPN, mkPt x y} : Set ℝ²) :=
    subset_convexHull ℝ _ (by simp)
  have hmid :
      ((x - 1) / (x + y - 2)) • sqNP + ((y - 1) / (x + y - 2)) • sqPN ∈
        convexHull ℝ ({sqNP, sqPN, mkPt x y} : Set ℝ²) := by
    apply h_conv hNP hPN
    · exact div_nonneg (by linarith) (le_of_lt hsum12)
    · exact div_nonneg (by linarith) (le_of_lt hsum12)
    · field_simp [hsum12_ne]; ring
  apply h_conv hmid hOut
  · exact div_nonneg (le_of_lt hsum12) (le_of_lt hxy)
  · exact div_nonneg (by norm_num) (le_of_lt hxy)
  · field_simp [hxy_ne]; ring

#print axioms sqPP_mem_convexHull_of_gt_one

/-- **Universal Corner-Wedge Non-Convexity Theorem**:
For every outer point `(x, y)` in the open corner quadrant $1 < x \wedge 1 < y$, adjoining `mkPt x y`
to the inner square `{sqPP, sqNP, sqNN, sqPN}` fails to form a convex pentagon because `sqPP` lies in
the convex hull of `{sqNP, sqPN, mkPt x y}`. -/
theorem not_convexIndep_innerSquare_corner_wedge_of_gt_one {x y : ℝ}
    (hx : 1 < x) (hy : 1 < y) :
    ¬ ConvexIndep ({sqPP, sqNP, sqNN, sqPN, mkPt x y} : Set ℝ²) := by
  intro hci
  apply hci sqPP (by simp)
  have hsub :
      ({sqNP, sqPN, mkPt x y} : Set ℝ²) ⊆
        ({sqPP, sqNP, sqNN, sqPN, mkPt x y} : Set ℝ²) \ {sqPP} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨by simp, ?_⟩
      intro h; have h0 := congrArg (fun w : ℝ² => w 0) h; simp [sqNP, sqPP] at h0; linarith
    · refine ⟨by simp, ?_⟩
      intro h; have h1 := congrArg (fun w : ℝ² => w 1) h; simp [sqPN, sqPP] at h1; linarith
    · refine ⟨by simp, ?_⟩
      intro h; have h0 := congrArg (fun w : ℝ² => w 0) h; simp [sqPP] at h0; linarith
  exact convexHull_mono hsub (sqPP_mem_convexHull_of_gt_one hx hy)

#print axioms not_convexIndep_innerSquare_corner_wedge_of_gt_one

/-- Specializing to the canonical 8-point corner-wedge witness `outPP = (4, 5)` certifies that
`{sqPP, sqNP, sqNN, sqPN, outPP}` is not convex independent. -/
theorem not_convexIndep_innerSquare_plus_outPP :
    ¬ ConvexIndep ({sqPP, sqNP, sqNN, sqPN, outPP} : Set ℝ²) :=
  not_convexIndep_innerSquare_corner_wedge_of_gt_one (by norm_num) (by norm_num)

#print axioms not_convexIndep_innerSquare_plus_outPP

/-- By contrast, the canonical 9-point parabola configuration `parabolaFinset 9` has cardinality 9,
is in general position (`NonTrilinear`), and contains the vertices of a convex pentagon. -/
theorem parabolaFinset_nine_hasConvexFiveGon :
    (parabolaFinset 9).card = 9 ∧
    NonTrilinear ((parabolaFinset 9 : Finset ℝ²) : Set ℝ²) ∧
    HasConvexNGon 5 ((parabolaFinset 9 : Finset ℝ²) : Set ℝ²) :=
  ⟨parabolaFinset_card 9,
    parabolaFinset_nonTrilinear 9,
    parabolaFinset_hasConvexNGon (by decide : 5 ≤ 9)⟩

#print axioms parabolaFinset_nine_hasConvexFiveGon

/-- Conditional completion bridge for $f(5) = 9$: if $8 \notin \mathrm{cardSet}\,5$ (as witnessed by the
8-point $(4, 4)$ nested-square configuration) and $9 \in \mathrm{cardSet}\,5$ (via the 9-point
Kalbfleisch–Kalbfleisch–Stanton reduction), then $f(5) = \mathrm{erdosSzekeresConjectured}\,5 = 9$. -/
theorem f_five_eq_nine_of_eight_not_mem_and_nine_mem
    (h8 : (8 : ℕ) ∉ cardSet 5) (h9 : (9 : ℕ) ∈ cardSet 5) :
    f 5 = 9 ∧ f 5 = erdosSzekeresConjectured 5 := by
  have hle : f 5 ≤ 9 := Nat.sInf_le h9
  have hge : 9 ≤ f 5 := by
    apply le_csInf ⟨9, h9⟩
    intro N hN
    by_contra hlt
    have hN8 : N ≤ 8 := by omega
    exact h8 (cardSet_upward_closed hN8 hN)
  have heq : f 5 = 9 := le_antisymm hle hge
  exact ⟨heq, heq⟩

#print axioms f_five_eq_nine_of_eight_not_mem_and_nine_mem

end Erdos107
