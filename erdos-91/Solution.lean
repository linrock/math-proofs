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

public import TriangularDisksAndEisenstein91
public import HexagonMultiplicity91
public import MultiDeletionCore91
public import Blueprint91

@[expose] public section

/-!
# Erdős Problem 91: Solution Entrypoint

This module exports the four small-case theorems matching `Challenge.lean` in the
`Erdos91.Palomar` namespace.
-/

open Finset Filter Topology
open scoped Finset

namespace Erdos91.Palomar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The set of positive pairwise Euclidean distances determined by `points`. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- The number of distinct positive distances determined by `points`. -/
noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)

/-- The minimum number of distinct positive distances among $n$-point sets in $X$. -/
noncomputable def minimalDistinctDistances (X : Type*) [MetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

/-- A planar set $A$ is optimal if $|A| = n$ and it attains `minimalDistinctDistances Plane n`. -/
noncomputable def IsOptimal (A : Finset Plane) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances Plane n

/-- Two finite planar sets are similar if related by a `DilationEquiv`. -/
def DilationEquivSimilar (A B : Finset Plane) : Prop :=
  ∃ f : Plane ≃ᵈ Plane, (f '' (A : Set Plane)) = (B : Set Plane)

/-- Equilateral triangle with unit side length, resting on the x-axis with one vertex at the origin. -/
noncomputable def equiTriangle : Finset Plane :=
  {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

/-- Every optimal $n$-point planar configuration is similar to every other. -/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset Plane, IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

/-- There exist at least $K$ pairwise nonsimilar optimal $n$-point planar configurations. -/
def HasAtLeastKNonsimilarMinimizers (K n : ℕ) : Prop :=
  ∃ F : Finset (Finset Plane),
    F.card = K ∧ (∀ A ∈ F, IsOptimal A n) ∧ (∀ A ∈ F, ∀ C ∈ F, A ≠ C → ¬ DilationEquivSimilar A C)

noncomputable instance : DecidablePred UniqueMinimizer := Classical.decPred _
noncomputable instance (K : ℕ) : DecidablePred (HasAtLeastKNonsimilarMinimizers K) := Classical.decPred _

/-- The subset of $\{0, \dots, N\}$ at which `UniqueMinimizer n` holds. -/
noncomputable def uniqueMinimizerSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter UniqueMinimizer

/-- The subset of $\{0, \dots, N\}$ admitting at least $K$ pairwise nonsimilar minimizers. -/
noncomputable def goodMultiplicitySet (K N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (HasAtLeastKNonsimilarMinimizers K)

/-- Triangular-lattice embedding $(x, y) \mapsto (2x + y, \sqrt{3} y)$ in $\mathbb{R}^2$. -/
noncomputable def triPoint (p : ℕ × ℕ) : Plane :=
  !₂[(2 * (p.1 : ℝ) + (p.2 : ℝ)), Real.sqrt 3 * (p.2 : ℝ)]

/-- Integer Eisenstein squared norm $4(a^2 + ab + b^2)$ of a triangular-lattice offset. -/
def triNormSq (u : ℕ × ℕ) : ℕ := 4 * (u.1 * u.1 + u.1 * u.2 + u.2 * u.2)

/-- Euclidean distance $\sqrt{\mathrm{triNormSq}(u)}$ of a triangular-lattice offset. -/
noncomputable def triNorm (u : ℕ × ℕ) : ℝ := Real.sqrt (triNormSq u : ℝ)

def hexRowList (k c m x : ℕ) : List (ℕ × ℕ) :=
  ((List.range k).filter (fun y => decide (c ≤ x + y ∧ x + y ≤ c + m))).map (fun y => (x, y))

def hexCoordsList (k c m : ℕ) : List (ℕ × ℕ) := (List.range k).flatMap (hexRowList k c m)
def hexCoords (k c m : ℕ) : Finset (ℕ × ℕ) := (hexCoordsList k c m).toFinset

/-- Clipped hexagon in the triangular lattice. -/
noncomputable def hexSet (k c m : ℕ) : Finset Plane := (hexCoords k c m).image triPoint

def triUtpRowList (m x : ℕ) : List (ℕ × ℕ) :=
  ((List.range (m + 1)).filter (fun y => decide ((x, y) ≠ (0, 0) ∧ x ≤ y ∧ x + y ≤ m))).map (fun y => (x, y))

def triUtpList (m : ℕ) : List (ℕ × ℕ) := (List.range (m + 1)).flatMap (triUtpRowList m)
def triUtp (m : ℕ) : Finset (ℕ × ℕ) := (triUtpList m).toFinset
def hex21Utp9 : Finset (ℕ × ℕ) := insert (2, 3) (triUtp 4)

private theorem minDist_eq :
    minimalDistinctDistances Plane = Minimizer91.minimalDistinctDistances :=
  funext Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_minimalDistinctDistances_eq

private theorem isOptimal_eq :
    IsOptimal = Minimizer91.IsOptimal := by
  ext A n
  exact (Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_isOptimal_and_similar_iff A A n).1

private theorem uniqueMinimizer_eq :
    UniqueMinimizer = PlateauDefinitions91.UniqueMinimizer := by
  ext n
  exact Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_uniqueMinimizer_iff n

private theorem hasAtLeastK_eq :
    HasAtLeastKNonsimilarMinimizers =
      Erdos91.GeneralMultiplicityAndDensityOne.HasAtLeastKNonsimilarMinimizers := by
  ext K n
  unfold HasAtLeastKNonsimilarMinimizers
    Erdos91.GeneralMultiplicityAndDensityOne.HasAtLeastKNonsimilarMinimizers
  rw [isOptimal_eq]
  rfl

private theorem hasAtLeastK_uncond_eq :
    HasAtLeastKNonsimilarMinimizers =
      Erdos91.UnconditionalNaturalDensityOne.HasAtLeastKNonsimilarMinimizers :=
  hasAtLeastK_eq

private theorem uniqueMinimizerSet_eq (N : ℕ) :
    uniqueMinimizerSet N = Erdos91.AsymptoticDensityOneAndGlobalBounds.uniqueMinimizerSet N := by
  ext n
  simp [uniqueMinimizerSet, Erdos91.AsymptoticDensityOneAndGlobalBounds.uniqueMinimizerSet,
    uniqueMinimizer_eq]

private theorem goodMultiplicitySet_eq (K N : ℕ) :
    goodMultiplicitySet K N =
      Erdos91.AsymptoticDensityOneAndGlobalBounds.goodMultiplicitySet K N := by
  ext n
  simp [goodMultiplicitySet, Erdos91.AsymptoticDensityOneAndGlobalBounds.goodMultiplicitySet,
    hasAtLeastK_eq]

private theorem goodMultiplicitySet_uncond_eq (K N : ℕ) :
    goodMultiplicitySet K N =
      Erdos91.UnconditionalNaturalDensityOne.goodMultiplicitySet K N := by
  ext n
  simp [goodMultiplicitySet, Erdos91.UnconditionalNaturalDensityOne.goodMultiplicitySet,
    hasAtLeastK_uncond_eq]

theorem erdos_91_variants_three : UniqueMinimizer 3 :=
  Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_erdos_91_solved_variants.1

theorem erdos_91_variants_four : ¬ UniqueMinimizer 4 :=
  Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_erdos_91_solved_variants.2.1

theorem erdos_91_variants_six : ¬ UniqueMinimizer 6 :=
  Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_erdos_91_solved_variants.2.2.1

theorem erdos_91_variants_seven : ¬ UniqueMinimizer 7 :=
  Erdos91.FormalConjecturesBridgesAndSolvedVariants.fc_erdos_91_solved_variants.2.2.2.1

end Erdos91.Palomar
