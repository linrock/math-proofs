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

public import Mathlib

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 20000

noncomputable section
open scoped BigOperators


/-!
# Erdős Problem #836: Uniform Hypergraph Chromatic Colouring (Lean 4.35.0-rc2 Baseline)

Official Reference: https://www.erdosproblems.com/836
Primary Reference: Erdős, P. and Lovász, L., *Problems and results on 3-chromatic hypergraphs
and some related questions*, Infinite and finite sets (Colloq., Keszthely, 1973), Vol. II,
pp. 609–627, Colloq. Math. Soc. János Bolyai, Vol. 10, North-Holland, Amsterdam, 1975.

## Problem Statement

Let `r ≥ 2` and `H` be an `r`-uniform hypergraph with chromatic number `3` (i.e., `H` has a
proper 3-colouring with no monochromatic edge, and no proper 2-colouring). Suppose any two
edges of `H` have a non-empty intersection (`IsIntersecting H`).
1. Must `H` contain `O(r^2)` many active vertices? (Negatively resolved by Noga Alon's
   equitable-partition hypergraph with `(2r - 2) + C(2r - 2, r - 1) / 2 ≍ 4^r / √r` vertices.)
2. Must there exist two distinct edges of `H` which meet in `≫ r` many vertices? (Erdős and
   Lovász (1975) proved `≫ r / log r`; resolved affirmatively with `c = 1 / 3` via the
   minimal-blue double-counting bound `r ≤ 2t + 1`.)
3. Are there examples other than the Fano plane `PG(2, 2)` (`r = 3`) where no two distinct
   edges meet in `r - 1` vertices?
-/

namespace Erdos836

variable {V : Type*}

/-- A finite hypergraph `H` (represented as a `Finset` of `Finset V` hyperedges) is `r`-uniform
if every hyperedge in `H` has cardinality `r`. -/
def IsUniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A hypergraph `H` is intersecting if every pair of hyperedges in `H` has nonempty intersection. -/
def IsIntersecting [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, (e₁ ∩ e₂).Nonempty

/-- The set of active vertices of `H`, i.e., the union of all hyperedges in `H`. -/
def activeVertices [DecidableEq V] (H : Finset (Finset V)) : Finset V :=
  H.biUnion id

/-- A vertex colouring `c : V → C` is proper for `H` if no hyperedge of `H` is monochromatic
(every hyperedge contains two vertices of distinct colours). -/
def IsProperColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- A hypergraph `H` is `k`-colourable if it has a proper vertex colouring with `Fin k`. -/
def IsKColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring H c

/-- A hypergraph `H` is 2-colourable (has Property B) if `IsKColorable H 2`. -/
def IsTwoColorable (H : Finset (Finset V)) : Prop :=
  IsKColorable H 2

/-- A hypergraph `H` is 3-colourable if `IsKColorable H 3`. -/
def IsThreeColorable (H : Finset (Finset V)) : Prop :=
  IsKColorable H 3

/-- A hypergraph `H` has chromatic number exactly `3` if it is 3-colourable and not 2-colourable. -/
def HasChromaticNumberThree (H : Finset (Finset V)) : Prop :=
  IsThreeColorable H ∧ ¬ IsTwoColorable H

/-- The degree of a vertex `v` in `H` is the number of hyperedges of `H` containing `v`. -/
def vertexDegree [DecidableEq V] (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- A hypergraph `H` is a star centred at `v` if `v` belongs to every hyperedge of `H`. -/
def IsStarAt (H : Finset (Finset V)) (v : V) : Prop :=
  ∀ e ∈ H, v ∈ e

/-- A finite vertex set `T` is a transversal (hitting set) of `H` if `T` intersects every
hyperedge of `H`. -/
def IsTransversal [DecidableEq V] (H : Finset (Finset V)) (T : Finset V) : Prop :=
  ∀ e ∈ H, (e ∩ T).Nonempty

/-- `H` has a pair of distinct edges meeting in at least `k` vertices. -/
def HasPairwiseIntersectionAtLeast [DecidableEq V] (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ k ≤ (e₁ ∩ e₂).card

/-- `H` is linear (nearly disjoint) if any two distinct edges meet in at most `1` vertex. -/
def IsLinearHypergraph [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

/-- Statement of Erdős Problem #836, Question 1 (Quadratic Vertex Bound Question):
Does there exist an absolute constant `C > 0` such that every 3-chromatic intersecting
`r`-uniform hypergraph (`r ≥ 2`) has at most `C * r^2` active vertices?
(Disproved by Alon's equitable-partition construction with `≍ 4^r / √r` vertices.) -/
def Erdos836QuadraticVertexQuestion : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ), 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → IsIntersecting H → HasChromaticNumberThree H →
        (activeVertices H).card ≤ C * r ^ 2

/-- Statement of Erdős Problem #836, Question 2 (Linear Pairwise Intersection Conjecture):
Does there exist an absolute constant `c > 0` such that for every `r ≥ 2` and every
3-chromatic intersecting `r`-uniform hypergraph `H`, there exist two distinct edges
meeting in at least `c * r` vertices? -/
def Erdos836LinearIntersectionConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ), 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → IsIntersecting H → HasChromaticNumberThree H →
        ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ c * (r : ℝ) ≤ ((e₁ ∩ e₂).card : ℝ)

/-- Statement of the Erdős–Shelah Codimension-One Intersection Question:
For a given `r ≥ 2`, does there exist a 3-chromatic intersecting `r`-uniform hypergraph
in which no two distinct edges meet in `r - 1` or more vertices? -/
def HasCodimensionOneAvoidingWitness (r : ℕ) : Prop :=
  ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
      ¬ HasPairwiseIntersectionAtLeast H (r - 1)

/-- Vertex count of Alon's counterexample hypergraph for uniformity `r`:
`|X| + |Y| = (2r - 2) + C(2r - 2, r - 1) / 2`. -/
def alonVertexCount (r : ℕ) : ℕ :=
  (2 * r - 2) + Nat.choose (2 * r - 2) (r - 1) / 2

/-- Edge count of Alon's counterexample hypergraph for uniformity `r`:
`C(2r - 2, r) + C(2r - 2, r - 1) = C(2r - 1, r)`. -/
def alonEdgeCount (r : ℕ) : ℕ :=
  Nat.choose (2 * r - 2) r + Nat.choose (2 * r - 2) (r - 1)

/-! ## Foundational Universal Lemmas -/

/-- The empty hypergraph is properly coloured by any function. -/
theorem isProperColoring_empty {C : Type*} (c : V → C) :
    IsProperColoring (∅ : Finset (Finset V)) c := by
  intro e he
  simp at he

/-- The empty hypergraph is `k`-colourable for every `k ≥ 1`. -/
theorem isKColorable_empty {k : ℕ} (hk : 0 < k) :
    IsKColorable (∅ : Finset (Finset V)) k :=
  ⟨fun _ => ⟨0, hk⟩, isProperColoring_empty _⟩

/-- The empty hypergraph is 2-colourable. -/
theorem isTwoColorable_empty : IsTwoColorable (∅ : Finset (Finset V)) :=
  isKColorable_empty (by decide)

/-- The empty hypergraph is 3-colourable. -/
theorem isThreeColorable_empty : IsThreeColorable (∅ : Finset (Finset V)) :=
  isKColorable_empty (by decide)

/-- The empty hypergraph does not have chromatic number 3. -/
theorem not_hasChromaticNumberThree_empty :
    ¬ HasChromaticNumberThree (∅ : Finset (Finset V)) := by
  intro h
  exact h.2 isTwoColorable_empty

/-- Every non-2-colourable hypergraph is nonempty. -/
theorem nonempty_of_not_isTwoColorable {H : Finset (Finset V)} (h : ¬ IsTwoColorable H) :
    H.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  exact h isTwoColorable_empty

/-- Every 3-chromatic hypergraph is nonempty. -/
theorem nonempty_of_hasChromaticNumberThree {H : Finset (Finset V)}
    (h : HasChromaticNumberThree H) : H.Nonempty :=
  nonempty_of_not_isTwoColorable h.2

/-- Proper colourings are hereditary under sub-hypergraph inclusion `H₁ ⊆ H₂`. -/
theorem isProperColoring_mono {H₁ H₂ : Finset (Finset V)} (hsub : H₁ ⊆ H₂)
    {C : Type*} {c : V → C} (hc : IsProperColoring H₂ c) :
    IsProperColoring H₁ c :=
  fun e he => hc e (hsub he)

/-- `k`-colourability is hereditary under sub-hypergraph inclusion `H₁ ⊆ H₂`. -/
theorem isKColorable_mono {H₁ H₂ : Finset (Finset V)} (hsub : H₁ ⊆ H₂)
    {k : ℕ} (h : IsKColorable H₂ k) : IsKColorable H₁ k := by
  rcases h with ⟨c, hc⟩
  exact ⟨c, isProperColoring_mono hsub hc⟩

/-- 2-colourability is hereditary under sub-hypergraph inclusion `H₁ ⊆ H₂`. -/
theorem isTwoColorable_mono {H₁ H₂ : Finset (Finset V)} (hsub : H₁ ⊆ H₂)
    (h : IsTwoColorable H₂) : IsTwoColorable H₁ :=
  isKColorable_mono hsub h

/-- `k`-colourability is monotone in the number of available colours `k₁ ≤ k₂`. -/
theorem isKColorable_mono_colors {H : Finset (Finset V)} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : IsKColorable H k₁) : IsKColorable H k₂ := by
  rcases h with ⟨c, hc⟩
  refine ⟨fun v => Fin.castLE hk (c v), ?_⟩
  intro e he
  rcases hc e he with ⟨u, hu, v, hv, huv⟩
  refine ⟨u, hu, v, hv, ?_⟩
  intro heq
  apply huv
  exact Fin.ext (by simpa using congrArg Fin.val heq)

/-- Every 2-colourable hypergraph is 3-colourable. -/
theorem isThreeColorable_of_isTwoColorable {H : Finset (Finset V)}
    (h : IsTwoColorable H) : IsThreeColorable H :=
  isKColorable_mono_colors (by decide) h

/-- The intersecting property is hereditary under sub-hypergraph inclusion `H₁ ⊆ H₂`. -/
theorem isIntersecting_mono [DecidableEq V] {H₁ H₂ : Finset (Finset V)} (hsub : H₁ ⊆ H₂)
    (h : IsIntersecting H₂) : IsIntersecting H₁ :=
  fun e₁ he₁ e₂ he₂ => h e₁ (hsub he₁) e₂ (hsub he₂)

/-- Every vertex in an edge `e ∈ H` belongs to `activeVertices H`. -/
theorem mem_activeVertices_of_mem_edge [DecidableEq V] {H : Finset (Finset V)} {e : Finset V}
    {v : V} (he : e ∈ H) (hv : v ∈ e) : v ∈ activeVertices H := by
  simpa [activeVertices] using ⟨e, he, hv⟩

/-- For any `r`-uniform hypergraph `H`, the number of active vertices is at most `|H| * r`. -/
theorem card_activeVertices_le_card_mul_r [DecidableEq V] {r : ℕ} {H : Finset (Finset V)}
    (hunif : IsUniform r H) :
    (activeVertices H).card ≤ H.card * r := by
  unfold activeVertices
  calc
    (H.biUnion id).card ≤ ∑ e ∈ H, (id e).card := Finset.card_biUnion_le
    _ = ∑ _e ∈ H, r := by
      refine Finset.sum_congr rfl (fun e he => ?_)
      exact hunif e he
    _ = H.card * r := by simp

/-- Any intersecting hypergraph with at least two edges has a pair of distinct edges meeting
in at least 1 vertex. -/
theorem hasPairwiseIntersectionAtLeast_one_of_isIntersecting [DecidableEq V]
    {H : Finset (Finset V)} (hinter : IsIntersecting H) (hcard : 1 < H.card) :
    HasPairwiseIntersectionAtLeast H 1 := by
  obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp hcard
  refine ⟨e₁, he₁, e₂, he₂, hne, ?_⟩
  exact Finset.Nonempty.card_pos (hinter e₁ he₁ e₂ he₂)

/-- Alon's edge count identity: `alonEdgeCount r = C(2r - 1, r)` for all `r ≥ 1`. -/
theorem alonEdgeCount_eq_choose (r : ℕ) (hr : 1 ≤ r) :
    alonEdgeCount r = Nat.choose (2 * r - 1) r := by
  unfold alonEdgeCount
  have h1 : (2 * r - 2).succ = 2 * r - 1 := by omega
  have h2 : (r - 1).succ = r := by omega
  have hchoose := Nat.choose_succ_succ (2 * r - 2) (r - 1)
  rw [h1, h2] at hchoose
  omega


/-! ## Unified from `IntersectingThreeChromaticHypergraphAndLovaszBounds836.lean` -/

variable {V : Type*}

/-! ## Decidability Instances for Finite Verification -/

instance instDecidableIsUniform [DecidableEq V] (r : ℕ) (H : Finset (Finset V)) :
    Decidable (IsUniform r H) :=
  inferInstanceAs (Decidable (∀ e ∈ H, e.card = r))

instance instDecidableIsIntersecting [DecidableEq V] (H : Finset (Finset V)) :
    Decidable (IsIntersecting H) :=
  inferInstanceAs (Decidable (∀ e₁ ∈ H, ∀ e₂ ∈ H, (e₁ ∩ e₂).Nonempty))

instance instDecidableIsProperColoring [DecidableEq V] (H : Finset (Finset V))
    {C : Type*} [DecidableEq C] (c : V → C) :
    Decidable (IsProperColoring H c) :=
  inferInstanceAs (Decidable (∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v))

instance instDecidableIsKColorable [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (k : ℕ) :
    Decidable (IsKColorable H k) :=
  inferInstanceAs (Decidable (∃ c : V → Fin k, IsProperColoring H c))

instance instDecidableIsTwoColorable [Fintype V] [DecidableEq V] (H : Finset (Finset V)) :
    Decidable (IsTwoColorable H) :=
  inferInstanceAs (Decidable (IsKColorable H 2))

instance instDecidableIsThreeColorable [Fintype V] [DecidableEq V] (H : Finset (Finset V)) :
    Decidable (IsThreeColorable H) :=
  inferInstanceAs (Decidable (IsKColorable H 3))

instance instDecidableHasChromaticNumberThree [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) :
    Decidable (HasChromaticNumberThree H) :=
  inferInstanceAs (Decidable (IsThreeColorable H ∧ ¬ IsTwoColorable H))

instance instDecidableHasPairwiseIntersectionAtLeast [DecidableEq V]
    (H : Finset (Finset V)) (k : ℕ) :
    Decidable (HasPairwiseIntersectionAtLeast H k) :=
  inferInstanceAs (Decidable (∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ k ≤ (e₁ ∩ e₂).card))

instance instDecidableIsLinearHypergraph [DecidableEq V] (H : Finset (Finset V)) :
    Decidable (IsLinearHypergraph H) :=
  inferInstanceAs (Decidable (∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1))

/-! ## Section 1: Universal Star 2-Colourability & Maximum Degree Bound -/

/-- The 2-colouring associated with a star centre `v₀`: `v₀` receives colour `0` and all
other vertices receive colour `1`. -/
def starColoring [DecidableEq V] (v₀ : V) : V → Fin 2 :=
  fun u => if u = v₀ then 0 else 1

/-- If `H` is an `r`-uniform hypergraph (`r ≥ 2`) and `v₀` belongs to every hyperedge of `H`,
then `starColoring v₀` is a proper 2-colouring of `H`. -/
theorem isProperColoring_starColoring [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) {v₀ : V} (hstar : IsStarAt H v₀) :
    IsProperColoring H (starColoring v₀) := by
  intro e he
  have hcard : e.card = r := hunif e he
  have hv₀ : v₀ ∈ e := hstar e he
  have herase_card : (e.erase v₀).card = r - 1 := by
    rw [Finset.card_erase_of_mem hv₀, hcard]
  have herase_pos : 0 < (e.erase v₀).card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp herase_pos
  have hu_mem : u ∈ e := Finset.mem_of_mem_erase hu
  have hu_ne : u ≠ v₀ := Finset.ne_of_mem_erase hu
  refine ⟨v₀, hv₀, u, hu_mem, ?_⟩
  simp [starColoring, hu_ne]

/-- Every `r`-uniform star hypergraph (`r ≥ 2`) is 2-colourable. -/
theorem isTwoColorable_of_isStarAt [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) {v₀ : V} (hstar : IsStarAt H v₀) :
    IsTwoColorable H :=
  ⟨starColoring v₀, isProperColoring_starColoring hr hunif hstar⟩

/-- In any non-2-colourable `r`-uniform hypergraph (`r ≥ 2`), no vertex belongs to all edges. -/
theorem not_isStarAt_of_not_isTwoColorable [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H) (v : V) :
    ¬ IsStarAt H v :=
  fun hstar => hnot2 (isTwoColorable_of_isStarAt hr hunif hstar)

/-- In any non-2-colourable `r`-uniform hypergraph (`r ≥ 2`), for every vertex `v`, there
exists an edge `e ∈ H` not containing `v`. -/
theorem exists_edge_not_mem_of_not_isTwoColorable [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H) (v : V) :
    ∃ e ∈ H, v ∉ e := by
  have hnot := not_isStarAt_of_not_isTwoColorable hr hunif hnot2 v
  unfold IsStarAt at hnot
  push Not at hnot
  exact hnot

/-- In any 3-chromatic `r`-uniform hypergraph (`r ≥ 2`), for every vertex `v`, there
exists an edge `e ∈ H` not containing `v`. -/
theorem exists_edge_not_mem_of_hasChromaticNumberThree [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hchrom : HasChromaticNumberThree H) (v : V) :
    ∃ e ∈ H, v ∉ e :=
  exists_edge_not_mem_of_not_isTwoColorable hr hunif hchrom.2 v

/-- Universal Maximum Degree Bound: in any non-2-colourable `r`-uniform hypergraph (`r ≥ 2`),
every vertex `v` satisfies `vertexDegree H v + 1 ≤ H.card` (`Δ(H) ≤ |E(H)| - 1`). -/
theorem vertexDegree_add_one_le_card_of_not_isTwoColorable [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H) (v : V) :
    vertexDegree H v + 1 ≤ H.card := by
  obtain ⟨e₀, he₀, hv₀⟩ := exists_edge_not_mem_of_not_isTwoColorable hr hunif hnot2 v
  have hsub : H.filter (fun e => v ∈ e) ⊆ H.erase e₀ := by
    intro e he
    simp only [Finset.mem_filter] at he
    rw [Finset.mem_erase]
    refine ⟨?_, he.1⟩
    rintro rfl
    exact hv₀ he.2
  have hle := Finset.card_le_card hsub
  have herase : (H.erase e₀).card + 1 = H.card := Finset.card_erase_add_one he₀
  unfold vertexDegree
  omega

/-- Universal Maximum Degree Bound for 3-chromatic `r`-uniform hypergraphs (`r ≥ 2`):
`vertexDegree H v + 1 ≤ H.card`. -/
theorem vertexDegree_add_one_le_card_of_hasChromaticNumberThree [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hchrom : HasChromaticNumberThree H) (v : V) :
    vertexDegree H v + 1 ≤ H.card :=
  vertexDegree_add_one_le_card_of_not_isTwoColorable hr hunif hchrom.2 v

/-! ## Section 2: Transversal Characterization & Exact Transversal Number `τ(H) = r` -/

/-- Indicator 2-colouring of a subset `T : Finset V`: vertices in `T` receive `0`, and vertices
outside `T` receive `1`. -/
def subsetColoring [DecidableEq V] (T : Finset V) : V → Fin 2 :=
  fun u => if u ∈ T then 0 else 1

/-- If `T` is a transversal of `H` that contains no hyperedge of `H`, then `subsetColoring T`
is a proper 2-colouring of `H`. -/
theorem isProperColoring_subsetColoring_of_isTransversal [DecidableEq V]
    {H : Finset (Finset V)} {T : Finset V} (htrans : IsTransversal H T)
    (hno_sub : ∀ e ∈ H, ¬ e ⊆ T) :
    IsProperColoring H (subsetColoring T) := by
  intro e he
  obtain ⟨u, hu⟩ := htrans e he
  obtain ⟨hu_e, hu_T⟩ := Finset.mem_inter.mp hu
  obtain ⟨v, hv_e, hv_not_T⟩ := Finset.not_subset.mp (hno_sub e he)
  refine ⟨u, hu_e, v, hv_e, ?_⟩
  simp [subsetColoring, hu_T, hv_not_T]

/-- In any non-2-colourable hypergraph `H`, every transversal `T` of `H` must contain at least
one entire hyperedge `e ∈ H`. -/
theorem exists_edge_subset_of_isTransversal_of_not_isTwoColorable [DecidableEq V]
    {H : Finset (Finset V)} (hnot2 : ¬ IsTwoColorable H) {T : Finset V}
    (htrans : IsTransversal H T) :
    ∃ e ∈ H, e ⊆ T := by
  by_contra hno
  push Not at hno
  exact hnot2 ⟨subsetColoring T, isProperColoring_subsetColoring_of_isTransversal htrans hno⟩

/-- Universal Transversal Lower Bound (`τ(H) ≥ r`): in any non-2-colourable `r`-uniform
hypergraph `H`, every transversal `T` has cardinality at least `r`. -/
theorem card_transversal_ge_r_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H)
    {T : Finset V} (htrans : IsTransversal H T) :
    r ≤ T.card := by
  obtain ⟨e, he, hsub⟩ := exists_edge_subset_of_isTransversal_of_not_isTwoColorable hnot2 htrans
  rw [← hunif e he]
  exact Finset.card_le_card hsub

/-- Universal Disjoint-Edge Guarantee (Erdős–Lovász Branching Step): in any non-2-colourable
`r`-uniform hypergraph `H`, for every vertex set `S` of size `S.card < r`, there exists a
hyperedge `e ∈ H` completely disjoint from `S`. -/
theorem exists_disjoint_edge_of_card_lt_r_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H)
    {S : Finset V} (hS : S.card < r) :
    ∃ e ∈ H, Disjoint e S := by
  have hnot_trans : ¬ IsTransversal H S := by
    intro htrans
    have hge := card_transversal_ge_r_of_not_isTwoColorable hunif hnot2 htrans
    omega
  unfold IsTransversal at hnot_trans
  push Not at hnot_trans
  rcases hnot_trans with ⟨e, he, hempty⟩
  exact ⟨e, he, Finset.disjoint_iff_inter_eq_empty.mpr hempty⟩

/-- In any intersecting hypergraph `H`, every hyperedge `e₀ ∈ H` is a transversal of `H`. -/
theorem isTransversal_of_mem_of_isIntersecting [DecidableEq V]
    {H : Finset (Finset V)} (hinter : IsIntersecting H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    IsTransversal H e₀ :=
  fun e he => hinter e he e₀ he₀

/-- In any non-2-colourable intersecting `r`-uniform hypergraph, the minimum transversal size
is achieved by every hyperedge and equals `r` (`∃ T, IsTransversal H T ∧ T.card = r`, and
`∀ T, IsTransversal H T → r ≤ T.card`). -/
theorem exists_transversal_card_eq_r_of_isIntersecting_of_not_isTwoColorable [DecidableEq V]
    {r : ℕ} {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) :
    (∃ T : Finset V, IsTransversal H T ∧ T.card = r) ∧
      (∀ T : Finset V, IsTransversal H T → r ≤ T.card) := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  refine ⟨⟨e₀, isTransversal_of_mem_of_isIntersecting hinter he₀, hunif e₀ he₀⟩, ?_⟩
  intro T hT
  exact card_transversal_ge_r_of_not_isTwoColorable hunif hnot2 hT

/-! ## Section 3: Universal 3-Colourability of Intersecting `r`-Uniform Hypergraphs (`r ≥ 2`) -/

/-- Canonical 3-colouring induced by a base edge `e₀` and distinguished vertex `v₀ ∈ e₀`:
`v₀` receives colour `0`, `e₀ \ {v₀}` receives colour `1`, and `V \ e₀` receives colour `2`. -/
def edgeAnchorThreeColoring [DecidableEq V] (e₀ : Finset V) (v₀ : V) : V → Fin 3 :=
  fun u => if u = v₀ then 0 else if u ∈ e₀ then 1 else 2

/-- For any intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), any edge `e₀ ∈ H`, and any
vertex `v₀ ∈ e₀`, `edgeAnchorThreeColoring e₀ v₀` is a proper 3-colouring of `H`. -/
theorem isProperColoring_edgeAnchorThreeColoring [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v₀ : V} (hv₀ : v₀ ∈ e₀) :
    IsProperColoring H (edgeAnchorThreeColoring e₀ v₀) := by
  intro e he
  have he_card : e.card = r := hunif e he
  have he₀_card : e₀.card = r := hunif e₀ he₀
  by_cases hv_in : v₀ ∈ e
  · have herase_pos : 0 < (e.erase v₀).card := by
      rw [Finset.card_erase_of_mem hv_in, he_card]
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp herase_pos
    have hu_mem : u ∈ e := Finset.mem_of_mem_erase hu
    have hu_ne : u ≠ v₀ := Finset.ne_of_mem_erase hu
    refine ⟨v₀, hv_in, u, hu_mem, ?_⟩
    by_cases hu_e₀ : u ∈ e₀ <;> simp [edgeAnchorThreeColoring, hu_ne, hu_e₀]
  · obtain ⟨x, hx⟩ := hinter e he e₀ he₀
    obtain ⟨hx_e, hx_e₀⟩ := Finset.mem_inter.mp hx
    have hx_ne : x ≠ v₀ := fun h => hv_in (h ▸ hx_e)
    have hnot_sub : ¬ e ⊆ e₀.erase v₀ := by
      intro hsub
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hv₀, he_card, he₀_card] at hle
      omega
    obtain ⟨y, hy_e, hy_not_erase⟩ := Finset.not_subset.mp hnot_sub
    have hy_ne : y ≠ v₀ := fun h => hv_in (h ▸ hy_e)
    have hy_not_e₀ : y ∉ e₀ := fun hy_e₀ =>
      hy_not_erase (Finset.mem_erase.mpr ⟨hy_ne, hy_e₀⟩)
    refine ⟨x, hx_e, y, hy_e, ?_⟩
    simp [edgeAnchorThreeColoring, hx_ne, hx_e₀, hy_ne, hy_not_e₀]

/-- **Universal 3-Colourability Theorem**: Every intersecting `r`-uniform hypergraph (`r ≥ 2`)
is 3-colourable (`χ(H) ≤ 3`). -/
theorem isThreeColorable_of_isIntersecting [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H) :
    IsThreeColorable H := by
  by_cases hne : H.Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    have he₀_pos : 0 < e₀.card := by
      rw [hunif e₀ he₀]
      omega
    obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp he₀_pos
    exact ⟨edgeAnchorThreeColoring e₀ v₀,
      isProperColoring_edgeAnchorThreeColoring hr hunif hinter he₀ hv₀⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact isThreeColorable_empty

/-- For any intersecting `r`-uniform hypergraph (`r ≥ 2`), having chromatic number 3 is
equivalent to not being 2-colourable. -/
theorem hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) :
    HasChromaticNumberThree H ↔ ¬ IsTwoColorable H :=
  ⟨fun h => h.2, fun h => ⟨isThreeColorable_of_isIntersecting hr hunif hinter, h⟩⟩

/-! ## Section 4: Minimum Edge Count & Erdős–Lovász Degree-Sum / Pigeonhole Bounds -/

/-- Every intersecting `r`-uniform hypergraph (`r ≥ 2`) with at most 2 edges is 2-colourable. -/
theorem isTwoColorable_of_isIntersecting_of_card_le_two [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hcard : H.card ≤ 2) :
    IsTwoColorable H := by
  by_cases hne : H.Nonempty
  · obtain ⟨e₁, he₁⟩ := hne
    by_cases hne2 : (H.erase e₁).Nonempty
    · obtain ⟨e₂, he₂_erase⟩ := hne2
      have he₂ : e₂ ∈ H := Finset.mem_of_mem_erase he₂_erase
      obtain ⟨v₀, hv₀⟩ := hinter e₁ he₁ e₂ he₂
      obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv₀
      have herase_le : (H.erase e₁).card ≤ 1 := by
        have h1 := Finset.card_erase_add_one he₁
        omega
      have hstar : IsStarAt H v₀ := by
        intro e he
        by_cases he_eq : e = e₁
        · subst he_eq; exact hv₁
        · have he_in_erase : e ∈ H.erase e₁ := Finset.mem_erase.mpr ⟨he_eq, he⟩
          have he_eq₂ : e = e₂ :=
            Finset.card_le_one.mp herase_le e he_in_erase e₂ he₂_erase
          subst he_eq₂; exact hv₂
      exact isTwoColorable_of_isStarAt hr hunif hstar
    · rw [Finset.not_nonempty_iff_eq_empty] at hne2
      have he₁_pos : 0 < e₁.card := by rw [hunif e₁ he₁]; omega
      obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp he₁_pos
      have hstar : IsStarAt H v₀ := by
        intro e he
        by_cases he_eq : e = e₁
        · subst he_eq; exact hv₀
        · exfalso
          have he_in_erase : e ∈ H.erase e₁ := Finset.mem_erase.mpr ⟨he_eq, he⟩
          rw [hne2] at he_in_erase
          simp at he_in_erase
      exact isTwoColorable_of_isStarAt hr hunif hstar
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact isTwoColorable_empty

/-- Universal Minimum Edge Count: every non-2-colourable (or 3-chromatic) intersecting
`r`-uniform hypergraph (`r ≥ 2`) has at least `3` edges. -/
theorem card_ge_three_of_isIntersecting_of_not_isTwoColorable [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) :
    3 ≤ H.card := by
  by_contra hlt
  have hle : H.card ≤ 2 := by omega
  exact hnot2 (isTwoColorable_of_isIntersecting_of_card_le_two hr hunif hinter hle)

/-- Double-counting identity for the sum of vertex degrees over an arbitrary finite set `S`:
`∑ v ∈ S, vertexDegree H v = ∑ e ∈ H, (e ∩ S).card`. -/
theorem sum_vertexDegree_eq_sum_card_inter [DecidableEq V] (H : Finset (Finset V)) (S : Finset V) :
    ∑ v ∈ S, vertexDegree H v = ∑ e ∈ H, (e ∩ S).card := by
  unfold vertexDegree
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.sum_filter]
  have hfilter : S.filter (fun v => v ∈ e) = e ∩ S := by
    ext v
    simp [Finset.mem_inter, and_comm]
  rw [hfilter]

/-- For any transversal `T` of `H`, the sum of vertex degrees over `T` is at least `H.card`. -/
theorem card_le_sum_vertexDegree_of_isTransversal [DecidableEq V]
    {H : Finset (Finset V)} {T : Finset V} (htrans : IsTransversal H T) :
    H.card ≤ ∑ v ∈ T, vertexDegree H v := by
  rw [sum_vertexDegree_eq_sum_card_inter, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum (fun e he => ?_)
  exact Finset.Nonempty.card_pos (htrans e he)

/-- In any intersecting hypergraph `H`, for every edge `e₀ ∈ H`, the sum of vertex degrees
over `e₀` is at least `H.card`. -/
theorem card_le_sum_vertexDegree_of_mem_of_isIntersecting [DecidableEq V]
    {H : Finset (Finset V)} (hinter : IsIntersecting H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    H.card ≤ ∑ v ∈ e₀, vertexDegree H v :=
  card_le_sum_vertexDegree_of_isTransversal (isTransversal_of_mem_of_isIntersecting hinter he₀)

/-- **Erdős–Lovász First Pigeonhole Step (1975)**: In any intersecting `r`-uniform hypergraph `H`
(`r ≥ 1`), every hyperedge `e₀ ∈ H` contains a vertex `v ∈ e₀` whose degree satisfies
`H.card ≤ r * vertexDegree H v`. -/
theorem exists_vertex_in_edge_mul_degree_ge_card [DecidableEq V] {r : ℕ} (hr : 1 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∃ v ∈ e₀, H.card ≤ r * vertexDegree H v := by
  have he₀_card : e₀.card = r := hunif e₀ he₀
  have he₀_ne : e₀.Nonempty := Finset.card_pos.mp (by omega)
  have hsum : H.card ≤ ∑ v ∈ e₀, vertexDegree H v :=
    card_le_sum_vertexDegree_of_mem_of_isIntersecting hinter he₀
  obtain ⟨v₀, hv₀, hmax⟩ := Finset.exists_max_image e₀ (vertexDegree H) he₀_ne
  refine ⟨v₀, hv₀, ?_⟩
  have hsum_le : ∑ v ∈ e₀, vertexDegree H v ≤ ∑ _v ∈ e₀, vertexDegree H v₀ :=
    Finset.sum_le_sum (fun v hv => hmax v hv)
  simp only [Finset.sum_const, smul_eq_mul, he₀_card] at hsum_le
  omega

/-- **Universal Small-Order Property B Theorem (`|V(H)| ≤ 2r - 2 ⟹ χ(H) ≤ 2`)**:
Every `r`-uniform hypergraph (`r ≥ 1`) with at most `2r - 2` active vertices is 2-colourable.
In particular:
- For `r = 2`, every 2-uniform hypergraph on `≤ 2` active vertices is 2-colourable;
- For `r = 3`, every 3-uniform hypergraph on `≤ 4` active vertices is 2-colourable;
- For `r = 4`, every 4-uniform hypergraph on `≤ 6` active vertices is 2-colourable. -/
theorem isTwoColorable_of_card_activeVertices_le_two_mul_r_sub_two [DecidableEq V]
    {r : ℕ} (hr : 1 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hcard : (activeVertices H).card ≤ 2 * r - 2) :
    IsTwoColorable H := by
  by_cases hne : H.Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    have he₀_sub : e₀ ⊆ activeVertices H := fun x hx => mem_activeVertices_of_mem_edge he₀ hx
    have he₀_le : r ≤ (activeVertices H).card := by
      rw [← hunif e₀ he₀]
      exact Finset.card_le_card he₀_sub
    have hsub_ex : r - 1 ≤ (activeVertices H).card := by omega
    obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hsub_ex
    refine ⟨subsetColoring S, ?_⟩
    intro e he
    have he_card : e.card = r := hunif e he
    have he_sub : e ⊆ activeVertices H := fun x hx => mem_activeVertices_of_mem_edge he hx
    have hnot_sub_S : ¬ e ⊆ S := by
      intro hsub
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨v, hv_e, hv_not_S⟩ := Finset.not_subset.mp hnot_sub_S
    have hnot_sub_sdiff : ¬ e ⊆ activeVertices H \ S := by
      intro hsub
      have hle := Finset.card_le_card hsub
      have hsdiff : (activeVertices H \ S).card = (activeVertices H).card - S.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub]
      omega
    obtain ⟨u, hu_e, hu_not_sdiff⟩ := Finset.not_subset.mp hnot_sub_sdiff
    have hu_A : u ∈ activeVertices H := he_sub hu_e
    have hu_S : u ∈ S := by
      by_contra hu_not_S
      exact hu_not_sdiff (Finset.mem_sdiff.mpr ⟨hu_A, hu_not_S⟩)
    refine ⟨u, hu_e, v, hv_e, ?_⟩
    simp [subsetColoring, hu_S, hv_not_S]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact isTwoColorable_empty

/-- **Universal Active-Vertex Lower Bound (`|V(H)| ≥ 2r - 1`)**:
Every non-2-colourable (in particular, 3-chromatic) `r`-uniform hypergraph (`r ≥ 1`) has at
least `2r - 1` active vertices. -/
theorem two_mul_r_sub_one_le_card_activeVertices_of_not_isTwoColorable [DecidableEq V]
    {r : ℕ} (hr : 1 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hnot2 : ¬ IsTwoColorable H) :
    2 * r - 1 ≤ (activeVertices H).card := by
  by_contra hlt
  have hle : (activeVertices H).card ≤ 2 * r - 2 := by omega
  exact hnot2 (isTwoColorable_of_card_activeVertices_le_two_mul_r_sub_two hr hunif hle)

/-! ## Section 5: Concrete Verified Extremal & Counterexample Witnesses (`r = 2, 3`) -/

/-- Finite subset formulation of Property B (`IsTwoColorable`): there exists a vertex subset `S`
that both intersects and fails to contain every edge `e ∈ H`. -/
def HasProperBipartition [Fintype V] [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∃ S ∈ (Finset.univ : Finset V).powerset, ∀ e ∈ H, (e ∩ S).Nonempty ∧ ¬ e ⊆ S

instance instDecidableHasProperBipartition [Fintype V] [DecidableEq V] (H : Finset (Finset V)) :
    Decidable (HasProperBipartition H) :=
  inferInstanceAs (Decidable (∃ S ∈ (Finset.univ : Finset V).powerset,
    ∀ e ∈ H, (e ∩ S).Nonempty ∧ ¬ e ⊆ S))

/-- Universal equivalence between `IsTwoColorable` and `HasProperBipartition`. -/
theorem isTwoColorable_iff_hasProperBipartition [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) :
    IsTwoColorable H ↔ HasProperBipartition H := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Finset.univ.filter (fun v => c v = 0), Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    intro e he
    rcases hc e he with ⟨u, hu, v, hv, huv⟩
    by_cases hcu : c u = 0
    · have hcv : c v ≠ 0 := fun h => huv (hcu.trans h.symm)
      refine ⟨⟨u, Finset.mem_inter.mpr ⟨hu, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hcu⟩⟩⟩,
        fun hsub => hcv (Finset.mem_filter.mp (hsub hv)).2⟩
    · have hcv : c v = 0 := by
        have h1 : (c u).val < 2 := (c u).isLt
        have h2 : (c v).val < 2 := (c v).isLt
        have hne_val : (c u).val ≠ (c v).val := fun h => huv (Fin.ext h)
        have hcu_ne : (c u).val ≠ 0 := fun h => hcu (Fin.ext h)
        exact Fin.ext (by omega)
      refine ⟨⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcv⟩⟩⟩,
        fun hsub => hcu (Finset.mem_filter.mp (hsub hu)).2⟩
  · rintro ⟨S, _, hS⟩
    refine ⟨subsetColoring S, ?_⟩
    intro e he
    rcases hS e he with ⟨⟨u, hu⟩, hnot_sub⟩
    obtain ⟨hu_e, hu_S⟩ := Finset.mem_inter.mp hu
    obtain ⟨v, hv_e, hv_not_S⟩ := Finset.not_subset.mp hnot_sub
    refine ⟨u, hu_e, v, hv_e, ?_⟩
    simp [subsetColoring, hu_S, hv_not_S]

/-- For `r = 2`, the complete graph `K₃` on `Fin 3` (`3` vertices, `3` edges). -/
def triangleK3 : Finset (Finset (Fin 3)) :=
  {{0, 1}, {1, 2}, {0, 2}}

theorem triangleK3_card : triangleK3.card = 3 := by decide

theorem triangleK3_isUniform : IsUniform 2 triangleK3 := by decide

theorem triangleK3_isIntersecting : IsIntersecting triangleK3 := by decide

theorem triangleK3_not_isTwoColorable : ¬ IsTwoColorable triangleK3 := by decide

theorem triangleK3_hasChromaticNumberThree : HasChromaticNumberThree triangleK3 :=
  (hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting (by decide)
    triangleK3_isUniform triangleK3_isIntersecting).mpr triangleK3_not_isTwoColorable

/-- For `r = 3` and `n = 5`, the complete 3-uniform hypergraph `K₅^(3)` (`10` edges). -/
def completeFive3 : Finset (Finset (Fin 5)) :=
  (Finset.univ : Finset (Fin 5)).powersetCard 3

theorem completeFive3_card : completeFive3.card = 10 := by decide

theorem completeFive3_isUniform : IsUniform 3 completeFive3 := by decide

theorem completeFive3_isIntersecting : IsIntersecting completeFive3 := by decide

theorem completeFive3_not_isTwoColorable : ¬ IsTwoColorable completeFive3 := by decide

theorem completeFive3_hasChromaticNumberThree : HasChromaticNumberThree completeFive3 :=
  (hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting (by decide)
    completeFive3_isUniform completeFive3_isIntersecting).mpr completeFive3_not_isTwoColorable

/-- The Fano plane `PG(2, 2)` on `Fin 7`: `7` vertices, `7` hyperedges of size `3`, generated by
cyclic shifts of `{0, 1, 3} mod 7`. -/
def fanoPlane : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}}

theorem fanoPlane_card : fanoPlane.card = 7 := by decide

theorem fanoPlane_isUniform : IsUniform 3 fanoPlane := by decide

theorem fanoPlane_isIntersecting : IsIntersecting fanoPlane := by decide

theorem fanoPlane_isLinearHypergraph : IsLinearHypergraph fanoPlane := by decide

theorem fanoPlane_not_hasPairwiseIntersectionAtLeast_two :
    ¬ HasPairwiseIntersectionAtLeast fanoPlane 2 := by decide

theorem fanoPlane_not_hasProperBipartition : ¬ HasProperBipartition fanoPlane := by decide

theorem fanoPlane_not_isTwoColorable : ¬ IsTwoColorable fanoPlane :=
  fun h => fanoPlane_not_hasProperBipartition ((isTwoColorable_iff_hasProperBipartition fanoPlane).mp h)

theorem fanoPlane_hasChromaticNumberThree : HasChromaticNumberThree fanoPlane :=
  (hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting (by decide)
    fanoPlane_isUniform fanoPlane_isIntersecting).mpr fanoPlane_not_isTwoColorable

/-- Formal verification of Erdős and Shelah's remark for `r = 3`: the Fano geometry `PG(2, 2)`
is a 3-chromatic intersecting 3-uniform hypergraph in which no two distinct edges meet in
`r - 1 = 2` vertices. -/
theorem hasCodimensionOneAvoidingWitness_three : HasCodimensionOneAvoidingWitness 3 :=
  ⟨7, fanoPlane, fanoPlane_isUniform, fanoPlane_isIntersecting,
    fanoPlane_hasChromaticNumberThree, fanoPlane_not_hasPairwiseIntersectionAtLeast_two⟩

/-- Alon's equitable-partition hypergraph construction instantiated at `r = 3` on `Fin 7`:
`X = {0, 1, 2, 3}` (`|X| = 4`) and `Y = {4, 5, 6}` (`|Y| = 3`, indexing the `3` equitable
2-partitions `{0,1}|{2,3}`, `{0,2}|{1,3}`, `{0,3}|{1,2}` of `X`), with `4 + 6 = 10` edges. -/
def alonHypergraph3 : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3},
   {0, 1, 4}, {2, 3, 4}, {0, 2, 5}, {1, 3, 5}, {0, 3, 6}, {1, 2, 6}}

theorem alonHypergraph3_card : alonHypergraph3.card = alonEdgeCount 3 := by decide

theorem alonHypergraph3_activeVertices_card :
    (activeVertices alonHypergraph3).card = alonVertexCount 3 := by decide

theorem alonHypergraph3_isUniform : IsUniform 3 alonHypergraph3 := by decide

theorem alonHypergraph3_isIntersecting : IsIntersecting alonHypergraph3 := by decide

theorem alonHypergraph3_not_hasProperBipartition : ¬ HasProperBipartition alonHypergraph3 := by decide

theorem alonHypergraph3_not_isTwoColorable : ¬ IsTwoColorable alonHypergraph3 :=
  fun h => alonHypergraph3_not_hasProperBipartition
    ((isTwoColorable_iff_hasProperBipartition alonHypergraph3).mp h)

theorem alonHypergraph3_hasChromaticNumberThree : HasChromaticNumberThree alonHypergraph3 :=
  (hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting (by decide)
    alonHypergraph3_isUniform alonHypergraph3_isIntersecting).mpr alonHypergraph3_not_isTwoColorable


/-! ## Unified from `AlonEquitablePartitionAndErdosLovaszBranchingBounds836.lean` -/

/-! ## Section 1: Handshake & Co-Degree Identities -/

/-- Universal Handshake Identity on Active Vertices: for any `r`-uniform hypergraph `H`,
the sum of vertex degrees over `activeVertices H` equals `H.card * r`. -/
theorem sum_vertexDegree_activeVertices_eq_card_mul_r [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) :
    ∑ v ∈ activeVertices H, vertexDegree H v = H.card * r := by
  rw [sum_vertexDegree_eq_sum_card_inter]
  have hcongr : ∑ e ∈ H, (e ∩ activeVertices H).card = ∑ _e ∈ H, r := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hsub : e ⊆ activeVertices H := fun x hx => mem_activeVertices_of_mem_edge he hx
    rw [Finset.inter_eq_left.mpr hsub, hunif e he]
  rw [hcongr, Finset.sum_const, smul_eq_mul]

/-- Universal Full-Universe Handshake Identity: for any `r`-uniform hypergraph `H` on a finite
vertex type `V`, the sum of vertex degrees over `Finset.univ` equals `H.card * r`. -/
theorem sum_vertexDegree_univ_eq_card_mul_r [Fintype V] [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) :
    ∑ v : V, vertexDegree H v = H.card * r := by
  rw [sum_vertexDegree_eq_sum_card_inter]
  have hcongr : ∑ e ∈ H, (e ∩ Finset.univ).card = ∑ _e ∈ H, r := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [Finset.inter_univ, hunif e he]
  rw [hcongr, Finset.sum_const, smul_eq_mul]

/-- Universal Co-Degree Decomposition Identity: for any `r`-uniform hypergraph `H` and any edge
`e₀ ∈ H`, the sum of pairwise intersection sizes `(e ∩ e₀).card` over `e ∈ H.erase e₀` plus `r`
equals the sum of vertex degrees over `e₀`. -/
theorem sum_card_inter_erase_eq_sum_vertexDegree_sub_r [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    (∑ e ∈ H.erase e₀, (e ∩ e₀).card) + r = ∑ v ∈ e₀, vertexDegree H v := by
  rw [sum_vertexDegree_eq_sum_card_inter]
  have hsplit := Finset.sum_erase_add H (fun e => (e ∩ e₀).card) he₀
  rw [Finset.inter_self, hunif e₀ he₀] at hsplit
  exact hsplit

/-- In any intersecting hypergraph `H`, for every edge `e₀ ∈ H`, the sum of pairwise
intersection sizes over `H.erase e₀` is at least `H.card - 1`. -/
theorem card_le_sum_card_inter_erase_add_one_of_isIntersecting [DecidableEq V]
    {H : Finset (Finset V)} (hinter : IsIntersecting H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    H.card ≤ (∑ e ∈ H.erase e₀, (e ∩ e₀).card) + 1 := by
  have herase : (H.erase e₀).card + 1 = H.card := Finset.card_erase_add_one he₀
  have hsum : (H.erase e₀).card ≤ ∑ e ∈ H.erase e₀, (e ∩ e₀).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum (fun e he => ?_)
    exact Finset.Nonempty.card_pos (hinter e (Finset.mem_of_mem_erase he) e₀ he₀)
  omega

/-! ## Section 2: Erdős–Lovász Pairwise Intersection & Co-Degree Bounds -/

/-- **Erdős–Lovász Pairwise Overlap Degree-Sum Upper Bound**: If an `r`-uniform hypergraph `H`
has no two distinct edges meeting in `k + 1` or more vertices, then for every edge `e₀ ∈ H`,
`∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1) * k + r`. -/
theorem sum_vertexDegree_le_card_sub_one_mul_add_r_of_not_hasPairwiseIntersectionAtLeast
    [DecidableEq V] {r k : ℕ} {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (k + 1)) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1) * k + r := by
  rw [← sum_card_inter_erase_eq_sum_vertexDegree_sub_r hunif he₀]
  have hle : ∑ e ∈ H.erase e₀, (e ∩ e₀).card ≤ ∑ _e ∈ H.erase e₀, k := by
    refine Finset.sum_le_sum (fun e he => ?_)
    have he_mem : e ∈ H := Finset.mem_of_mem_erase he
    have he_ne : e ≠ e₀ := Finset.ne_of_mem_erase he
    by_contra hgt
    have hge : k + 1 ≤ (e ∩ e₀).card := by omega
    exact hno ⟨e, he_mem, e₀, he₀, he_ne, hge⟩
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem he₀] at hle
  omega

/-- **Pairwise Overlap Edge-Count Bound**: In any nonempty intersecting `r`-uniform hypergraph `H`
avoiding pairwise intersection `k + 1`, `H.card ≤ (H.card - 1) * k + r`. -/
theorem card_le_card_sub_one_mul_add_r_of_isIntersecting_of_not_hasPairwiseIntersectionAtLeast
    [DecidableEq V] {r k : ℕ} {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hno : ¬ HasPairwiseIntersectionAtLeast H (k + 1))
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    H.card ≤ (H.card - 1) * k + r := by
  have h1 := card_le_sum_vertexDegree_of_mem_of_isIntersecting hinter he₀
  have h2 := sum_vertexDegree_le_card_sub_one_mul_add_r_of_not_hasPairwiseIntersectionAtLeast
    hunif hno he₀
  omega

/-- **Erdős–Lovász Co-Degree Pigeonhole Theorem**: In any `r`-uniform hypergraph `H` with at
least 2 edges, for every edge `e₀ ∈ H`, there exists a distinct edge `e₁ ∈ H` (`e₁ ≠ e₀`) such
that `∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1) * (e₁ ∩ e₀).card + r`. -/
theorem exists_other_edge_mul_inter_ge_sum_vertexDegree_sub_r [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hcard : 2 ≤ H.card)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∃ e₁ ∈ H, e₁ ≠ e₀ ∧ ∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1) * (e₁ ∩ e₀).card + r := by
  have herase_pos : 0 < (H.erase e₀).card := by
    rw [Finset.card_erase_of_mem he₀]
    omega
  obtain ⟨e₁, he₁_erase, hmax⟩ :=
    Finset.exists_max_image (H.erase e₀) (fun e => (e ∩ e₀).card) (Finset.card_pos.mp herase_pos)
  refine ⟨e₁, Finset.mem_of_mem_erase he₁_erase, Finset.ne_of_mem_erase he₁_erase, ?_⟩
  rw [← sum_card_inter_erase_eq_sum_vertexDegree_sub_r hunif he₀]
  have hle : ∑ e ∈ H.erase e₀, (e ∩ e₀).card ≤ ∑ _e ∈ H.erase e₀, (e₁ ∩ e₀).card :=
    Finset.sum_le_sum (fun e he => hmax e he)
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem he₀] at hle
  omega

/-- **Sufficient Degree-Sum Criterion for Large Pairwise Intersection**: If `H` is an `r`-uniform
hypergraph and `e₀ ∈ H` satisfies `(H.card - 1) * k + r < ∑ v ∈ e₀, vertexDegree H v`, then `H`
contains two distinct edges meeting in at least `k + 1` vertices. -/
theorem hasPairwiseIntersectionAtLeast_of_sum_vertexDegree_gt [DecidableEq V] {r k : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) {e₀ : Finset V} (he₀ : e₀ ∈ H)
    (hgt : (H.card - 1) * k + r < ∑ v ∈ e₀, vertexDegree H v) :
    HasPairwiseIntersectionAtLeast H (k + 1) := by
  by_contra hno
  have hle := sum_vertexDegree_le_card_sub_one_mul_add_r_of_not_hasPairwiseIntersectionAtLeast
    hunif hno he₀
  omega

/-! ## Section 3: Exact Identities & Projective-Plane Bounds for Linear Intersecting Hypergraphs -/

/-- In any linear intersecting `r`-uniform hypergraph `H`, every pair of distinct edges meets in
exactly `1` vertex, so for every edge `e₀ ∈ H`, `∑ v ∈ e₀, vertexDegree H v = H.card - 1 + r`. -/
theorem sum_vertexDegree_eq_card_sub_one_add_r_of_isLinearHypergraph [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ v ∈ e₀, vertexDegree H v = H.card - 1 + r := by
  rw [← sum_card_inter_erase_eq_sum_vertexDegree_sub_r hunif he₀]
  have hcongr : ∑ e ∈ H.erase e₀, (e ∩ e₀).card = ∑ _e ∈ H.erase e₀, 1 := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    have he_mem : e ∈ H := Finset.mem_of_mem_erase he
    have he_ne : e ≠ e₀ := Finset.ne_of_mem_erase he
    have hge : 1 ≤ (e ∩ e₀).card := Finset.Nonempty.card_pos (hinter e he_mem e₀ he₀)
    have hle : (e ∩ e₀).card ≤ 1 := hlin e he_mem e₀ he₀ he_ne
    omega
  simp only [hcongr, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem he₀]

/-- In any linear intersecting `r`-uniform hypergraph `H`, for every edge `e₀ ∈ H` and every
vertex `v ∉ e₀`, `vertexDegree H v ≤ r`. -/
theorem vertexDegree_le_r_of_not_mem_edge_of_isLinearHypergraph [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∉ e₀) :
    vertexDegree H v ≤ r := by
  unfold vertexDegree
  have hsum : (H.filter (fun e => v ∈ e)).card ≤ ∑ e ∈ H.filter (fun e => v ∈ e), (e ∩ e₀).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum (fun e he => ?_)
    exact Finset.Nonempty.card_pos (hinter e (Finset.mem_filter.mp he).1 e₀ he₀)
  have hcomm := (sum_vertexDegree_eq_sum_card_inter (H.filter (fun e => v ∈ e)) e₀).symm
  have hle_one : ∑ u ∈ e₀, vertexDegree (H.filter (fun e => v ∈ e)) u ≤ ∑ _u ∈ e₀, 1 := by
    refine Finset.sum_le_sum (fun u hu => ?_)
    unfold vertexDegree
    refine Finset.card_le_one.mpr (fun e₁ he₁ e₂ he₂ => ?_)
    by_contra hne
    simp only [Finset.mem_filter] at he₁ he₂
    have hsub : ({v, u} : Finset V) ⊆ e₁ ∩ e₂ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨he₁.1.2, he₂.1.2⟩
      · exact Finset.mem_inter.mpr ⟨he₁.2, he₂.2⟩
    have hvu_ne : v ≠ u := fun h => hv (h ▸ hu)
    have hcard2 : 2 ≤ (e₁ ∩ e₂).card := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hvu_ne] at hle
      exact hle
    have hle1 := hlin e₁ he₁.1.1 e₂ he₂.1.1 hne
    omega
  simp only [Finset.sum_const, smul_eq_mul, mul_one, hunif e₀ he₀] at hle_one
  omega

/-- **Universal Linear Hypergraph Maximum Degree Bound**: In any non-2-colourable linear
intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), every vertex `v` has degree at most `r`. -/
theorem vertexDegree_le_r_of_isLinearHypergraph_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) (v : V) :
    vertexDegree H v ≤ r := by
  obtain ⟨e₀, he₀, hv⟩ := exists_edge_not_mem_of_not_isTwoColorable hr hunif hnot2 v
  exact vertexDegree_le_r_of_not_mem_edge_of_isLinearHypergraph hunif hinter hlin he₀ hv

/-- **Universal Projective-Plane Edge Upper Bound (`|E(H)| ≤ r² - r + 1`)**: Every non-2-colourable
linear intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) has at most `r * r - r + 1` edges
(attained with equality by `triangleK3` at `r = 2` and `fanoPlane` at `r = 3`). -/
theorem card_le_r_sq_sub_r_add_one_of_isLinearHypergraph_of_not_isTwoColorable [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    H.card ≤ r * r - r + 1 := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  have hsum_eq := sum_vertexDegree_eq_card_sub_one_add_r_of_isLinearHypergraph hunif hinter hlin he₀
  have hsum_le : ∑ v ∈ e₀, vertexDegree H v ≤ ∑ _v ∈ e₀, r :=
    Finset.sum_le_sum (fun v _ =>
      vertexDegree_le_r_of_isLinearHypergraph_of_not_isTwoColorable hr hunif hinter hlin hnot2 v)
  simp only [Finset.sum_const, smul_eq_mul, hunif e₀ he₀] at hsum_le
  have hpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  omega

/-! ## Section 4: Vertex-Avoiding Subhypergraphs, Criticality & Erdős–Lovász Branching -/

/-- The subhypergraph of `H` consisting of all hyperedges disjoint from a vertex set `S`. -/
def avoidingEdges [DecidableEq V] (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  H.filter (fun e => Disjoint e S)

/-- The subhypergraph of `H` consisting of all hyperedges not containing a vertex `v`. -/
def vertexAvoidingEdges [DecidableEq V] (H : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  H.filter (fun e => v ∉ e)

/-- For any `r`-uniform hypergraph `H` and vertex subset `S`, `avoidingEdges H S` is `r`-uniform. -/
theorem isUniform_avoidingEdges [DecidableEq V] {r : ℕ} {H : Finset (Finset V)}
    (hunif : IsUniform r H) (S : Finset V) :
    IsUniform r (avoidingEdges H S) :=
  fun e he => hunif e (Finset.mem_filter.mp he).1

/-- For any intersecting hypergraph `H` and vertex subset `S`, `avoidingEdges H S` is intersecting. -/
theorem isIntersecting_avoidingEdges [DecidableEq V] {H : Finset (Finset V)}
    (hinter : IsIntersecting H) (S : Finset V) :
    IsIntersecting (avoidingEdges H S) :=
  isIntersecting_mono (Finset.filter_subset _ H) hinter

/-- In any non-2-colourable `r`-uniform hypergraph `H`, for every vertex set `S` with `S.card < r`,
the avoiding subhypergraph `avoidingEdges H S` is nonempty. -/
theorem nonempty_avoidingEdges_of_card_lt_r_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H)
    {S : Finset V} (hS : S.card < r) :
    (avoidingEdges H S).Nonempty := by
  obtain ⟨e, he, hdisj⟩ := exists_disjoint_edge_of_card_lt_r_of_not_isTwoColorable hunif hnot2 hS
  exact ⟨e, Finset.mem_filter.mpr ⟨he, hdisj⟩⟩

/-- Exact Partition Identity for Vertex-Avoiding Edges: for any hypergraph `H` and vertex `v`,
`(vertexAvoidingEdges H v).card + vertexDegree H v = H.card`. -/
theorem card_vertexAvoidingEdges_add_vertexDegree [DecidableEq V] (H : Finset (Finset V)) (v : V) :
    (vertexAvoidingEdges H v).card + vertexDegree H v = H.card := by
  unfold vertexAvoidingEdges vertexDegree
  rw [add_comm]
  exact Finset.card_filter_add_card_filter_not (fun e => v ∈ e)

/-- **Erdős–Lovász Multi-Vertex Branching Union Bound**: For any hypergraph `H` and finite vertex
set `S`, `H.card ≤ (avoidingEdges H S).card + ∑ v ∈ S, vertexDegree H v`. -/
theorem card_le_card_avoidingEdges_add_sum_vertexDegree [DecidableEq V]
    (H : Finset (Finset V)) (S : Finset V) :
    H.card ≤ (avoidingEdges H S).card + ∑ v ∈ S, vertexDegree H v := by
  rw [sum_vertexDegree_eq_sum_card_inter]
  have hpart := Finset.card_filter_add_card_filter_not (s := H) (fun e => Disjoint e S)
  have hhit : (H.filter (fun e => ¬ Disjoint e S)).card ≤ ∑ e ∈ H, (e ∩ S).card := by
    have hsub : ∑ e ∈ H.filter (fun e => ¬ Disjoint e S), (e ∩ S).card ≤ ∑ e ∈ H, (e ∩ S).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ H)
    have hones : (H.filter (fun e => ¬ Disjoint e S)).card ≤
        ∑ e ∈ H.filter (fun e => ¬ Disjoint e S), (e ∩ S).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum (fun e he => ?_)
      have hnd : ¬ Disjoint e S := (Finset.mem_filter.mp he).2
      rw [Finset.not_disjoint_iff_nonempty_inter] at hnd
      exact Finset.Nonempty.card_pos hnd
    omega
  unfold avoidingEdges
  omega

/-- In any intersecting hypergraph `H`, for every edge `e₀ ∈ H` and every vertex `v`, the punctured
edge `e₀.erase v` is a transversal of `vertexAvoidingEdges H v`. -/
theorem isTransversal_vertexAvoidingEdges_erase_of_isIntersecting [DecidableEq V]
    {H : Finset (Finset V)} (hinter : IsIntersecting H) {e₀ : Finset V} (he₀ : e₀ ∈ H) (v : V) :
    IsTransversal (vertexAvoidingEdges H v) (e₀.erase v) := by
  intro e he
  obtain ⟨he_H, hv_not_e⟩ := Finset.mem_filter.mp he
  obtain ⟨u, hu⟩ := hinter e he_H e₀ he₀
  obtain ⟨hu_e, hu_e₀⟩ := Finset.mem_inter.mp hu
  have hu_ne : u ≠ v := fun h => hv_not_e (h ▸ hu_e)
  exact ⟨u, Finset.mem_inter.mpr ⟨hu_e, Finset.mem_erase.mpr ⟨hu_ne, hu_e₀⟩⟩⟩

/-- **Universal Vertex-Deletion 2-Colourability (Vertex-Criticality Theorem)**: In any intersecting
`r`-uniform hypergraph `H` (`r ≥ 2`), for every edge `e₀ ∈ H` and every vertex `v ∈ e₀`, the
vertex-avoiding subhypergraph `vertexAvoidingEdges H v` is 2-colourable. -/
theorem isTwoColorable_vertexAvoidingEdges_of_mem_edge [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    IsTwoColorable (vertexAvoidingEdges H v) := by
  refine ⟨subsetColoring (e₀.erase v),
    isProperColoring_subsetColoring_of_isTransversal
      (isTransversal_vertexAvoidingEdges_erase_of_isIntersecting hinter he₀ v) ?_⟩
  intro e he hsub
  have he_H : e ∈ H := (Finset.mem_filter.mp he).1
  have hle := Finset.card_le_card hsub
  rw [hunif e he_H, Finset.card_erase_of_mem hv, hunif e₀ he₀] at hle
  omega

/-- **Erdős–Lovász First-Step Branching Remainder Bound**: In any intersecting `r`-uniform
hypergraph `H`, for every edge `e₀ ∈ H`, vertex `v ∈ e₀`, and degree bound `D`, if
`∀ u ∈ e₀.erase v, vertexDegree H u ≤ D`, then `(vertexAvoidingEdges H v).card ≤ (r - 1) * D`. -/
theorem card_vertexAvoidingEdges_le_r_sub_one_mul_of_mem_edge [DecidableEq V] {r D : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (hdeg : ∀ u ∈ e₀.erase v, vertexDegree H u ≤ D) :
    (vertexAvoidingEdges H v).card ≤ (r - 1) * D := by
  have htrans := isTransversal_vertexAvoidingEdges_erase_of_isIntersecting hinter he₀ v
  have h1 := card_le_sum_vertexDegree_of_isTransversal htrans
  have h2 : ∑ u ∈ e₀.erase v, vertexDegree (vertexAvoidingEdges H v) u ≤
      ∑ u ∈ e₀.erase v, vertexDegree H u := by
    refine Finset.sum_le_sum (fun u _ => ?_)
    unfold vertexDegree vertexAvoidingEdges
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ H))
  have h3 : ∑ u ∈ e₀.erase v, vertexDegree H u ≤ ∑ _u ∈ e₀.erase v, D :=
    Finset.sum_le_sum (fun u hu => hdeg u hu)
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hv, hunif e₀ he₀] at h3
  omega

/-- **Universal Edge Upper Bound from Punctured-Edge Degree Bound**: In any intersecting `r`-uniform
hypergraph `H`, if `e₀ ∈ H` and every vertex `u ∈ e₀` has `vertexDegree H u ≤ D`, then
`H.card ≤ r * D`. -/
theorem card_le_r_mul_of_vertexDegree_le_on_edge [DecidableEq V] {r D : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) (hdeg : ∀ u ∈ e₀, vertexDegree H u ≤ D) :
    H.card ≤ r * D := by
  have h1 := card_le_sum_vertexDegree_of_mem_of_isIntersecting hinter he₀
  have h2 : ∑ u ∈ e₀, vertexDegree H u ≤ ∑ _u ∈ e₀, D :=
    Finset.sum_le_sum (fun u hu => hdeg u hu)
  simp only [Finset.sum_const, smul_eq_mul, hunif e₀ he₀] at h2
  omega

/-! ## Section 5: Alon Equitable-Partition Exponential Lower Bounds -/

/-- Universal Central Binomial Exponential Lower Bound: `2 ^ k ≤ Nat.choose (2 * k) k` for all `k`. -/
theorem two_pow_le_choose_two_mul (k : ℕ) : 2 ^ k ≤ Nat.choose (2 * k) k := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hstep1 : Nat.choose (2 * (m + 1)) (m + 1) =
        Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) := by
      have h : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h, Nat.choose_succ_succ]
    have hstep2 : Nat.choose (2 * m + 1) (m + 1) =
        Nat.choose (2 * m) m + Nat.choose (2 * m) (m + 1) := by
      rw [Nat.choose_succ_succ]
    have hstep3 : Nat.choose (2 * m) m ≤ Nat.choose (2 * m + 1) m := by
      cases m with
      | zero => simp
      | succ j =>
        have h : 2 * (j + 1) + 1 = (2 * (j + 1)) + 1 := rfl
        have h2 := Nat.choose_succ_succ (2 * (j + 1)) j
        dsimp only [Nat.succ_eq_add_one] at h2
        omega
    rw [pow_succ]
    omega

/-- **Universal Exponential Lower Bound for Alon Edge Count**: For every `r ≥ 1`,
`2 ^ (r - 1) ≤ alonEdgeCount r`. -/
theorem two_pow_sub_one_le_alonEdgeCount (r : ℕ) (hr : 1 ≤ r) :
    2 ^ (r - 1) ≤ alonEdgeCount r := by
  unfold alonEdgeCount
  have hcentral := two_pow_le_choose_two_mul (r - 1)
  have hmul : 2 * (r - 1) = 2 * r - 2 := by omega
  rw [hmul] at hcentral
  omega

/-- **Universal Exponential Lower Bound for Alon Vertex Count**: For every `r ≥ 2`,
`(2 * r - 2) + 2 ^ (r - 2) ≤ alonVertexCount r`. -/
theorem two_pow_sub_two_add_two_mul_r_sub_two_le_alonVertexCount (r : ℕ) (hr : 2 ≤ r) :
    (2 * r - 2) + 2 ^ (r - 2) ≤ alonVertexCount r := by
  unfold alonVertexCount
  have hcentral := two_pow_le_choose_two_mul (r - 1)
  have hmul : 2 * (r - 1) = 2 * r - 2 := by omega
  rw [hmul] at hcentral
  have hpow : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    have h1 : r - 1 = (r - 2) + 1 := by omega
    rw [h1, pow_succ, mul_comm]
  omega


/-- In any intersecting `r`-uniform hypergraph `H` with `2 ≤ H.card`, for every edge `e₀ ∈ H`,
there exists a distinct edge `e₁ ∈ H` (`e₁ ≠ e₀`) such that
`H.card ≤ (H.card - 1) * (e₁ ∩ e₀).card + r`. -/
theorem exists_other_edge_mul_inter_add_r_ge_card [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hcard : 2 ≤ H.card) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∃ e₁ ∈ H, e₁ ≠ e₀ ∧ H.card ≤ (H.card - 1) * (e₁ ∩ e₀).card + r := by
  obtain ⟨e₁, he₁, hne, hle⟩ := exists_other_edge_mul_inter_ge_sum_vertexDegree_sub_r hunif hcard he₀
  have hsum := card_le_sum_vertexDegree_of_mem_of_isIntersecting hinter he₀
  exact ⟨e₁, he₁, hne, by omega⟩

/-- For every active vertex `v ∈ activeVertices H` of an intersecting `r`-uniform hypergraph `H`
(`r ≥ 2`), the subhypergraph `vertexAvoidingEdges H v` of edges not containing `v` is 2-colourable. -/
theorem isTwoColorable_vertexAvoidingEdges_of_mem_activeVertices [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {v : V} (hv : v ∈ activeVertices H) :
    IsTwoColorable (vertexAvoidingEdges H v) := by
  unfold activeVertices at hv
  simp only [Finset.mem_biUnion, id_eq] at hv
  obtain ⟨e₀, he₀, hv_e₀⟩ := hv
  exact isTwoColorable_vertexAvoidingEdges_of_mem_edge hr hunif hinter he₀ hv_e₀


end Erdos836


/-! ## Ported from `AlonMinimumDegreeTransversalAndLovaszThreeUniformClassification836.lean` -/

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 20000


/-!
# Erdős Problem #836: Alon's Minimum-Degree Transversal Bound & Lovász's `r = 3` Classification

This module combines Alon's minimum-degree transversal bound with Lovász's `r = 3` intersecting
hypergraph classification.

## Main Universal Results (`∀`)

1. **Universal Transversal 2-Colourability & Alon Transversal Degree Bounds (Section 1)**:
   - `not_subset_of_isUniform_of_card_lt`: no hyperedge of an `r`-uniform hypergraph is contained in
     a vertex set of size `< r`.
   - `isProperColoring_subsetColoring_of_isTransversal_of_card_lt` and
     `isTwoColorable_of_isTransversal_of_card_lt_r`: every `r`-uniform hypergraph admitting a
     transversal of size `< r` (`τ(H) ≤ r - 1`) is 2-colourable.
   - `card_le_card_mul_of_isTransversal_of_vertexDegree_le` and
     `exists_vertex_in_transversal_mul_degree_ge_card`: for any transversal `T` of `H`,
     `H.card ≤ T.card * max_{v ∈ T} vertexDegree H v`.
   - `mul_card_activeVertices_le_card_mul_r_of_le_vertexDegree`: Alon's minimum-degree handshake
     bound `(activeVertices H).card * δ ≤ H.card * r` whenever all active vertices have degree `≥ δ`.

2. **Degree-1 Erase Transversals, Minimum Active Degree `δ(H) ≥ 2`, and Private Witnesses (Section 2)**:
   - `isTransversal_erase_of_mem_edge_of_forall_mem_imp_eq` and
     `isTwoColorable_of_mem_edge_of_forall_mem_imp_eq`: if `v ∈ e₀ ∈ H` belongs to no other edge of
     an intersecting `r`-uniform hypergraph (`r ≥ 2`), then `e₀.erase v` is a transversal of size
     `r - 1` and `H` is 2-colourable.
   - `exists_other_edge_mem_of_mem_edge_of_not_isTwoColorable`,
     `two_le_vertexDegree_of_mem_edge_of_not_isTwoColorable`, and
     `two_le_vertexDegree_of_mem_activeVertices_of_not_isTwoColorable`: every active vertex in a
     non-2-colourable intersecting `r`-uniform hypergraph (`r ≥ 2`) has degree `≥ 2` (tight at
     degree `2` on the partition vertices of Alon's construction).
   - `two_mul_card_activeVertices_le_card_mul_r_of_not_isTwoColorable` and
     `two_mul_r_le_sum_vertexDegree_of_mem_edge_of_not_isTwoColorable`: universal active-vertex
     upper bound `2 * |V(H)| ≤ |E(H)| * r` and edge degree-sum lower bound `2r ≤ ∑_{v ∈ e₀} d(v)`.
   - `exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable`: for every `e₀ ∈ H` and
     every `v ∈ e₀`, there exists a private-intersection witness `e₁ ∈ H` with `e₁ ∩ e₀ = {v}`.

3. **Unit-Intersection & Multi-Intersection Decomposition and Sharpened Co-Degree Bounds (Section 3)**:
   - `r_le_card_unitInterEdges_of_not_isTwoColorable` and
     `r_add_one_le_card_of_isIntersecting_of_not_isTwoColorable`: every edge `e₀ ∈ H` meets at
     least `r` edges of `H` in a single vertex (`r ≤ |unitInterEdges H e₀|`), yielding the
     universal minimum-edge bound `r + 1 ≤ H.card` for all `r ≥ 2`.
   - `card_unitInterEdges_add_card_multiInterEdges` and
     `card_multiInterEdges_add_r_le_card_sub_one_of_not_isTwoColorable`: exact partition of
     `H.erase e₀` into unit-intersection and multi-intersection (`≥ 2`) edges.
   - `sum_vertexDegree_le_card_sub_one_sub_r_mul_add_two_mul_r_of_not_hasPairwiseIntersectionAtLeast`:
     sharpened Erdős–Lovász–Alon co-degree bound `∑_{v ∈ e₀} d(v) ≤ (|H| - 1 - r) * k + 2r`.

4. **Alon–Lovász Degree-2 Vertex Replacement & Codimension-One Avoidance `δ(H) ≥ 3` (Section 4)**:
   - `isTransversal_insert_erase_of_forall_mem_imp_eq_or_eq` and
     `insert_erase_mem_of_forall_mem_imp_eq_or_eq_of_not_isTwoColorable`: if `v ∈ e₀` belongs only
     to `e₀` and `e₁` in a non-2-colourable intersecting `r`-uniform hypergraph (`r ≥ 2`), then for
     every `w ∈ e₁`, `insert w (e₀.erase v)` is a transversal of `H` and belongs to `H`.
   - `hasPairwiseIntersectionAtLeast_sub_one_of_vertexDegree_le_two_of_not_isTwoColorable`: any
     active vertex of degree `≤ 2` (`r ≥ 3`) forces `HasPairwiseIntersectionAtLeast H (r - 1)`.
   - `three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable`
     and `three_le_vertexDegree_of_isLinearHypergraph_of_not_isTwoColorable`: every non-2-colourable
     intersecting `r`-uniform hypergraph (`r ≥ 3`) avoiding pairwise intersection `r - 1` has
     minimum active-vertex degree `≥ 3`, edge degree-sum `≥ 3r`, and `3 * |V(H)| ≤ |E(H)| * r`.

5. **Lovász's `r = 3` Classification (`τ ≤ 3`), Fano Parameter Uniqueness & Controls (Section 5)**:
   - `lovasz_three_uniform_transversal_le_three` and
     `isTwoColorable_of_r_eq_three_of_isTransversal_of_card_le_two`: Lovász's `r = 3` transversal
     classification (`τ(H) ∈ {1, 2}` implies `IsTwoColorable H`; `χ(H) = 3` implies `τ(H) = 3`).
   - `vertexDegree_eq_three_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable`,
     `card_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable`, and
     `card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable`:
     every linear 3-chromatic intersecting 3-uniform hypergraph is 3-regular on active vertices and
     has `|E(H)| = 7` and `|V(H)| = 7` (the exact parameters of the Fano plane `PG(2,2)`).
   - `tauThreeTwoColorableWitness6_*` and `alonHypergraph3_exists_vertex_degree_eq_two`: kernel-checked
     negative/positive controls certifying that `τ(H) = 3` does not imply `χ(H) = 3` on `Fin 6`
     (6 edges) and that `alonHypergraph3` achieves the minimum possible active degree `2`.
-/

namespace Erdos836

variable {V : Type*}

/-! ## Section 1: Universal Transversal 2-Colourability & Alon Transversal Degree Bounds -/

/-- No hyperedge of an `r`-uniform hypergraph `H` can be a subset of a set `T` of size `< r`. -/
theorem not_subset_of_isUniform_of_card_lt {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) {T : Finset V} (hcard : T.card < r)
    {e : Finset V} (he : e ∈ H) : ¬ e ⊆ T := by
  intro hsub
  have hle := Finset.card_le_card hsub
  have heq := hunif e he
  omega

/-- If `T` is a transversal of an `r`-uniform hypergraph `H` with `T.card < r`, then
`subsetColoring T` is a proper 2-colouring of `H`. -/
theorem isProperColoring_subsetColoring_of_isTransversal_of_card_lt [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) {T : Finset V}
    (hT : IsTransversal H T) (hcard : T.card < r) :
    IsProperColoring H (subsetColoring T) :=
  isProperColoring_subsetColoring_of_isTransversal hT
    (fun _ he => not_subset_of_isUniform_of_card_lt hunif hcard he)

/-- Any `r`-uniform hypergraph `H` admitting a transversal `T` of size `< r` is 2-colourable. -/
theorem isTwoColorable_of_isTransversal_of_card_lt_r [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) {T : Finset V}
    (hT : IsTransversal H T) (hcard : T.card < r) :
    IsTwoColorable H :=
  ⟨subsetColoring T, isProperColoring_subsetColoring_of_isTransversal_of_card_lt hunif hT hcard⟩

/-- Alon's Transversal Degree Upper Bound: if `T` is a transversal of `H` and every vertex in `T`
has degree at most `D`, then `H.card ≤ T.card * D`. -/
theorem card_le_card_mul_of_isTransversal_of_vertexDegree_le [DecidableEq V]
    {H : Finset (Finset V)} {T : Finset V} (hT : IsTransversal H T) {D : ℕ}
    (hdeg : ∀ v ∈ T, vertexDegree H v ≤ D) :
    H.card ≤ T.card * D := by
  have h1 := card_le_sum_vertexDegree_of_isTransversal hT
  have h2 : ∑ v ∈ T, vertexDegree H v ≤ ∑ _v ∈ T, D :=
    Finset.sum_le_sum hdeg
  rw [Finset.sum_const, smul_eq_mul] at h2
  exact le_trans h1 h2

/-- Pigeonhole Principle on Transversals: for every nonempty transversal `T` of `H`, there exists
a vertex `v ∈ T` such that `H.card ≤ T.card * vertexDegree H v`. -/
theorem exists_vertex_in_transversal_mul_degree_ge_card [DecidableEq V]
    {H : Finset (Finset V)} {T : Finset V} (hne : T.Nonempty) (hT : IsTransversal H T) :
    ∃ v ∈ T, H.card ≤ T.card * vertexDegree H v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image T (vertexDegree H) hne
  exact ⟨v, hv, card_le_card_mul_of_isTransversal_of_vertexDegree_le hT hmax⟩

/-- Alon's Minimum-Degree Handshake Bound: if every active vertex of an `r`-uniform hypergraph `H`
has degree at least `δ`, then `(activeVertices H).card * δ ≤ H.card * r`. -/
theorem mul_card_activeVertices_le_card_mul_r_of_le_vertexDegree [DecidableEq V] {r δ : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hdeg : ∀ v ∈ activeVertices H, δ ≤ vertexDegree H v) :
    (activeVertices H).card * δ ≤ H.card * r := by
  have hsum : ∑ _v ∈ activeVertices H, δ ≤ ∑ v ∈ activeVertices H, vertexDegree H v :=
    Finset.sum_le_sum hdeg
  rw [Finset.sum_const, smul_eq_mul, sum_vertexDegree_activeVertices_eq_card_mul_r hunif] at hsum
  exact hsum

/-! ## Section 2: Degree-1 Erase Transversals, Minimum Active Degree `δ(H) ≥ 2`, and Private Witnesses -/

/-- If `e₀ ∈ H` is the unique hyperedge containing `v ∈ e₀` in an intersecting `r`-uniform
hypergraph `H` (`r ≥ 2`), then `e₀.erase v` is a transversal of `H`. -/
theorem isTransversal_erase_of_mem_edge_of_forall_mem_imp_eq [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (huniq : ∀ e ∈ H, v ∈ e → e = e₀) :
    IsTransversal H (e₀.erase v) := by
  intro e he
  by_cases hve : v ∈ e
  · have heq := huniq e he hve
    rw [heq]
    have hsub : e₀.erase v ⊆ e₀ := Finset.erase_subset v e₀
    rw [Finset.inter_eq_right.mpr hsub]
    have hcard : (e₀.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem hv, hunif e₀ he₀]
    exact Finset.card_pos.mp (by omega)
  · have havoid : e ∈ vertexAvoidingEdges H v := by
      unfold vertexAvoidingEdges
      rw [Finset.mem_filter]
      exact ⟨he, hve⟩
    exact isTransversal_vertexAvoidingEdges_erase_of_isIntersecting hinter he₀ v e havoid

/-- Any intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) with a vertex `v ∈ e₀ ∈ H` contained in
no other edge of `H` is 2-colourable. -/
theorem isTwoColorable_of_mem_edge_of_forall_mem_imp_eq [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (huniq : ∀ e ∈ H, v ∈ e → e = e₀) :
    IsTwoColorable H := by
  have hT := isTransversal_erase_of_mem_edge_of_forall_mem_imp_eq hr hunif hinter he₀ hv huniq
  have hcard : (e₀.erase v).card < r := by
    rw [Finset.card_erase_of_mem hv, hunif e₀ he₀]
    omega
  exact isTwoColorable_of_isTransversal_of_card_lt_r hunif hT hcard

/-- In a non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), for every `e₀ ∈ H`
and every `v ∈ e₀`, there exists a distinct edge `e₁ ∈ H` (`e₁ ≠ e₀`) containing `v`. -/
theorem exists_other_edge_mem_of_mem_edge_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    ∃ e₁ ∈ H, e₁ ≠ e₀ ∧ v ∈ e₁ := by
  by_contra hno
  exact hnot2 (isTwoColorable_of_mem_edge_of_forall_mem_imp_eq hr hunif hinter he₀ hv
    (fun e he hve => by
      by_contra hne
      exact hno ⟨e, he, hne, hve⟩))

/-- Every vertex `v ∈ e₀ ∈ H` in a non-2-colourable intersecting `r`-uniform hypergraph (`r ≥ 2`)
has degree `2 ≤ vertexDegree H v`. -/
theorem two_le_vertexDegree_of_mem_edge_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    2 ≤ vertexDegree H v := by
  obtain ⟨e₁, he₁, hne, hv₁⟩ :=
    exists_other_edge_mem_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hv
  unfold vertexDegree
  have hsub : ({e₁, e₀} : Finset (Finset V)) ⊆ H.filter (fun e => v ∈ e) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [Finset.mem_filter]
    rcases he with rfl | rfl
    · exact ⟨he₁, hv₁⟩
    · exact ⟨he₀, hv⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hcard
  exact hcard

/-- Alon's Minimum Active-Vertex Degree Bound: every active vertex `v ∈ activeVertices H` of a
non-2-colourable intersecting `r`-uniform hypergraph (`r ≥ 2`) has `2 ≤ vertexDegree H v`. -/
theorem two_le_vertexDegree_of_mem_activeVertices_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {v : V} (hv : v ∈ activeVertices H) :
    2 ≤ vertexDegree H v := by
  unfold activeVertices at hv
  simp only [Finset.mem_biUnion, id_eq] at hv
  obtain ⟨e₀, he₀, hv₀⟩ := hv
  exact two_le_vertexDegree_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hv₀

/-- Universal Active-Vertex Upper Bound from Minimum Degree `≥ 2`: in any non-2-colourable
intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), `2 * (activeVertices H).card ≤ H.card * r`. -/
theorem two_mul_card_activeVertices_le_card_mul_r_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) :
    2 * (activeVertices H).card ≤ H.card * r := by
  have h := mul_card_activeVertices_le_card_mul_r_of_le_vertexDegree hunif
    (fun _ hv => two_le_vertexDegree_of_mem_activeVertices_of_not_isTwoColorable
      hr hunif hinter hnot2 hv)
  linarith

/-- For every edge `e₀ ∈ H` of a non-2-colourable intersecting `r`-uniform hypergraph (`r ≥ 2`),
`2 * r ≤ ∑ v ∈ e₀, vertexDegree H v`. -/
theorem two_mul_r_le_sum_vertexDegree_of_mem_edge_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    2 * r ≤ ∑ v ∈ e₀, vertexDegree H v := by
  have hsum : ∑ _v ∈ e₀, 2 ≤ ∑ v ∈ e₀, vertexDegree H v :=
    Finset.sum_le_sum (fun _ hv =>
      two_le_vertexDegree_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hv)
  rw [Finset.sum_const, smul_eq_mul, hunif e₀ he₀] at hsum
  linarith

/-- Private-Intersection Witness Theorem: in any non-2-colourable intersecting `r`-uniform
hypergraph `H` (`r ≥ 2`), for every edge `e₀ ∈ H` and every vertex `v ∈ e₀`, there exists an edge
`e₁ ∈ H` such that `e₁ ∩ e₀ = {v}`, `v ∈ e₁`, and `e₁ ≠ e₀`. -/
theorem exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    ∃ e₁ ∈ H, e₁ ∩ e₀ = {v} ∧ v ∈ e₁ ∧ e₁ ≠ e₀ := by
  have hcard : (e₀.erase v).card < r := by
    rw [Finset.card_erase_of_mem hv, hunif e₀ he₀]
    omega
  obtain ⟨e₁, he₁, hdisj⟩ :=
    exists_disjoint_edge_of_card_lt_r_of_not_isTwoColorable hunif hnot2 hcard
  have hne_inter := hinter e₁ he₁ e₀ he₀
  have hsub_sing : e₁ ∩ e₀ ⊆ {v} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_singleton]
    by_contra hxv
    have hx_erase : x ∈ e₀.erase v := Finset.mem_erase.mpr ⟨hxv, hx.2⟩
    exact Finset.disjoint_left.mp hdisj hx.1 hx_erase
  have heq_sing : e₁ ∩ e₀ = {v} := by
    obtain ⟨w, hw⟩ := hne_inter
    have hw_v := Finset.mem_singleton.mp (hsub_sing hw)
    subst hw_v
    exact Finset.Subset.antisymm hsub_sing (Finset.singleton_subset_iff.mpr hw)
  have hv₁ : v ∈ e₁ := by
    have hv_inter : v ∈ e₁ ∩ e₀ := by rw [heq_sing]; exact Finset.mem_singleton_self v
    exact (Finset.mem_inter.mp hv_inter).1
  have hne : e₁ ≠ e₀ := by
    intro h_eq
    subst h_eq
    have hc : (e₁ ∩ e₁).card = 1 := by rw [heq_sing, Finset.card_singleton]
    rw [Finset.inter_self, hunif e₁ he₁] at hc
    omega
  exact ⟨e₁, he₁, heq_sing, hv₁, hne⟩

/-! ## Section 3: Unit-Intersection & Multi-Intersection Decomposition and Sharpened Co-Degree Bounds -/

/-- The hyperedges in `H.erase e₀` that intersect `e₀` in exactly one vertex. -/
def unitInterEdges [DecidableEq V] (H : Finset (Finset V)) (e₀ : Finset V) : Finset (Finset V) :=
  (H.erase e₀).filter (fun e => (e ∩ e₀).card = 1)

/-- The hyperedges in `H.erase e₀` that intersect `e₀` in a number of vertices different from `1`
(which for intersecting hypergraphs means `2 ≤ (e ∩ e₀).card`). -/
def multiInterEdges [DecidableEq V] (H : Finset (Finset V)) (e₀ : Finset V) : Finset (Finset V) :=
  (H.erase e₀).filter (fun e => ¬ (e ∩ e₀).card = 1)

/-- Every unit-intersection hyperedge of `e₀` belongs to `H.erase e₀`. -/
theorem unitInterEdges_subset_erase [DecidableEq V] (H : Finset (Finset V)) (e₀ : Finset V) :
    unitInterEdges H e₀ ⊆ H.erase e₀ :=
  Finset.filter_subset _ _

/-- Exact partition of `H.erase e₀` into `unitInterEdges H e₀` and `multiInterEdges H e₀`. -/
theorem card_unitInterEdges_add_card_multiInterEdges [DecidableEq V]
    {H : Finset (Finset V)} {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    (unitInterEdges H e₀).card + (multiInterEdges H e₀).card = H.card - 1 := by
  unfold unitInterEdges multiInterEdges
  have hpart := Finset.card_filter_add_card_filter_not (s := H.erase e₀)
    (p := fun e => (e ∩ e₀).card = 1)
  have herase := Finset.card_erase_of_mem he₀
  omega

/-- In any non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), every edge `e₀ ∈ H`
has at least `r` unit-intersection edges: `r ≤ (unitInterEdges H e₀).card`. -/
theorem r_le_card_unitInterEdges_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    r ≤ (unitInterEdges H e₀).card := by
  have hsub : e₀ ⊆ (unitInterEdges H e₀).biUnion (fun e => e ∩ e₀) := by
    intro v hv
    obtain ⟨e₁, he₁, heq_sing, _, hne⟩ :=
      exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hv
    rw [Finset.mem_biUnion]
    refine ⟨e₁, ?_, ?_⟩
    · unfold unitInterEdges
      rw [Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨hne, he₁⟩, ?_⟩
      rw [heq_sing, Finset.card_singleton]
    · rw [heq_sing, Finset.mem_singleton]
  have hle1 := Finset.card_le_card hsub
  rw [hunif e₀ he₀] at hle1
  have hle2 : ((unitInterEdges H e₀).biUnion (fun e => e ∩ e₀)).card ≤
      ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card := Finset.card_biUnion_le
  have hsum_eq : ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card = (unitInterEdges H e₀).card := by
    have hcongr : ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card = ∑ _e ∈ unitInterEdges H e₀, 1 := by
      refine Finset.sum_congr rfl (fun e he => ?_)
      unfold unitInterEdges at he
      exact (Finset.mem_filter.mp he).2
    rw [hcongr, Finset.sum_const, smul_eq_mul, mul_one]
  omega

/-- Universal Minimum-Edge Lower Bound `r + 1 ≤ H.card` for every non-2-colourable intersecting
`r`-uniform hypergraph (`r ≥ 2`). -/
theorem r_add_one_le_card_of_isIntersecting_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) :
    r + 1 ≤ H.card := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  have h1 := r_le_card_unitInterEdges_of_not_isTwoColorable hr hunif hinter hnot2 he₀
  have h2 := card_unitInterEdges_add_card_multiInterEdges he₀
  have h3 : 1 ≤ H.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  omega

/-- For every edge `e₀ ∈ H` of a non-2-colourable intersecting `r`-uniform hypergraph (`r ≥ 2`),
at most `H.card - 1 - r` edges of `H.erase e₀` meet `e₀` in `2` or more vertices. -/
theorem card_multiInterEdges_add_r_le_card_sub_one_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    (multiInterEdges H e₀).card + r ≤ H.card - 1 := by
  have h1 := r_le_card_unitInterEdges_of_not_isTwoColorable hr hunif hinter hnot2 he₀
  have h2 := card_unitInterEdges_add_card_multiInterEdges he₀
  omega

/-- Sharpened Erdős–Lovász–Alon Co-Degree Upper Bound: if `H` is a non-2-colourable intersecting
`r`-uniform hypergraph (`r ≥ 2`) with no two distinct edges meeting in `k + 1` or more vertices
(`k ≥ 1`), then for every `e₀ ∈ H`, `∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1 - r) * k + 2 * r`. -/
theorem sum_vertexDegree_le_card_sub_one_sub_r_mul_add_two_mul_r_of_not_hasPairwiseIntersectionAtLeast
    [DecidableEq V] {r k : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (k + 1))
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1 - r) * k + 2 * r := by
  have hcodeg := sum_card_inter_erase_eq_sum_vertexDegree_sub_r hunif he₀
  have hsplit := (Finset.sum_filter_add_sum_filter_not (s := H.erase e₀)
    (p := fun e => (e ∩ e₀).card = 1) (f := fun e => (e ∩ e₀).card)).symm
  change ∑ e ∈ H.erase e₀, (e ∩ e₀).card =
    (∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card) +
      (∑ e ∈ multiInterEdges H e₀, (e ∩ e₀).card) at hsplit
  have hunit_sum : ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card = (unitInterEdges H e₀).card := by
    have hcongr : ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card = ∑ _e ∈ unitInterEdges H e₀, 1 := by
      refine Finset.sum_congr rfl (fun e he => ?_)
      unfold unitInterEdges at he
      exact (Finset.mem_filter.mp he).2
    rw [hcongr, Finset.sum_const, smul_eq_mul, mul_one]
  have hmulti_sum : ∑ e ∈ multiInterEdges H e₀, (e ∩ e₀).card ≤ (multiInterEdges H e₀).card * k := by
    have hle : ∑ e ∈ multiInterEdges H e₀, (e ∩ e₀).card ≤ ∑ _e ∈ multiInterEdges H e₀, k := by
      refine Finset.sum_le_sum (fun e he => ?_)
      unfold multiInterEdges at he
      have herase := (Finset.mem_filter.mp he).1
      obtain ⟨hne, heH⟩ := Finset.mem_erase.mp herase
      by_contra hgt
      exact hno ⟨e, heH, e₀, he₀, hne, by omega⟩
    rw [Finset.sum_const, smul_eq_mul] at hle
    exact hle
  have hpart := card_unitInterEdges_add_card_multiInterEdges he₀
  have hr_unit := r_le_card_unitInterEdges_of_not_isTwoColorable hr hunif hinter hnot2 he₀
  have hdecomp : H.card - 1 - r = (multiInterEdges H e₀).card + ((unitInterEdges H e₀).card - r) := by
    omega
  have hunit_diff : (unitInterEdges H e₀).card - r ≤ ((unitInterEdges H e₀).card - r) * k :=
    Nat.le_mul_of_pos_right _ hk
  have hrhs : (H.card - 1 - r) * k =
      (multiInterEdges H e₀).card * k + ((unitInterEdges H e₀).card - r) * k := by
    rw [hdecomp, Nat.add_mul]
  omega

/-- In any `r`-uniform hypergraph `H`, no two distinct edges can meet in `r` or more vertices. -/
theorem not_hasPairwiseIntersectionAtLeast_r_of_isUniform [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) :
    ¬ HasPairwiseIntersectionAtLeast H r := by
  rintro ⟨e₁, he₁, e₂, he₂, hne, hcard⟩
  have hsub : e₁ ∩ e₂ ⊆ e₁ := Finset.inter_subset_left
  have h1 : e₁.card ≤ (e₁ ∩ e₂).card := by rw [hunif e₁ he₁]; exact hcard
  have heq : e₁ ∩ e₂ = e₁ := Finset.eq_of_subset_of_card_le hsub h1
  have hsub2 : e₁ ⊆ e₂ := by
    rw [← heq]
    exact Finset.inter_subset_right
  have heq2 : e₁ = e₂ := Finset.eq_of_subset_of_card_le hsub2 (by rw [hunif e₁ he₁, hunif e₂ he₂])
  exact hne heq2

/-- Unconditional Sharpened Co-Degree Upper Bound for any non-2-colourable intersecting `r`-uniform
hypergraph (`r ≥ 2`): `∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1 - r) * (r - 1) + 2 * r`. -/
theorem sum_vertexDegree_le_card_sub_one_sub_r_mul_r_sub_one_add_two_mul_r_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ v ∈ e₀, vertexDegree H v ≤ (H.card - 1 - r) * (r - 1) + 2 * r := by
  have hno : ¬ HasPairwiseIntersectionAtLeast H ((r - 1) + 1) := by
    have heq : (r - 1) + 1 = r := by omega
    rw [heq]
    exact not_hasPairwiseIntersectionAtLeast_r_of_isUniform hunif
  exact sum_vertexDegree_le_card_sub_one_sub_r_mul_add_two_mul_r_of_not_hasPairwiseIntersectionAtLeast
    hr (by omega) hunif hinter hnot2 hno he₀

/-! ## Section 4: Alon–Lovász Degree-2 Vertex Replacement & Codimension-One Avoidance (`δ(H) ≥ 3`) -/

/-- If `v ∈ e₀` belongs only to `e₀` and `e₁` in an intersecting `r`-uniform hypergraph `H` (`r ≥ 2`),
then for every `w ∈ e₁`, `insert w (e₀.erase v)` is a transversal of `H`. -/
theorem isTransversal_insert_erase_of_forall_mem_imp_eq_or_eq [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ e₁ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁) {w : V} (hw : w ∈ e₁) :
    IsTransversal H (insert w (e₀.erase v)) := by
  intro e he
  by_cases hve : v ∈ e
  · rcases honly e he hve with heq | heq
    · rw [heq]
      have hcard : (e₀.erase v).card = r - 1 := by
        rw [Finset.card_erase_of_mem hv, hunif e₀ he₀]
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (e₀.erase v).card)
      refine ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hu, ?_⟩⟩
      exact Finset.mem_insert_of_mem hu
    · rw [heq]
      exact ⟨w, Finset.mem_inter.mpr ⟨hw, Finset.mem_insert_self w _⟩⟩
  · have havoid : e ∈ vertexAvoidingEdges H v := by
      unfold vertexAvoidingEdges
      rw [Finset.mem_filter]
      exact ⟨he, hve⟩
    obtain ⟨u, hu⟩ :=
      isTransversal_vertexAvoidingEdges_erase_of_isIntersecting hinter he₀ v e havoid
    rw [Finset.mem_inter] at hu
    exact ⟨u, Finset.mem_inter.mpr ⟨hu.1, Finset.mem_insert_of_mem hu.2⟩⟩

/-- Alon–Lovász Degree-2 Vertex Replacement Theorem: if `v ∈ e₀` belongs only to `e₀` and `e₁` in a
non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), then for every `w ∈ e₁`,
`insert w (e₀.erase v) ∈ H`. -/
theorem insert_erase_mem_of_forall_mem_imp_eq_or_eq_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ e₁ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁) {w : V} (hw : w ∈ e₁) :
    insert w (e₀.erase v) ∈ H := by
  have hT := isTransversal_insert_erase_of_forall_mem_imp_eq_or_eq hr hunif hinter he₀ hv honly hw
  obtain ⟨f, hf, hsub⟩ := exists_edge_subset_of_isTransversal_of_not_isTwoColorable hnot2 hT
  have hcard_le : (insert w (e₀.erase v)).card ≤ f.card := by
    have h1 : (insert w (e₀.erase v)).card ≤ (e₀.erase v).card + 1 := Finset.card_insert_le _ _
    rw [Finset.card_erase_of_mem hv, hunif e₀ he₀] at h1
    rw [hunif f hf]
    omega
  have heq : f = insert w (e₀.erase v) := Finset.eq_of_subset_of_card_le hsub hcard_le
  rwa [← heq]

/-- If `e₀, e₁ ∈ H` are distinct edges containing `v` and `vertexDegree H v ≤ 2`, then every edge
of `H` containing `v` is either `e₀` or `e₁`. -/
theorem forall_mem_imp_eq_or_eq_of_vertexDegree_le_two [DecidableEq V]
    {H : Finset (Finset V)} {e₀ e₁ : Finset V} (he₀ : e₀ ∈ H) (he₁ : e₁ ∈ H) (hne : e₁ ≠ e₀)
    {v : V} (hv₀ : v ∈ e₀) (hv₁ : v ∈ e₁) (hdeg : vertexDegree H v ≤ 2) :
    ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ := by
  have hsub : ({e₁, e₀} : Finset (Finset V)) ⊆ H.filter (fun e => v ∈ e) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [Finset.mem_filter]
    rcases he with rfl | rfl
    · exact ⟨he₁, hv₁⟩
    · exact ⟨he₀, hv₀⟩
  have hcard_pair : ({e₁, e₀} : Finset (Finset V)).card = 2 := Finset.card_pair hne
  have hle : (H.filter (fun e => v ∈ e)).card ≤ ({e₁, e₀} : Finset (Finset V)).card := by
    rw [hcard_pair]
    exact hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  intro e he hve
  have hmem : e ∈ ({e₁, e₀} : Finset (Finset V)) := by
    rw [heq, Finset.mem_filter]
    exact ⟨he, hve⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- If a non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 3`) contains a vertex
`v ∈ e₀ ∈ H` of degree `vertexDegree H v ≤ 2`, then `H` contains two distinct edges meeting in at
least `r - 1` vertices (`HasPairwiseIntersectionAtLeast H (r - 1)`). -/
theorem hasPairwiseIntersectionAtLeast_sub_one_of_vertexDegree_le_two_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (hdeg : vertexDegree H v ≤ 2) :
    HasPairwiseIntersectionAtLeast H (r - 1) := by
  obtain ⟨e₁, he₁, heq_sing, hv₁, hne⟩ :=
    exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable (by omega) hunif hinter hnot2 he₀ hv
  have honly := forall_mem_imp_eq_or_eq_of_vertexDegree_le_two he₀ he₁ hne hv hv₁ hdeg
  have hcard_erase : (e₁.erase v).card = r - 1 := by
    rw [Finset.card_erase_of_mem hv₁, hunif e₁ he₁]
  obtain ⟨w, hw_erase⟩ := Finset.card_pos.mp (by omega : 0 < (e₁.erase v).card)
  obtain ⟨hwv, hw₁⟩ := Finset.mem_erase.mp hw_erase
  have hw_not_e₀ : w ∉ e₀ := by
    intro hw₀
    have hw_inter : w ∈ e₁ ∩ e₀ := Finset.mem_inter.mpr ⟨hw₁, hw₀⟩
    rw [heq_sing, Finset.mem_singleton] at hw_inter
    exact hwv hw_inter
  have hf_mem : insert w (e₀.erase v) ∈ H :=
    insert_erase_mem_of_forall_mem_imp_eq_or_eq_of_not_isTwoColorable
      (by omega) hunif hinter hnot2 he₀ hv honly hw₁
  have hf_ne : insert w (e₀.erase v) ≠ e₀ := by
    intro h_eq
    have hw_in : w ∈ insert w (e₀.erase v) := Finset.mem_insert_self w _
    rw [h_eq] at hw_in
    exact hw_not_e₀ hw_in
  have hsub_inter : e₀.erase v ⊆ (insert w (e₀.erase v)) ∩ e₀ := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx, Finset.mem_of_mem_erase hx⟩
  have hcard_inter : r - 1 ≤ ((insert w (e₀.erase v)) ∩ e₀).card := by
    have hle := Finset.card_le_card hsub_inter
    rw [Finset.card_erase_of_mem hv, hunif e₀ he₀] at hle
    exact hle
  exact ⟨insert w (e₀.erase v), hf_mem, e₀, he₀, hf_ne, hcard_inter⟩

/-- Codimension-One Avoiding Minimum-Degree Theorem (on edges): for `r ≥ 3`, if `H` is a
non-2-colourable intersecting `r`-uniform hypergraph avoiding pairwise intersection `r - 1`, then
every vertex `v ∈ e₀ ∈ H` has `3 ≤ vertexDegree H v`. -/
theorem three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    3 ≤ vertexDegree H v := by
  by_contra hlt
  exact hno (hasPairwiseIntersectionAtLeast_sub_one_of_vertexDegree_le_two_of_not_isTwoColorable
    hr hunif hinter hnot2 he₀ hv (by omega))

/-- Codimension-One Avoiding Minimum Active-Vertex Degree Theorem: for `r ≥ 3`, if `H` is a
non-2-colourable intersecting `r`-uniform hypergraph avoiding pairwise intersection `r - 1`, then
every active vertex `v ∈ activeVertices H` has `3 ≤ vertexDegree H v`. -/
theorem three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {v : V} (hv : v ∈ activeVertices H) :
    3 ≤ vertexDegree H v := by
  unfold activeVertices at hv
  simp only [Finset.mem_biUnion, id_eq] at hv
  obtain ⟨e₀, he₀, hv₀⟩ := hv
  exact three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
    hr hunif hinter hnot2 hno he₀ hv₀

/-- Active-Vertex Upper Bound under Codimension-One Avoidance: for `r ≥ 3`, if `H` is a
non-2-colourable intersecting `r`-uniform hypergraph with `¬ HasPairwiseIntersectionAtLeast H (r - 1)`,
then `3 * (activeVertices H).card ≤ H.card * r`. -/
theorem three_mul_card_activeVertices_le_card_mul_r_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    3 * (activeVertices H).card ≤ H.card * r := by
  have h := mul_card_activeVertices_le_card_mul_r_of_le_vertexDegree hunif
    (fun _ hv =>
      three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
        hr hunif hinter hnot2 hno hv)
  linarith

/-- Any linear hypergraph avoids pairwise intersection `k` for every `k ≥ 2`. -/
theorem not_hasPairwiseIntersectionAtLeast_of_isLinearHypergraph [DecidableEq V] {k : ℕ}
    (hk : 2 ≤ k) {H : Finset (Finset V)} (hlin : IsLinearHypergraph H) :
    ¬ HasPairwiseIntersectionAtLeast H k := by
  rintro ⟨e₁, he₁, e₂, he₂, hne, hcard⟩
  have hle := hlin e₁ he₁ e₂ he₂ hne
  omega

/-- Every active vertex of a non-2-colourable linear intersecting `r`-uniform hypergraph (`r ≥ 3`)
has degree at least `3`. -/
theorem three_le_vertexDegree_of_isLinearHypergraph_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H)
    {v : V} (hv : v ∈ activeVertices H) :
    3 ≤ vertexDegree H v :=
  three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
    hr hunif hinter hnot2 (not_hasPairwiseIntersectionAtLeast_of_isLinearHypergraph (by omega) hlin) hv

/-- In any non-2-colourable linear intersecting `r`-uniform hypergraph (`r ≥ 3`),
`2 * r + 1 ≤ H.card`. -/
theorem two_mul_r_add_one_le_card_of_isLinearHypergraph_of_not_isTwoColorable [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    2 * r + 1 ≤ H.card := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  have hno := not_hasPairwiseIntersectionAtLeast_of_isLinearHypergraph (k := r - 1) (by omega) hlin
  have hsum_ge : ∑ _v ∈ e₀, 3 ≤ ∑ v ∈ e₀, vertexDegree H v :=
    Finset.sum_le_sum (fun _ hv =>
      three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
        hr hunif hinter hnot2 hno he₀ hv)
  rw [Finset.sum_const, smul_eq_mul, hunif e₀ he₀,
    sum_vertexDegree_eq_card_sub_one_add_r_of_isLinearHypergraph hunif hinter hlin he₀] at hsum_ge
  have hpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  omega

/-- If `v ∈ e₀ ∈ H` has `vertexDegree H v ≤ 2` in a non-2-colourable intersecting `r`-uniform
hypergraph `H` (`r ≥ 3`), then `2 ≤ (multiInterEdges H e₀).card`. -/
theorem two_le_card_multiInterEdges_of_vertexDegree_le_two_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (hdeg : vertexDegree H v ≤ 2) :
    2 ≤ (multiInterEdges H e₀).card := by
  obtain ⟨e₁, he₁, heq_sing, hv₁, hne⟩ :=
    exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable
      (by omega) hunif hinter hnot2 he₀ hv
  have honly := forall_mem_imp_eq_or_eq_of_vertexDegree_le_two he₀ he₁ hne hv hv₁ hdeg
  have hcard_erase : 1 < (e₁.erase v).card := by
    rw [Finset.card_erase_of_mem hv₁, hunif e₁ he₁]
    omega
  obtain ⟨w₁, w₂, hw₁_er, hw₂_er, hw_ne⟩ := Finset.one_lt_card_iff.mp hcard_erase
  obtain ⟨hw₁_v, hw₁⟩ := Finset.mem_erase.mp hw₁_er
  obtain ⟨hw₂_v, hw₂⟩ := Finset.mem_erase.mp hw₂_er
  have hw₁_not : w₁ ∉ e₀ := by
    intro h0
    have hmem : w₁ ∈ e₁ ∩ e₀ := Finset.mem_inter.mpr ⟨hw₁, h0⟩
    rw [heq_sing, Finset.mem_singleton] at hmem
    exact hw₁_v hmem
  have hw₂_not : w₂ ∉ e₀ := by
    intro h0
    have hmem : w₂ ∈ e₁ ∩ e₀ := Finset.mem_inter.mpr ⟨hw₂, h0⟩
    rw [heq_sing, Finset.mem_singleton] at hmem
    exact hw₂_v hmem
  have hmem_multi : ∀ w ∈ e₁, w ∉ e₀ → insert w (e₀.erase v) ∈ multiInterEdges H e₀ := by
    intro w hw hw_not
    unfold multiInterEdges
    rw [Finset.mem_filter, Finset.mem_erase]
    have hf_H : insert w (e₀.erase v) ∈ H :=
      insert_erase_mem_of_forall_mem_imp_eq_or_eq_of_not_isTwoColorable
        (by omega) hunif hinter hnot2 he₀ hv honly hw
    have hf_ne : insert w (e₀.erase v) ≠ e₀ := by
      intro h_eq
      have h_in : w ∈ insert w (e₀.erase v) := Finset.mem_insert_self w _
      rw [h_eq] at h_in
      exact hw_not h_in
    have hsub_inter : e₀.erase v ⊆ (insert w (e₀.erase v)) ∩ e₀ := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx, Finset.mem_of_mem_erase hx⟩
    have hge2 : 2 ≤ ((insert w (e₀.erase v)) ∩ e₀).card := by
      have hle := Finset.card_le_card hsub_inter
      rw [Finset.card_erase_of_mem hv, hunif e₀ he₀] at hle
      omega
    exact ⟨⟨hf_ne, hf_H⟩, by omega⟩
  have hf_ne : insert w₁ (e₀.erase v) ≠ insert w₂ (e₀.erase v) := by
    intro h_eq
    have h_in : w₁ ∈ insert w₂ (e₀.erase v) := by
      rw [← h_eq]
      exact Finset.mem_insert_self w₁ _
    rcases Finset.mem_insert.mp h_in with h12 | h_er
    · exact hw_ne h12
    · exact hw₁_not (Finset.mem_of_mem_erase h_er)
  have hsub_pair :
      ({insert w₁ (e₀.erase v), insert w₂ (e₀.erase v)} : Finset (Finset V)) ⊆
        multiInterEdges H e₀ := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hmem_multi w₁ hw₁ hw₁_not
    · exact hmem_multi w₂ hw₂ hw₂_not
  have hcard_le := Finset.card_le_card hsub_pair
  rw [Finset.card_pair hf_ne] at hcard_le
  exact hcard_le

/-- If every vertex `v ∈ e₀ ∈ H` has degree at least `3` in a non-2-colourable intersecting
`r`-uniform hypergraph `H` (`r ≥ 3`), then `r + 3 ≤ H.card`. -/
theorem r_add_three_le_card_of_three_le_vertexDegree_on_edge [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) {e₀ : Finset V} (he₀ : e₀ ∈ H)
    (hdeg3 : ∀ v ∈ e₀, 3 ≤ vertexDegree H v) :
    r + 3 ≤ H.card := by
  have hsum_ge : 3 * r ≤ ∑ v ∈ e₀, vertexDegree H v := by
    have h := Finset.sum_le_sum hdeg3
    rw [Finset.sum_const, smul_eq_mul, hunif e₀ he₀] at h
    linarith
  have hsum_le :=
    sum_vertexDegree_le_card_sub_one_sub_r_mul_r_sub_one_add_two_mul_r_of_not_isTwoColorable
      (by omega) hunif hinter hnot2 he₀
  by_contra hlt
  have hdiff_le : H.card - 1 - r ≤ 1 := by omega
  have hmul_le : (H.card - 1 - r) * (r - 1) ≤ 1 * (r - 1) :=
    Nat.mul_le_mul_right (r - 1) hdiff_le
  omega

/-- Universal Minimum-Edge Lower Bound `r + 3 ≤ H.card` for every non-2-colourable intersecting
`r`-uniform hypergraph `H` with `r ≥ 3` (combining the Alon–Lovász degree-2 replacement bound with
the sharpened co-degree bound for degree `≥ 3`). -/
theorem r_add_three_le_card_of_isIntersecting_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) :
    r + 3 ≤ H.card := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  by_cases hex : ∃ v ∈ e₀, vertexDegree H v ≤ 2
  · obtain ⟨v, hv, hdeg2⟩ := hex
    have hmulti :=
      two_le_card_multiInterEdges_of_vertexDegree_le_two_of_not_isTwoColorable
        hr hunif hinter hnot2 he₀ hv hdeg2
    have hunit := r_le_card_unitInterEdges_of_not_isTwoColorable (by omega) hunif hinter hnot2 he₀
    have hpart := card_unitInterEdges_add_card_multiInterEdges he₀
    have hpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
    omega
  · refine r_add_three_le_card_of_three_le_vertexDegree_on_edge hr hunif hinter hnot2 he₀ ?_
    intro v hv
    by_contra hlt
    exact hex ⟨v, hv, by omega⟩

/-! ## Section 5: Lovász's `r = 3` Classification (`τ ≤ 3`), Fano Uniqueness & Concrete Controls -/

/-- Lovász's `r = 3` Intersecting Transversal Bound: every nonempty intersecting 3-uniform
hypergraph `H` admits a transversal `T` of cardinality `1 ≤ T.card ∧ T.card ≤ 3`. -/
theorem lovasz_three_uniform_transversal_le_three [DecidableEq V]
    {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hne : H.Nonempty) :
    ∃ T : Finset V, IsTransversal H T ∧ 1 ≤ T.card ∧ T.card ≤ 3 := by
  obtain ⟨e₀, he₀⟩ := hne
  refine ⟨e₀, isTransversal_of_mem_of_isIntersecting hinter he₀, ?_⟩
  rw [hunif e₀ he₀]
  omega

/-- Lovász's `r = 3` 2-Colourability Criterion: every 3-uniform hypergraph `H` admitting a
transversal `T` of cardinality `T.card ≤ 2` (`τ(H) ∈ {1, 2}`) is 2-colourable. -/
theorem isTwoColorable_of_r_eq_three_of_isTransversal_of_card_le_two [DecidableEq V]
    {H : Finset (Finset V)} (hunif : IsUniform 3 H) {T : Finset V}
    (hT : IsTransversal H T) (hcard : T.card ≤ 2) :
    IsTwoColorable H :=
  isTwoColorable_of_isTransversal_of_card_lt_r hunif hT (by omega)

/-- Lovász–Alon `r = 3` Minimum-Edge Bound: every non-2-colourable intersecting 3-uniform
hypergraph `H` has at least `6` edges (`6 ≤ H.card`). -/
theorem six_le_card_of_r_eq_three_of_isIntersecting_of_not_isTwoColorable [DecidableEq V]
    {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) :
    6 ≤ H.card :=
  r_add_three_le_card_of_isIntersecting_of_not_isTwoColorable (by decide) hunif hinter hnot2

/-- Exact 3-Regularity of Linear 3-Chromatic Intersecting 3-Uniform Hypergraphs: every active
vertex of a non-2-colourable linear intersecting 3-uniform hypergraph has degree `3`. -/
theorem vertexDegree_eq_three_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H)
    {v : V} (hv : v ∈ activeVertices H) :
    vertexDegree H v = 3 := by
  have hge := three_le_vertexDegree_of_isLinearHypergraph_of_not_isTwoColorable
    (by decide) hunif hinter hlin hnot2 hv
  have hle := vertexDegree_le_r_of_isLinearHypergraph_of_not_isTwoColorable
    (by decide) hunif hinter hlin hnot2 v
  omega

/-- Fano Edge-Count Uniqueness Theorem (`|E(H)| = 7`): every non-2-colourable linear intersecting
3-uniform hypergraph `H` has `H.card = 7`. -/
theorem card_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    H.card = 7 := by
  have hge := two_mul_r_add_one_le_card_of_isLinearHypergraph_of_not_isTwoColorable
    (by decide) hunif hinter hlin hnot2
  have hle := card_le_r_sq_sub_r_add_one_of_isLinearHypergraph_of_not_isTwoColorable
    (by decide) hunif hinter hlin hnot2
  omega

/-- Fano Vertex-Count Uniqueness Theorem (`|V(H)| = 7`): every non-2-colourable linear intersecting
3-uniform hypergraph `H` has `(activeVertices H).card = 7`. -/
theorem card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    (activeVertices H).card = 7 := by
  have hhand := sum_vertexDegree_activeVertices_eq_card_mul_r hunif
  have hcard := card_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
    hunif hinter hlin hnot2
  have hcongr : ∑ v ∈ activeVertices H, vertexDegree H v = ∑ _v ∈ activeVertices H, 3 := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    exact vertexDegree_eq_three_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
      hunif hinter hlin hnot2 hv
  rw [hcongr, Finset.sum_const, smul_eq_mul, hcard] at hhand
  omega

/-- Pilot Task 2 Negative Control: the 6-edge 3-uniform intersecting hypergraph on `Fin 6`
having minimum transversal number `τ(H) = 3` that is nevertheless 2-colourable (`χ(H) = 2`),
certifying that `τ(H) = r` is necessary but not sufficient for `χ(H) = 3` at `r = 3`. -/
def tauThreeTwoColorableWitness6 : Finset (Finset (Fin 6)) :=
  { {0, 1, 2}, {2, 3, 4}, {0, 1, 3}, {0, 4, 5}, {1, 4, 5}, {2, 3, 5} }

theorem tauThreeTwoColorableWitness6_card : tauThreeTwoColorableWitness6.card = 6 := by decide

theorem tauThreeTwoColorableWitness6_isUniform :
    IsUniform 3 tauThreeTwoColorableWitness6 := by decide

theorem tauThreeTwoColorableWitness6_isIntersecting :
    IsIntersecting tauThreeTwoColorableWitness6 := by decide

theorem tauThreeTwoColorableWitness6_hasProperBipartition :
    HasProperBipartition tauThreeTwoColorableWitness6 := by decide

theorem tauThreeTwoColorableWitness6_isTwoColorable :
    IsTwoColorable tauThreeTwoColorableWitness6 :=
  (isTwoColorable_iff_hasProperBipartition tauThreeTwoColorableWitness6).mpr
    tauThreeTwoColorableWitness6_hasProperBipartition

instance instDecidableIsTransversal [DecidableEq V] (H : Finset (Finset V)) (T : Finset V) :
    Decidable (IsTransversal H T) := by
  unfold IsTransversal
  infer_instance

/-- Every transversal of `tauThreeTwoColorableWitness6` has cardinality at least `3` (`τ = 3`),
certifying that `τ(H) = 3` does not imply `¬ IsTwoColorable H` at `r = 3`. -/
theorem tauThreeTwoColorableWitness6_no_transversal_card_le_two :
    ∀ T : Finset (Fin 6), IsTransversal tauThreeTwoColorableWitness6 T → 3 ≤ T.card := by
  decide

/-- Positive Control: Alon's 3-uniform construction `alonHypergraph3` contains active vertices of
degree `2`, certifying that the universal lower bound `2 ≤ vertexDegree H v` is sharp. -/
theorem alonHypergraph3_exists_vertex_degree_eq_two :
    ∃ v ∈ activeVertices alonHypergraph3, vertexDegree alonHypergraph3 v = 2 := by
  decide

end Erdos836
