import Geometry956
import DifferenceBody956

/-!
# Extremal function `h(n)` and Formal Conjectures bridge for Erdős #956

Defines the `sSup` extremal function `h(n)` and `unitPairs C X` from
`FormalConjectures/ErdosProblems/956.lean` and proves `BddAbove` via `n.choose 2`
so that any verified `Configuration n` bounds `h(n)` from below via `le_csSup`.
-/

namespace Erdos956.Specification

open Erdos956.Geometry

/-- A verified configuration of `N` pairwise-disjoint translates of one compact
convex planar body `C` with a certified list of unordered unit-distance pairs. -/
structure Configuration (N : ℕ) where
  C : Set Plane
  compact : IsCompact C
  convex : Convex ℝ C
  nonempty : C.Nonempty
  interior_nonempty : (interior C).Nonempty
  X : Finset Plane
  cardinality : X.card = N
  disjoint : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    Disjoint ((· + x) '' C) ((· + y) '' C)
  edges : Finset (Finset Plane)
  edges_good : ∀ e ∈ edges, ∃ x y : Plane,
    x ≠ y ∧ e = {x, y} ∧ x ∈ X ∧ y ∈ X ∧
      Erdos956.translateSetDistance C x y = 1

end Erdos956.Specification

namespace Erdos956.Extremal

open scoped Classical
open Erdos956.Geometry

/-- Minimum Euclidean distance between the sets `C + x` and `C + y`
(matching `FormalConjectures.ErdosProblems.956.translateDistance`). -/
noncomputable def translateDistance (C : Set Plane) (x y : Plane) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

/-- A family of pairwise disjoint translates of one nonempty compact convex set
(matching `FormalConjectures.ErdosProblems.956.IsConfiguration`). -/
def IsConfiguration (C : Set Plane) (X : Finset Plane) : Prop :=
  C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
    ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint ((· + x) '' C) ((· + y) '' C)

/-- The unordered pairs of distinct centers whose translates have set-distance one
(matching `FormalConjectures.ErdosProblems.956.unitPairs`). -/
noncomputable def unitPairs (C : Set Plane) (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 2).filter fun e =>
    ∃ x y : Plane, x ≠ y ∧ e = {x, y} ∧ translateDistance C x y = 1

/-- The maximum number of unordered unit-distance pairs among `n` disjoint convex translates
(matching `FormalConjectures.ErdosProblems.956.h`). -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
    X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m}

theorem unitPairs_card_le_choose_two (C : Set Plane) (X : Finset Plane) :
    (unitPairs C X).card ≤ X.card.choose 2 := by
  unfold unitPairs
  calc
    ((X.powersetCard 2).filter _).card ≤ (X.powersetCard 2).card :=
      Finset.card_filter_le _ _
    _ = X.card.choose 2 := Finset.card_powersetCard 2 X

theorem attainable_bddAbove (n : ℕ) :
    BddAbove {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
      X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m} := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨C, X, hcard, _, rfl⟩
  rw [← hcard]
  exact unitPairs_card_le_choose_two C X

theorem configuration_isConfiguration {n : ℕ} (config : Specification.Configuration n) :
    IsConfiguration config.C config.X :=
  ⟨config.nonempty, config.compact, config.convex, config.disjoint⟩

theorem configuration_edges_subset_unitPairs {n : ℕ} (config : Specification.Configuration n) :
    config.edges ⊆ unitPairs config.C config.X := by
  intro e he
  obtain ⟨x, y, hne, rfl, hx, hy, hdist⟩ := config.edges_good e he
  unfold unitPairs
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨?_, Finset.card_pair hne⟩, ⟨x, y, hne, rfl, hdist⟩⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hx
  · rw [Finset.mem_singleton.mp hz]
    exact hy

theorem configuration_edges_le_h {n : ℕ} (config : Specification.Configuration n) :
    config.edges.card ≤ h n := by
  have hsub : config.edges.card ≤ (unitPairs config.C config.X).card :=
    Finset.card_le_card (configuration_edges_subset_unitPairs config)
  have hmem : (unitPairs config.C config.X).card ∈
      {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
        X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m} :=
    ⟨config.C, config.X, config.cardinality, configuration_isConfiguration config, rfl⟩
  exact hsub.trans (le_csSup (attainable_bddAbove n) hmem)

end Erdos956.Extremal
