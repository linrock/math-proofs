module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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
public import Erdos902Unified435
public import SzekeresParityRefinementAndTightenedBinomialBounds902
public import SecondOrderBinomialDecayAndTransitiveTripleCounting902
public import QuinticBinomialDecayAndKendallBabingtonSmithBounds902

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 200000
set_option exponentiation.threshold 4096

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section
open scoped Classical BigOperators

/-!
# Erdős Problem 902: General `ZMod p` Paley Tournament Construction & Second-Moment / Pairwise-Intersection Domination Reduction

This module (`Blueprint902.lean`) builds on `Erdos902Unified435` and the auxiliary
modules (`SzekeresParityRefinementAndTightenedBinomialBounds902`,
`SecondOrderBinomialDecayAndTransitiveTripleCounting902`, and
`QuinticBinomialDecayAndKendallBabingtonSmithBounds902`) to establish with zero `sorry`:

1. **General Paley / Quadratic-Residue Digraph Construction on `ZMod p` and `Fin p` (`p ≡ 3 [MOD 4]`):**
   - `paleyZModDigraph p : Digraph (ZMod p)` with directed adjacency `u ≠ v ∧ IsSquare (v - u)`.
   - Non-squareness of `-1 : ZMod p` (`not_isSquare_neg_one_zmod`), quadratic-character skew-symmetry
     `IsSquare (v - u) ↔ ¬ IsSquare (u - v)` (`isSquare_sub_iff_not_isSquare_neg_sub`), and
     unconditional tournament trichotomy `IsTournament (paleyZModDigraph p)`
     (`isTournament_paleyZModDigraph`) for every prime `p ≡ 3 [MOD 4]`.
   - Affine automorphism invariance (`paleyZModDigraph_affine_adj`) under translations `x ↦ x + c`
     and scaling `x ↦ r * x + c` by nonzero squares `r ∈ (ZMod p)ˣ`.
   - Reflection bijection `v ↦ 2 * u - v` (`card_paleyZModOutNeigh_eq_card_paleyZModInNeigh`) and
     exact degree partition (`paleyZModOutNeigh_disjoint_and_regular`) proving regular out-degree
     and in-degree `(p - 1) / 2` on `ZMod p`, transported via `finZModEquiv p : Fin p ≃ ZMod p` to
     `paleyFinDigraph p : Digraph (Fin p)` (`isTournament_and_regular_paleyFinDigraph`) with exact
     transitive and cyclic triple counts.

2. **Second-Moment / Lovász Local Lemma / Pairwise-Intersection Domination Reduction (`5 ≤ n ≤ 10`):**
   - Deterministic second-moment pairwise out-neighborhood intersection identity
     (`sum_sq_card_domSet_eq_sum_choose_commonOutNeigh`):
     `∑_{|S|=k} (domSet G S).card ^ 2 = ∑ u, ∑ v, (commonOutNeigh G u v).card.choose k`.
   - Discrete Cauchy–Schwarz / Paley–Zygmund lower bound on `(dominatedSubsets G k).card`
     (`second_moment_dominatedSubsets_bound`), pairwise-intersection paradoxicality criterion
     (`isParadoxicalTournament_of_second_moment_commonOutNeigh`), and doubly-regular / Paley
     tournament specialization (`doubly_regular_sum_sq_card_domSet_and_criterion`).
   - Probabilistic orientation-space first-moment, second-moment, and multiplicity-deficit identities
     for `undominatedSubsetFinset n ω` and `excessBadMultiplicity n N`
     (`sum_card_undominatedSubsetFinset_eq_sum_card_badOrientations`,
     `sum_sq_card_undominatedSubsetFinset_eq_sum_card_inter_badOrientations`,
     `card_biUnion_badOrientations_add_excessBadMultiplicity`,
     `card_inter_badOrientations_le_excessBadMultiplicity`, and
     `hasParadoxicalTournament_of_excessBadMultiplicity_gt`).
   - Complete falsification of `ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)` for all `1 ≤ n ≤ 10`
     (`twenty_nine_seventy_nine_lower_bound_and_not_criterion_ten`, closing the `n = 10` case via
     the `(29, 79)` dyadic rational lower bound at `n_0 = 8`), and the top-down conditional
     reduction (`erdos_902_mid_range_reduction_of_second_moment_or_excess_multiplicity`) reducing
     `f n ≤ n ^ 2 * 2 ^ n` for all `n ≥ 2` (and `f n ≤ n ^ 2 * 2 ^ n + 1` for all `n ≥ 1`) to
     either the deterministic pairwise-intersection second-moment condition or the probabilistic
     excess-multiplicity condition on the six mid-range cases `5 ≤ n ≤ 10`.
-/

namespace Erdos902

/-!
## Section 1: General Paley / Quadratic-Residue Digraph Construction on `ZMod p` and `Fin p`
-/

/-- The general Paley (quadratic-residue) digraph on `ZMod p`: there is a directed edge `u → v`
iff `u ≠ v` and `v - u` is a square in `ZMod p`. -/
def paleyZModDigraph (p : ℕ) : Digraph (ZMod p) where
  Adj u v := u ≠ v ∧ IsSquare (v - u)

/-- The strict out-neighborhood of `u` in `paleyZModDigraph p`. -/
def paleyZModOutNeigh (p : ℕ) [Fintype (ZMod p)] (u : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun v => (paleyZModDigraph p).Adj u v)

/-- The strict in-neighborhood of `u` in `paleyZModDigraph p`. -/
def paleyZModInNeigh (p : ℕ) [Fintype (ZMod p)] (u : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun v => (paleyZModDigraph p).Adj v u)

/-- Canonical equivalence `Fin p ≃ ZMod p` for `p ≠ 0`. -/
def finZModEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun u := (u.val : ZMod p)
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv u := Fin.ext (ZMod.val_natCast_of_lt u.isLt)
  right_inv x := ZMod.natCast_zmod_val x

/-- The general Paley digraph transported to `Fin p` along `finZModEquiv p`. -/
def paleyFinDigraph (p : ℕ) [NeZero p] : Digraph (Fin p) :=
  comapDigraph (paleyZModDigraph p) (finZModEquiv p).toEmbedding

/-- Theorem 1: For every prime `p ≡ 3 [MOD 4]`, `-1` is not a square in `ZMod p`. -/
theorem not_isSquare_neg_one_zmod {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  omega

/-- Theorem 2: Skew-symmetry of quadratic residues modulo a prime `p ≡ 3 [MOD 4]`: for `u ≠ v` in
`ZMod p`, `v - u` is a square iff `u - v` is not a square. -/
theorem isSquare_sub_iff_not_isSquare_neg_sub {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {u v : ZMod p} (huv : u ≠ v) :
    IsSquare (v - u) ↔ ¬ IsSquare (u - v) := by
  have hsub : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  have hneg1 : quadraticChar (ZMod p) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (not_isSquare_neg_one_zmod hp)
  have hmul : quadraticChar (ZMod p) (u - v) = - quadraticChar (ZMod p) (v - u) := by
    have heq : u - v = (-1) * (v - u) := by ring
    rw [heq, map_mul, hneg1, neg_one_mul]
  rw [← quadraticChar_one_iff_isSquare hsub, ← quadraticChar_neg_one_iff_not_isSquare]
  omega

/-- Theorem 3: For every prime `p ≡ 3 [MOD 4]`, `paleyZModDigraph p` is a tournament on `ZMod p`. -/
theorem isTournament_paleyZModDigraph {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    IsTournament (paleyZModDigraph p) := by
  refine ⟨fun v h => h.1 rfl, fun u v huv => ?_⟩
  dsimp [paleyZModDigraph]
  rw [and_iff_right huv, and_iff_right huv.symm]
  exact isSquare_sub_iff_not_isSquare_neg_sub hp huv

/-- Theorem 4: Affine automorphism invariance of `paleyZModDigraph p` under translations `x ↦ x + c`
and scaling `x ↦ r * x + c` by any nonzero quadratic residue `r : ZMod p`. -/
theorem paleyZModDigraph_affine_adj {p : ℕ} [Fact p.Prime] (u v c r : ZMod p)
    (hr : r ≠ 0) (hr_sq : IsSquare r) :
    ((paleyZModDigraph p).Adj (u + c) (v + c) ↔ (paleyZModDigraph p).Adj u v) ∧
      ((paleyZModDigraph p).Adj (r * u + c) (r * v + c) ↔ (paleyZModDigraph p).Adj u v) := by
  refine ⟨?_, ?_⟩
  · dsimp [paleyZModDigraph]
    have h1 : (u + c = v + c) ↔ (u = v) := add_left_inj c
    have h2 : (v + c) - (u + c) = v - u := by ring
    rw [not_congr h1, h2]
  · dsimp [paleyZModDigraph]
    have h1 : (r * u + c = r * v + c) ↔ (u = v) :=
      (add_left_inj c).trans (mul_right_inj' hr)
    have h2 : (r * v + c) - (r * u + c) = r * (v - u) := by ring
    rw [not_congr h1, h2]
    refine and_congr_right (fun _ => ⟨fun hsq => ?_, fun hsq => hr_sq.mul hsq⟩)
    have hinv : IsSquare r⁻¹ := isSquare_inv.mpr hr_sq
    have hprod := hinv.mul hsq
    rwa [inv_mul_cancel_left₀ hr] at hprod

/-- Theorem 5: For every `p : ℕ` and every vertex `u : ZMod p`, the reflection involution
`v ↦ 2 * u - v` bijects `paleyZModOutNeigh p u` onto `paleyZModInNeigh p u`, so out-degree equals
in-degree at every vertex. -/
theorem card_paleyZModOutNeigh_eq_card_paleyZModInNeigh (p : ℕ) [Fintype (ZMod p)] (u : ZMod p) :
    (paleyZModOutNeigh p u).card = (paleyZModInNeigh p u).card := by
  refine Finset.card_bij (fun v _ => 2 * u - v)
    (fun v hv => ?_) (fun v₁ _ v₂ _ heq => ?_) (fun w hw => ?_)
  · rw [paleyZModInNeigh, Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
    rw [paleyZModOutNeigh, Finset.mem_filter] at hv
    rcases hv.2 with ⟨hne, hsq⟩
    have hsub : u - (2 * u - v) = v - u := by ring
    refine ⟨fun h => hne ?_, by rwa [hsub]⟩
    have : v - u = 0 := by rw [← hsub, h, sub_self]
    exact (sub_eq_zero.mp this).symm
  · have : v₁ - v₂ = (2 * u - v₂) - (2 * u - v₁) := by ring
    rw [heq, sub_self] at this
    exact sub_eq_zero.mp this
  · refine ⟨2 * u - w, ?_, by ring⟩
    rw [paleyZModOutNeigh, Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
    rw [paleyZModInNeigh, Finset.mem_filter] at hw
    rcases hw.2 with ⟨hne, hsq⟩
    have hsub : (2 * u - w) - u = u - w := by ring
    refine ⟨fun h => hne ?_, by rwa [hsub]⟩
    have : u - w = 0 := by rw [← hsub, ← h, sub_self]
    exact (sub_eq_zero.mp this).symm

/-- Theorem 6: For every prime `p ≡ 3 [MOD 4]` and every `u : ZMod p`, `paleyZModOutNeigh p u` and
`paleyZModInNeigh p u` disjointly partition `Finset.univ.erase u` and both have exact cardinality
`(p - 1) / 2`. -/
theorem paleyZModOutNeigh_disjoint_and_regular {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (u : ZMod p) :
    Disjoint (paleyZModOutNeigh p u) (paleyZModInNeigh p u) ∧
      paleyZModOutNeigh p u ∪ paleyZModInNeigh p u = Finset.univ.erase u ∧
      2 * (paleyZModOutNeigh p u).card = p - 1 ∧
      (paleyZModOutNeigh p u).card = (p - 1) / 2 ∧
      (paleyZModInNeigh p u).card = (p - 1) / 2 := by
  have hT := isTournament_paleyZModDigraph hp
  have hdisj : Disjoint (paleyZModOutNeigh p u) (paleyZModInNeigh p u) := by
    rw [Finset.disjoint_left]
    intro v hv_out hv_in
    rw [paleyZModOutNeigh, Finset.mem_filter] at hv_out
    rw [paleyZModInNeigh, Finset.mem_filter] at hv_in
    exact (hT.2 u v hv_out.2.1).mp hv_out.2 hv_in.2
  have hunion : paleyZModOutNeigh p u ∪ paleyZModInNeigh p u = Finset.univ.erase u := by
    ext v
    simp only [paleyZModOutNeigh, paleyZModInNeigh, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_erase]
    refine ⟨fun h => ?_, fun ⟨hne, _⟩ => ?_⟩
    · rcases h with h1 | h2
      · exact ⟨h1.1.symm, trivial⟩
      · exact ⟨h2.1, trivial⟩
    · by_cases hadj : (paleyZModDigraph p).Adj u v
      · exact Or.inl hadj
      · exact Or.inr ((hT.2 v u hne).mpr hadj)
  have hsum : (paleyZModOutNeigh p u).card + (paleyZModInNeigh p u).card = p - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, ZMod.card]
  have heq := card_paleyZModOutNeigh_eq_card_paleyZModInNeigh p u
  exact ⟨hdisj, hunion, by omega, by omega, by omega⟩

/-- Theorem 7: For every prime `p ≡ 3 [MOD 4]`, `paleyFinDigraph p` is a regular tournament on
`Fin p` of out-degree and in-degree `(p - 1) / 2`, with exact transitive-triple count
`p * ((p - 1) / 2).choose 2` and cyclic-triple count `p.choose 3 - p * ((p - 1) / 2).choose 2`. -/
theorem isTournament_and_regular_paleyFinDigraph {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    IsTournament (paleyFinDigraph p) ∧
      (∀ u : Fin p,
        (outNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 ∧
          (inNeigh (paleyFinDigraph p) u).card = (p - 1) / 2) ∧
      (transitiveTripleFinset (paleyFinDigraph p)).card = p * ((p - 1) / 2).choose 2 ∧
      (cyclicTripleFinset (paleyFinDigraph p)).card =
        p.choose 3 - p * ((p - 1) / 2).choose 2 := by
  have hT : IsTournament (paleyFinDigraph p) :=
    isTournament_comap (isTournament_paleyZModDigraph hp) (finZModEquiv p).toEmbedding
  have hreg : ∀ u : Fin p,
      (outNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 ∧
        (inNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 := by
    intro u
    have hout : (outNeigh (paleyFinDigraph p) u).map (finZModEquiv p).toEmbedding =
        paleyZModOutNeigh p (finZModEquiv p u) := by
      ext x
      simp only [Finset.mem_map, outNeigh, paleyZModOutNeigh, Finset.mem_filter,
        Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
      refine ⟨fun ⟨v, hv, hvx⟩ => hvx ▸ hv, fun hx => ?_⟩
      refine ⟨(finZModEquiv p).symm x, ?_, (finZModEquiv p).apply_symm_apply x⟩
      dsimp [paleyFinDigraph, comapDigraph]
      rwa [(finZModEquiv p).apply_symm_apply x]
    have hin : (inNeigh (paleyFinDigraph p) u).map (finZModEquiv p).toEmbedding =
        paleyZModInNeigh p (finZModEquiv p u) := by
      ext x
      simp only [Finset.mem_map, inNeigh, paleyZModInNeigh, Finset.mem_filter,
        Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
      refine ⟨fun ⟨v, hv, hvx⟩ => hvx ▸ hv, fun hx => ?_⟩
      refine ⟨(finZModEquiv p).symm x, ?_, (finZModEquiv p).apply_symm_apply x⟩
      dsimp [paleyFinDigraph, comapDigraph]
      rwa [(finZModEquiv p).apply_symm_apply x]
    have hcard_out : (outNeigh (paleyFinDigraph p) u).card =
        (paleyZModOutNeigh p (finZModEquiv p u)).card := by
      rw [← hout, Finset.card_map]
    have hcard_in : (inNeigh (paleyFinDigraph p) u).card =
        (paleyZModInNeigh p (finZModEquiv p u)).card := by
      rw [← hin, Finset.card_map]
    have hzm := paleyZModOutNeigh_disjoint_and_regular hp (finZModEquiv p u)
    exact ⟨hcard_out.trans hzm.2.2.2.1, hcard_in.trans hzm.2.2.2.2⟩
  have htriples := card_transitive_and_cyclic_triples_of_regular hT (fun u => (hreg u).2)
  exact ⟨hT, hreg, htriples.1, htriples.2.1⟩

/-!
## Section 2: Second-Moment / Lovász Local Lemma / Pairwise-Intersection Domination Reduction
-/

/-- Common out-neighborhood `outNeigh G u ∩ outNeigh G v` of two vertices `u, v : Fin N`. -/
def commonOutNeigh {N : ℕ} (G : Digraph (Fin N)) (u v : Fin N) : Finset (Fin N) :=
  outNeigh G u ∩ outNeigh G v

/-- The finset of `k`-element subsets of `Fin N` that have at least one dominator in `G`. -/
def dominatedSubsets {N : ℕ} (G : Digraph (Fin N)) (k : ℕ) : Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin N)).powersetCard k).filter (fun S => (domSet G S).Nonempty)

/-- The finset of `n`-element subsets of `Fin N` that have no dominator in
`tournamentOfOrientation ω`. -/
def undominatedSubsetFinset (n : ℕ) {N : ℕ} (ω : EdgeIdx N → Bool) :
    Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin N)).powersetCard n).filter (fun S => ω ∈ badOrientations S)

/-- Total excess multiplicity `∑_{ω ∈ ⋃ badOrientations S} (|undominatedSubsetFinset n ω| - 1)`
measuring pairwise and higher-order overlap among bad orientations. -/
def excessBadMultiplicity (n N : ℕ) : ℕ :=
  ∑ ω ∈ ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations,
    ((undominatedSubsetFinset n ω).card - 1)


/-- Theorem 9: Both `u` and `v` dominate `S` iff `S ⊆ commonOutNeigh G u v`. -/
theorem mem_domSet_and_mem_domSet_iff_subset_commonOutNeigh {N : ℕ} (G : Digraph (Fin N))
    (u v : Fin N) (S : Finset (Fin N)) :
    (u ∈ domSet G S ∧ v ∈ domSet G S) ↔ S ⊆ commonOutNeigh G u v := by
  simp only [mem_domSet_iff, Dominates, commonOutNeigh, Finset.subset_iff,
    Finset.mem_inter, mem_outNeigh_iff]
  exact ⟨fun ⟨hu, hv⟩ w hw => ⟨hu w hw, hv w hw⟩,
    fun h => ⟨fun w hw => (h hw).1, fun w hw => (h hw).2⟩⟩

/-- Theorem 10: Second-moment pairwise-intersection identity for subset domination:
`∑_{|S|=k} (domSet G S).card ^ 2 = ∑ u, ∑ v, (commonOutNeigh G u v).card.choose k`. -/
theorem sum_sq_card_domSet_eq_sum_choose_commonOutNeigh {N : ℕ} (G : Digraph (Fin N)) (k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card ^ 2) =
      ∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k := by
  have hsq : ∀ S : Finset (Fin N),
      (domSet G S).card ^ 2 =
        ∑ u : Fin N, ∑ v : Fin N, if u ∈ domSet G S ∧ v ∈ domSet G S then 1 else 0 := by
    intro S
    have hcard : (domSet G S).card = ∑ u : Fin N, if u ∈ domSet G S then 1 else 0 := by
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [sq, hcard, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hu : u ∈ domSet G S <;> by_cases hv : v ∈ domSet G S <;> simp [hu, hv]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.card_filter]
  have hfilter :
      ((Finset.univ : Finset (Fin N)).powersetCard k).filter
          (fun S => u ∈ domSet G S ∧ v ∈ domSet G S) =
        (commonOutNeigh G u v).powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      mem_domSet_and_mem_domSet_iff_subset_commonOutNeigh]
    exact and_comm
  rw [hfilter, Finset.card_powersetCard]

/-- Theorem 11: Discrete Cauchy–Schwarz inequality `(∑ x ∈ s, g x) ^ 2 ≤ s.card * ∑ x ∈ s, (g x) ^ 2`
for natural-number-valued functions on any finset. -/
theorem nat_sum_sq_le_card_mul_sum_sq {α : Type*} (s : Finset α) (g : α → ℕ) :
    (∑ x ∈ s, g x) ^ 2 ≤ s.card * ∑ x ∈ s, (g x) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℤ)) (fun x => (g x : ℤ))
  simp only [one_mul, one_pow, Finset.sum_const, Int.nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- Theorem 12: Paley–Zygmund / Chung–Erdős second-moment lower bound on `(dominatedSubsets G k).card`:
`(∑ v, (outNeigh G v).card.choose k) ^ 2 ≤ (dominatedSubsets G k).card * ∑ u, ∑ v, (commonOutNeigh G u v).card.choose k`. -/
theorem second_moment_dominatedSubsets_bound {N : ℕ} (G : Digraph (Fin N)) (k : ℕ) :
    (∑ v : Fin N, (outNeigh G v).card.choose k) ^ 2 ≤
      (dominatedSubsets G k).card *
        ∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k := by
  have hsum1 :
      (∑ S ∈ dominatedSubsets G k, (domSet G S).card) =
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card := by
    dsimp [dominatedSubsets]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hne : (domSet G S).Nonempty
    · rw [if_pos hne]
    · rw [if_neg hne, Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
  have hsum2 :
      (∑ S ∈ dominatedSubsets G k, (domSet G S).card ^ 2) =
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card ^ 2 := by
    dsimp [dominatedSubsets]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hne : (domSet G S).Nonempty
    · rw [if_pos hne]
    · rw [if_neg hne, Finset.not_nonempty_iff_eq_empty.mp hne,
        Finset.card_empty, zero_pow (by decide)]
  calc
    (∑ v : Fin N, (outNeigh G v).card.choose k) ^ 2
        = (∑ S ∈ dominatedSubsets G k, (domSet G S).card) ^ 2 := by
          rw [hsum1, sum_card_domSet_eq_sum_choose_outNeigh]
    _ ≤ (dominatedSubsets G k).card * ∑ S ∈ dominatedSubsets G k, (domSet G S).card ^ 2 :=
          nat_sum_sq_le_card_mul_sum_sq (dominatedSubsets G k) (fun S => (domSet G S).card)
    _ = (dominatedSubsets G k).card *
          ∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k := by
          rw [hsum2, sum_sq_card_domSet_eq_sum_choose_commonOutNeigh]

/-- Theorem 13: Deterministic second-moment pairwise-intersection domination criterion:
if `G` is a tournament on `Fin N` (`k ≤ N`) and
`(N.choose k - 1) * ∑ u, ∑ v, (commonOutNeigh G u v).card.choose k < (∑ v, (outNeigh G v).card.choose k) ^ 2`,
then `G` is `k`-paradoxical (`IsParadoxicalTournament k G`). -/
theorem isParadoxicalTournament_of_second_moment_commonOutNeigh {k N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (hkN : k ≤ N)
    (hsm : (N.choose k - 1) * (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) <
      (∑ v : Fin N, (outNeigh G v).card.choose k) ^ 2) :
    IsParadoxicalTournament k G := by
  have hcs := second_moment_dominatedSubsets_bound G k
  have hlt : (N.choose k - 1) * (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) <
      (dominatedSubsets G k).card * (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) :=
    lt_of_lt_of_le hsm hcs
  have hcard_gt : N.choose k - 1 < (dominatedSubsets G k).card := by
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul_right (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) hle
    omega
  have hsub : dominatedSubsets G k ⊆ (Finset.univ : Finset (Fin N)).powersetCard k :=
    Finset.filter_subset _ _
  have hcard_le : (dominatedSubsets G k).card ≤ N.choose k := by
    calc
      (dominatedSubsets G k).card ≤ ((Finset.univ : Finset (Fin N)).powersetCard k).card :=
        Finset.card_le_card hsub
      _ = N.choose k := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have heq : dominatedSubsets G k = (Finset.univ : Finset (Fin N)).powersetCard k := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    omega
  refine ⟨hG, by simpa using hkN, fun S hScard => ?_⟩
  have hmem : S ∈ (Finset.univ : Finset (Fin N)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩
  rw [← heq, dominatedSubsets, Finset.mem_filter] at hmem
  rcases hmem.2 with ⟨v, hv⟩
  exact ⟨v, mem_domSet_iff.mp hv⟩

/-- Theorem 14: Doubly-regular tournament first- and second-moment evaluation and paradoxicality
criterion: if `(outNeigh G u).card = d` for all `u` and `(commonOutNeigh G u v).card = l` for all
`u ≠ v`, then `∑_{|S|=k} (domSet G S).card = N * d.choose k`,
`∑_{|S|=k} (domSet G S).card ^ 2 = N * d.choose k + N * (N - 1) * l.choose k`, and
`(N.choose k - 1) * (d.choose k + (N - 1) * l.choose k) < N * (d.choose k) ^ 2` implies
`IsParadoxicalTournament k G`. -/
theorem doubly_regular_sum_sq_card_domSet_and_criterion {N d l k : ℕ} {G : Digraph (Fin N)}
    (hd : ∀ u : Fin N, (outNeigh G u).card = d)
    (hl : ∀ u v : Fin N, u ≠ v → (commonOutNeigh G u v).card = l) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card) =
      N * d.choose k ∧
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card ^ 2) =
      N * d.choose k + N * (N - 1) * l.choose k ∧
    (IsTournament G → k ≤ N → 1 ≤ N →
      (N.choose k - 1) * (d.choose k + (N - 1) * l.choose k) < N * (d.choose k) ^ 2 →
      IsParadoxicalTournament k G) := by
  have hsum_out : (∑ u : Fin N, (outNeigh G u).card.choose k) = N * d.choose k := by
    have hcongr : ∀ u ∈ (Finset.univ : Finset (Fin N)),
        (outNeigh G u).card.choose k = d.choose k := fun u _ => by rw [hd u]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have h1 : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card) =
      N * d.choose k := by
    rw [sum_card_domSet_eq_sum_choose_outNeigh, hsum_out]
  have hinner : ∀ u : Fin N,
      (∑ v : Fin N, (commonOutNeigh G u v).card.choose k) =
        d.choose k + (N - 1) * l.choose k := by
    intro u
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
    have huu : (commonOutNeigh G u u).card = d := by
      dsimp [commonOutNeigh]
      rw [Finset.inter_self, hd u]
    have herase : ∀ v ∈ (Finset.univ : Finset (Fin N)).erase u,
        (commonOutNeigh G u v).card.choose k = l.choose k := by
      intro v hv
      rw [hl u v (Finset.ne_of_mem_erase hv).symm]
    rw [huu, Finset.sum_congr rfl herase, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hsum_u : (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) =
      N * (d.choose k + (N - 1) * l.choose k) := by
    rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  refine ⟨h1, ?_, fun hT hkN hN1 hlt => ?_⟩
  · rw [sum_sq_card_domSet_eq_sum_choose_commonOutNeigh, hsum_u]
    ring
  · apply isParadoxicalTournament_of_second_moment_commonOutNeigh hT hkN
    rw [hsum_u, hsum_out]
    have hmul := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < N)
    calc
      (N.choose k - 1) * (N * (d.choose k + (N - 1) * l.choose k))
          = N * ((N.choose k - 1) * (d.choose k + (N - 1) * l.choose k)) := by ring
      _ < N * (N * d.choose k ^ 2) := hmul
      _ = (N * d.choose k) ^ 2 := by ring

/-- Theorem 15: An orientation `ω : EdgeIdx N → Bool` yields an `n`-paradoxical tournament
(`n ≤ N`) iff `undominatedSubsetFinset n ω = ∅`. -/
theorem isParadoxicalTournament_tournamentOfOrientation_iff_undominatedSubsetFinset_eq_empty
    {n N : ℕ} (hnN : n ≤ N) (ω : EdgeIdx N → Bool) :
    IsParadoxicalTournament n (tournamentOfOrientation ω) ↔
      undominatedSubsetFinset n ω = ∅ := by
  refine ⟨fun hG => ?_, fun hemp => ?_⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [undominatedSubsetFinset, Finset.mem_filter, Finset.mem_powersetCard,
      badOrientations, Finset.mem_filter] at hS
    exact hS.2.2 (hG.2.2 S hS.1.2)
  · refine ⟨isTournament_tournamentOfOrientation ω, by simpa using hnN, fun S hScard => ?_⟩
    by_contra hnotDom
    have hmem : S ∈ undominatedSubsetFinset n ω := by
      rw [undominatedSubsetFinset, Finset.mem_filter, Finset.mem_powersetCard,
        badOrientations, Finset.mem_filter]
      exact ⟨⟨Finset.subset_univ S, hScard⟩, Finset.mem_univ ω, hnotDom⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty S hmem

/-- Theorem 16: First-moment double-counting identity on the tournament orientation space:
`∑ ω, (undominatedSubsetFinset n ω).card = ∑_{|S|=n} (badOrientations S).card`. -/
theorem sum_card_undominatedSubsetFinset_eq_sum_card_badOrientations (n N : ℕ) :
    (∑ ω : EdgeIdx N → Bool, (undominatedSubsetFinset n ω).card) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (badOrientations S).card := by
  simp_rw [undominatedSubsetFinset, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Theorem 17: Second-moment pairwise-intersection identity on the tournament orientation space:
`∑ ω, (undominatedSubsetFinset n ω).card ^ 2 = ∑_{|S|=n} ∑_{|T|=n} (badOrientations S ∩ badOrientations T).card`. -/
theorem sum_sq_card_undominatedSubsetFinset_eq_sum_card_inter_badOrientations (n N : ℕ) :
    (∑ ω : EdgeIdx N → Bool, (undominatedSubsetFinset n ω).card ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
        ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
          (badOrientations S ∩ badOrientations T).card := by
  have hsq : ∀ ω : EdgeIdx N → Bool,
      (undominatedSubsetFinset n ω).card ^ 2 =
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
          ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
            if ω ∈ badOrientations S ∩ badOrientations T then 1 else 0 := by
    intro ω
    rw [sq, undominatedSubsetFinset, Finset.card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    by_cases hS : ω ∈ badOrientations S <;> by_cases hT : ω ∈ badOrientations T <;>
      simp [hS, hT, Finset.mem_inter]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Theorem 18: Exact multiplicity-deficit identity decomposing the first-moment sum of
`(badOrientations S).card` into the biUnion cardinality plus `excessBadMultiplicity n N`. -/
theorem card_biUnion_badOrientations_add_excessBadMultiplicity (n N : ℕ) :
    (((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations).card +
      excessBadMultiplicity n N =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (badOrientations S).card := by
  let B := ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations
  have hpos : ∀ ω ∈ B, 1 ≤ (undominatedSubsetFinset n ω).card := by
    intro ω hω
    rw [Finset.mem_biUnion] at hω
    rcases hω with ⟨S, hS, hωS⟩
    exact Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hωS⟩⟩
  have hB_sum :
      B.card + excessBadMultiplicity n N =
        ∑ ω ∈ B, (undominatedSubsetFinset n ω).card := by
    dsimp [excessBadMultiplicity]
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ω hω => ?_)
    have := hpos ω hω
    omega
  rw [hB_sum, ← sum_card_undominatedSubsetFinset_eq_sum_card_badOrientations]
  symm
  rw [← Finset.sum_subset (Finset.subset_univ B)]
  intro ω _ hnotB
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro S hS
  rw [undominatedSubsetFinset, Finset.mem_filter] at hS
  exact hnotB (Finset.mem_biUnion.mpr ⟨S, hS.1, hS.2⟩)

/-- Theorem 19: Bonferroni pairwise-intersection lower bound on `excessBadMultiplicity n N`:
for any two distinct `n`-subsets `S₀ ≠ T₀`, `(badOrientations S₀ ∩ badOrientations T₀).card ≤ excessBadMultiplicity n N`. -/
theorem card_inter_badOrientations_le_excessBadMultiplicity {n N : ℕ}
    {S₀ T₀ : Finset (Fin N)}
    (hS₀ : S₀ ∈ (Finset.univ : Finset (Fin N)).powersetCard n)
    (hT₀ : T₀ ∈ (Finset.univ : Finset (Fin N)).powersetCard n)
    (hne : S₀ ≠ T₀) :
    (badOrientations S₀ ∩ badOrientations T₀).card ≤ excessBadMultiplicity n N ∧
      (((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations).card +
        (badOrientations S₀ ∩ badOrientations T₀).card ≤
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (badOrientations S).card := by
  let B := ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations
  have hsub : badOrientations S₀ ∩ badOrientations T₀ ⊆ B := by
    intro ω hω
    exact Finset.mem_biUnion.mpr ⟨S₀, hS₀, (Finset.mem_inter.mp hω).1⟩
  have hle_one : ∀ ω ∈ badOrientations S₀ ∩ badOrientations T₀,
      1 ≤ (undominatedSubsetFinset n ω).card - 1 := by
    intro ω hω
    rcases Finset.mem_inter.mp hω with ⟨h1, h2⟩
    have hpair : ({S₀, T₀} : Finset (Finset (Fin N))) ⊆ undominatedSubsetFinset n ω := by
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA2
      · exact Finset.mem_filter.mpr ⟨hS₀, h1⟩
      · rw [Finset.mem_singleton.mp hA2]
        exact Finset.mem_filter.mpr ⟨hT₀, h2⟩
    have hcard2 : 2 ≤ (undominatedSubsetFinset n ω).card := by
      calc
        2 = ({S₀, T₀} : Finset (Finset (Fin N))).card := (Finset.card_pair hne).symm
        _ ≤ (undominatedSubsetFinset n ω).card := Finset.card_le_card hpair
    omega
  have hcard_le : (badOrientations S₀ ∩ badOrientations T₀).card ≤ excessBadMultiplicity n N := by
    calc
      (badOrientations S₀ ∩ badOrientations T₀).card
          = ∑ _ω ∈ badOrientations S₀ ∩ badOrientations T₀, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ ω ∈ badOrientations S₀ ∩ badOrientations T₀,
            ((undominatedSubsetFinset n ω).card - 1) := Finset.sum_le_sum hle_one
      _ ≤ ∑ ω ∈ B, ((undominatedSubsetFinset n ω).card - 1) :=
            Finset.sum_le_sum_of_subset hsub
      _ = excessBadMultiplicity n N := rfl
  have hid := card_biUnion_badOrientations_add_excessBadMultiplicity n N
  exact ⟨hcard_le, by omega⟩

/-- Theorem 20: Multiplicity-deficit / Lovász Local Lemma existence bridge beyond the first-moment
union bound: if `n ≤ N` and the first-moment sum of bad orientations is strictly less than
`2 ^ Fintype.card (EdgeIdx N) + excessBadMultiplicity n N`, then `HasParadoxicalTournament n N`
holds. -/
theorem hasParadoxicalTournament_of_excessBadMultiplicity_gt {n N : ℕ} (hnN : n ≤ N)
    (hexcess :
      2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (N.choose n * (2 ^ n - 1) ^ (N - n)) <
        2 ^ Fintype.card (EdgeIdx N) + excessBadMultiplicity n N) :
    (∃ ω : EdgeIdx N → Bool, IsParadoxicalTournament n (tournamentOfOrientation ω)) ∧
      HasParadoxicalTournament n N := by
  let B := ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations
  have hid : B.card + excessBadMultiplicity n N =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (badOrientations S).card :=
    card_biUnion_badOrientations_add_excessBadMultiplicity n N
  rw [sum_card_badOrientations] at hid
  have hmul : N.choose n *
      (2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (2 ^ n - 1) ^ (N - n)) =
    2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (N.choose n * (2 ^ n - 1) ^ (N - n)) := by ring
  rw [hmul] at hid
  have huniv : (Finset.univ : Finset (EdgeIdx N → Bool)).card = 2 ^ Fintype.card (EdgeIdx N) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hB_lt : B.card < (Finset.univ : Finset (EdgeIdx N → Bool)).card := by
    rw [huniv]
    omega
  have hne : B ≠ Finset.univ := fun heq => by
    rw [heq] at hB_lt
    exact lt_irrefl _ hB_lt
  have hnonempty : (Finset.univ \ B).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_univ_of_forall fun x => hsub (Finset.mem_univ x))
  obtain ⟨ω, hω⟩ := hnonempty
  have hnotB : ω ∉ B := (Finset.mem_sdiff.mp hω).2
  have hpar : IsParadoxicalTournament n (tournamentOfOrientation ω) := by
    refine ⟨isTournament_tournamentOfOrientation ω, by simpa using hnN, fun S hScard => ?_⟩
    by_contra hnotDom
    apply hnotB
    rw [Finset.mem_biUnion]
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hnotDom⟩⟩
  exact ⟨⟨ω, hpar⟩, ⟨tournamentOfOrientation ω, hpar⟩⟩

/-- Theorem 21: Dyadic `(29, 79)` lower bound for `n ≥ 8` and complete falsification of the
first-moment union-bound criterion `ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)` for all
`1 ≤ n ≤ 10` (closing the `n = 10` case). -/
theorem twenty_nine_seventy_nine_lower_bound_and_not_criterion_ten :
    (∀ n : ℕ, 8 ≤ n → 29 * (2 ^ n) ^ (2 ^ n) ≤ 79 * (2 ^ n - 1) ^ (2 ^ n)) ∧
      ¬ ErdosProbabilisticCriterion 10 (10 ^ 2 * 2 ^ 10) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ 10 → ¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)) := by
  have hstep : ∀ n : ℕ, 8 ≤ n → 29 * (2 ^ n) ^ (2 ^ n) ≤ 79 * (2 ^ n - 1) ^ (2 ^ n) := by
    intro n hn
    exact (rational_lower_bound_step_and_three_eleven_twenty
      (by decide : 1 ≤ 8) hn
      (by decide : 29 * (2 ^ 8) ^ (2 ^ 8) ≤ 79 * (2 ^ 8 - 1) ^ (2 ^ 8))).1
  have h10 : ¬ ErdosProbabilisticCriterion 10 (10 ^ 2 * 2 ^ 10) :=
    not_erdosProbabilisticCriterion_sq_of_rational_lower_bound 10 29 79
      (by decide) (by decide) (hstep 10 (by decide)) (by decide)
  refine ⟨hstep, h10, fun n hn1 hn10 => ?_⟩
  by_cases hn9 : n ≤ 9
  · exact not_erdosProbabilisticCriterion_sq_mul_two_pow_of_le_nine hn1 hn9
  · have hn_eq : n = 10 := by omega
    subst hn_eq
    exact h10

/-- Theorem 22: Top-down conditional reduction closing the mid-range gap `5 ≤ n ≤ 10` for
`legacyF n ≤ n ^ 2 * 2 ^ n` (and hence `∀ n ≥ 2, legacyF n ≤ n ^ 2 * 2 ^ n` and `∀ n ≥ 1, legacyF n ≤ n ^ 2 * 2 ^ n + 1`)
from either a tournament witness satisfying the deterministic second-moment pairwise-intersection
bound at `M ≤ n ^ 2 * 2 ^ n` or the probabilistic excess-multiplicity bound at `N = n ^ 2 * 2 ^ n`. -/
theorem erdos_902_mid_range_reduction_of_second_moment_or_excess_multiplicity
    (hmid : ∀ n : ℕ, 5 ≤ n → n ≤ 10 →
      (∃ (M : ℕ) (G : Digraph (Fin M)),
        n ≤ M ∧ M ≤ n ^ 2 * 2 ^ n ∧ IsTournament G ∧
        (M.choose n - 1) * (∑ u : Fin M, ∑ v : Fin M, (commonOutNeigh G u v).card.choose n) <
          (∑ v : Fin M, (outNeigh G v).card.choose n) ^ 2) ∨
      2 ^ (Fintype.card (EdgeIdx (n ^ 2 * 2 ^ n)) - n * (n ^ 2 * 2 ^ n - n)) *
          ((n ^ 2 * 2 ^ n).choose n * (2 ^ n - 1) ^ (n ^ 2 * 2 ^ n - n)) <
        2 ^ Fintype.card (EdgeIdx (n ^ 2 * 2 ^ n)) +
          excessBadMultiplicity n (n ^ 2 * 2 ^ n)) :
    (∀ n : ℕ, 1 ≤ n → legacyF n ≤ n ^ 2 * 2 ^ n + 1) ∧
      (∀ n : ℕ, 2 ≤ n → legacyF n ≤ n ^ 2 * 2 ^ n) := by
  apply f_le_sq_mul_two_pow_add_one_of_mid_range
  intro n hn5 hn10
  rcases hmid n hn5 hn10 with ⟨M, G, hnM, hM_le, hT, hsm⟩ | hexcess
  · have hpar : IsParadoxicalTournament n G :=
      isParadoxicalTournament_of_second_moment_commonOutNeigh hT hnM hsm
    exact hasParadoxicalTournament_mono_N hM_le ⟨G, hpar⟩
  · have hnN : n ≤ n ^ 2 * 2 ^ n := by
      have h1 : 1 ≤ n ^ 2 := by nlinarith
      have h2 : n ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
      nlinarith
    exact (hasParadoxicalTournament_of_excessBadMultiplicity_gt hnN hexcess).2

end Erdos902
end
