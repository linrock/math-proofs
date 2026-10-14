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

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Set

/-!
# Erdős Problem #107: Inductive $k$-Cup/$k$-Cap Convex Independence and KKS Wedge-Pigeonhole Pentagon Forcing

This module extends `Erdos107Unified435.lean` on the Erdős–Szekeres convex polygon problem (`erdos_107`)
with 26 universally quantified structural theorems across four sections:

1. **All-Triple Cup/Cap Sets (`IsCupSet`, `IsCapSet`) and Universal Skipped-Chord Convex Independence**:
   We define `IsCupSet P C` (every ordered triple $x < y < z$ in $C$ has `0 < lineSide (P x) (P y) (P z)`)
   and `IsCapSet P C` (every ordered triple $x < y < z$ in $C$ has `lineSide (P x) (P y) (P z) < 0`),
   prove that right end-extension with a single adjacent `slopeLt` turn preserves `IsCupSet`
   (`isCupSet_insert_right`) and left end-extension with a single adjacent `slopeGt` turn preserves
   `IsCapSet` (`isCapSet_insert_left`), prove the universal skipped-vertex chord separation lemmas
   (`isCupSet_skipped_chord_sep`, `isCapSet_skipped_chord_sep`), and establish that every `IsCupSet`
   and every `IsCapSet` of arbitrary finite size in an $x$-monotone sequence is `ConvexIndep`
   (`convexIndep_of_isCupSet`, `convexIndep_of_isCapSet`).

2. **Inductive $k$-Cup/$k$-Cap Polygon Forcing and the General Erdős–Szekeres Theorem for Arbitrary $k \ge 3$**:
   By induction on the chain length $m$, we prove that every `CupChainEnding P S m a b` extracts an
   $(m + 2)$-element `IsCupSet P C` (`cupChainEnding_exists_isCupSet`) and every `CapChainStarting P S k b c`
   extracts a $(k + 2)$-element `IsCapSet P C` (`capChainStarting_exists_isCapSet`). Consequently,
   `HasCup P S (k - 2) ∨ HasCap P S (k - 2)` forces `HasConvexNGon k (P '' (S : Set ℕ))` for every $k \ge 2$
   (`hasConvexNGon_of_hasCup_or_hasCap`), yielding the general asymmetric $(r, s)$ convex polygon theorem
   (`erdos_szekeres_asymmetric_convex_ngon_dichotomy`), the unconditional Erdős–Szekeres convex $k$-gon
   theorem for all $k \ge 2$ (`erdos_szekeres_convex_ngon_theorem`), the general endpoint-sharing
   cup-cap polygon forcing recurrence (`endpoint_sharing_cup_cap_forces_convexNGon`), and the general
   Tóth–Valtr $(k - 1, k)$ recurrence (`tothValtr_general_cup_cap_or_convexNGon`).

3. **Universal Cyclic 10-Triple Pentagon Criterion and KKS $(4, 4, 1)$ Wedge-Pigeonhole Pentagon Forcing**:
   We prove that any 5 points in $\mathbb{R}^2$ (without any $x$-monotonicity hypothesis) whose 10 ordered
   triples have `0 < lineSide p_i p_j p_k` form a convex pentagon (`convexIndep_five_of_all_triples_pos`,
   `hasConvexFiveGon_of_all_triples_pos`), deduce the 4-gon exterior cap-wedge pentagon forcing lemma
   (`kks_quad_cap_wedge_forces_fiveGon`), and establish the Kalbfleisch–Kalbfleisch–Stanton $(4, 4, 1)$
   diagonal-quadrant partition and pentagon forcing reduction (`kks_four_four_one_diagonal_quadrant_dichotomy`,
   `kks_four_four_one_wedge_pentagon_reduction`).

4. **KKS $(4, 3, 2)$ Wedge-Pigeonhole Pentagon Forcing and 9-Point Master Reduction**:
   We prove the $(4, 3, 2)$ inner-line separation dichotomy (`kks_four_three_two_inner_quad_dichotomy`),
   the three-edge wedge-pigeonhole pentagon forcing reduction (`kks_four_three_two_wedge_pentagon_reduction`),
   and the master 9-point nested-subhull synthesis (`kks_nine_point_nested_subhull_master_reduction`).
-/

namespace Erdos107

/-! ## Section 1: All-Triple Cup/Cap Sets (`IsCupSet`, `IsCapSet`) and Universal Skipped-Chord Convex Independence -/

/-- A finite index set $C \subseteq \mathbb{N}$ is an all-triple cup set for $P$ if every strictly increasing
triple $x < y < z$ in $C$ has strictly positive oriented area `0 < lineSide (P x) (P y) (P z)`. -/
def IsCupSet (P : ℕ → ℝ²) (C : Finset ℕ) : Prop :=
  ∀ ⦃x y z : ℕ⦄, x ∈ C → y ∈ C → z ∈ C → x < y → y < z → 0 < lineSide (P x) (P y) (P z)

/-- A finite index set $C \subseteq \mathbb{N}$ is an all-triple cap set for $P$ if every strictly increasing
triple $x < y < z$ in $C$ has strictly negative oriented area `lineSide (P x) (P y) (P z) < 0`. -/
def IsCapSet (P : ℕ → ℝ²) (C : Finset ℕ) : Prop :=
  ∀ ⦃x y z : ℕ⦄, x ∈ C → y ∈ C → z ∈ C → x < y → y < z → lineSide (P x) (P y) (P z) < 0

/-- Any two-element index set $\{a, b\}$ satisfies `IsCupSet P {a, b}`. -/
theorem isCupSet_pair (P : ℕ → ℝ²) (a b : ℕ) : IsCupSet P ({a, b} : Finset ℕ) := by
  intro x y z hx hy hz hxy hyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

#print axioms isCupSet_pair

/-- Any two-element index set $\{b, c\}$ satisfies `IsCapSet P {b, c}`. -/
theorem isCapSet_pair (P : ℕ → ℝ²) (b c : ℕ) : IsCapSet P ({b, c} : Finset ℕ) := by
  intro x y z hx hy hz hxy hyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

#print axioms isCapSet_pair

/-- **Universal Right End-Extension Theorem for Cup Sets**:
If $C$ is an all-triple cup set for an $x$-monotone sequence $P$ whose largest two elements are $a < b$,
and $b < c$ satisfies the single adjacent turn condition `slopeLt (P a) (P b) (P c)`, then `insert c C`
is also an all-triple cup set for $P$. -/
theorem isCupSet_insert_right {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ} {a b c : ℕ}
    (haC : a ∈ C) (hbC : b ∈ C) (hab : a < b) (hbc : b < c)
    (hle_b : ∀ x ∈ C, x ≤ b) (hle_a : ∀ x ∈ C, x < b → x ≤ a)
    (hcup : IsCupSet P C) (hturn : slopeLt (P a) (P b) (P c)) :
    IsCupSet P (insert c C) := by
  have h_ubc : ∀ u ∈ C, u < b → slopeLt (P u) (P b) (P c) := by
    intro u hu hub
    have hua : u ≤ a := hle_a u hu hub
    rcases lt_or_eq_of_le hua with hlt | rfl
    · have huab : slopeLt (P u) (P a) (P b) :=
        (slopeLt_iff_lineSide_pos _ _ _).mpr (hcup hu haC hbC hlt hab)
      exact (slopeLt_trans_left_and_right (hmono hlt) (hmono hab) (hmono hbc) huab hturn).2
    · exact hturn
  intro x y z hx hy hz hxy hyz
  have hxC : x ∈ C := by
    rcases Finset.mem_insert.mp hx with rfl | hxC
    · exfalso
      rcases Finset.mem_insert.mp hz with rfl | hzC
      · omega
      · have := hle_b z hzC; omega
    · exact hxC
  have hyC : y ∈ C := by
    rcases Finset.mem_insert.mp hy with rfl | hyC
    · exfalso
      rcases Finset.mem_insert.mp hz with rfl | hzC
      · omega
      · have := hle_b z hzC; omega
    · exact hyC
  rcases Finset.mem_insert.mp hz with hzc | hzC
  · rw [hzc]
    have hyb : y ≤ b := hle_b y hyC
    rcases lt_or_eq_of_le hyb with hyb_lt | rfl
    · have hxyb : slopeLt (P x) (P y) (P b) :=
        (slopeLt_iff_lineSide_pos _ _ _).mpr (hcup hxC hyC hbC hxy hyb_lt)
      have hybc : slopeLt (P y) (P b) (P c) := h_ubc y hyC hyb_lt
      have hxyc : slopeLt (P x) (P y) (P c) :=
        (slopeLt_trans_left_and_right (hmono hxy) (hmono hyb_lt) (hmono hbc) hxyb hybc).1
      exact (slopeLt_iff_lineSide_pos _ _ _).mp hxyc
    · exact (slopeLt_iff_lineSide_pos _ _ _).mp (h_ubc x hxC hxy)
  · exact hcup hxC hyC hzC hxy hyz

#print axioms isCupSet_insert_right

/-- **Universal Left End-Extension Theorem for Cap Sets**:
If $C$ is an all-triple cap set for an $x$-monotone sequence $P$ whose smallest two elements are $b < c$,
and $a < b$ satisfies the single adjacent turn condition `slopeGt (P a) (P b) (P c)`, then `insert a C`
is also an all-triple cap set for $P$. -/
theorem isCapSet_insert_left {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ} {a b c : ℕ}
    (hbC : b ∈ C) (hcC : c ∈ C) (hab : a < b) (hbc : b < c)
    (hge_b : ∀ x ∈ C, b ≤ x) (hge_c : ∀ x ∈ C, b < x → c ≤ x)
    (hcap : IsCapSet P C) (hturn : slopeGt (P a) (P b) (P c)) :
    IsCapSet P (insert a C) := by
  have h_abw : ∀ w ∈ C, b < w → slopeGt (P a) (P b) (P w) := by
    intro w hw hbw
    have hcw : c ≤ w := hge_c w hw hbw
    rcases lt_or_eq_of_le hcw with hlt | rfl
    · have hbcw : slopeGt (P b) (P c) (P w) :=
        (slopeGt_iff_lineSide_neg _ _ _).mpr (hcap hbC hcC hw hbc hlt)
      exact (slopeGt_trans_left_and_right (hmono hab) (hmono hbc) (hmono hlt) hturn hbcw).1
    · exact hturn
  intro x y z hx hy hz hxy hyz
  have hzC : z ∈ C := by
    rcases Finset.mem_insert.mp hz with rfl | hzC
    · exfalso
      rcases Finset.mem_insert.mp hx with rfl | hxC
      · omega
      · have := hge_b x hxC; omega
    · exact hzC
  have hyC : y ∈ C := by
    rcases Finset.mem_insert.mp hy with rfl | hyC
    · exfalso
      rcases Finset.mem_insert.mp hx with rfl | hxC
      · omega
      · have := hge_b x hxC; omega
    · exact hyC
  rcases Finset.mem_insert.mp hx with hxa | hxC
  · rw [hxa]
    have hby : b ≤ y := hge_b y hyC
    rcases lt_or_eq_of_le hby with hby_lt | rfl
    · have haby : slopeGt (P a) (P b) (P y) := h_abw y hyC hby_lt
      have hbyz : slopeGt (P b) (P y) (P z) :=
        (slopeGt_iff_lineSide_neg _ _ _).mpr (hcap hbC hyC hzC hby_lt hyz)
      have hayz : slopeGt (P a) (P y) (P z) :=
        (slopeGt_trans_left_and_right (hmono hab) (hmono hby_lt) (hmono hyz) haby hbyz).2
      exact (slopeGt_iff_lineSide_neg _ _ _).mp hayz
    · exact (slopeGt_iff_lineSide_neg _ _ _).mp (h_abw z hzC hyz)
  · exact hcap hxC hyC hzC hxy hyz

#print axioms isCapSet_insert_left

/-- **Universal Skipped-Vertex Chord Separation Lemma for Cup Sets**:
For any three consecutive indices $l < v < r$ in an all-triple cup set $C$, the directed chord
$P(r) \to P(l)$ keeps all $P(z)$ ($z \in C \setminus \{v\}$) on its non-positive side while placing
$P(v)$ on its strictly positive side. -/
theorem isCupSet_skipped_chord_sep {P : ℕ → ℝ²} {C : Finset ℕ} (hcup : IsCupSet P C)
    {l v r : ℕ} (hlC : l ∈ C) (hvC : v ∈ C) (hrC : r ∈ C)
    (hlv : l < v) (hvr : v < r) (hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z) :
    (∀ z ∈ C, z ≠ v → lineSide (P r) (P l) (P z) ≤ 0) ∧ 0 < lineSide (P r) (P l) (P v) := by
  have hlr : l < r := lt_trans hlv hvr
  refine ⟨?_, ?_⟩
  · intro z hzC hzv
    rcases hgap z hzC hzv with hzl | hrz
    · rcases lt_or_eq_of_le hzl with hlt | rfl
      · have hpos : 0 < lineSide (P z) (P l) (P r) := hcup hzC hlC hrC hlt hlr
        have hrel : lineSide (P r) (P l) (P z) = - lineSide (P z) (P l) (P r) := by
          dsimp [lineSide]; ring
        linarith
      · rw [lineSide_self_right]
    · rcases lt_or_eq_of_le hrz with hlt | rfl
      · have hpos : 0 < lineSide (P l) (P r) (P z) := hcup hlC hrC hzC hlr hlt
        have hrel : lineSide (P r) (P l) (P z) = - lineSide (P l) (P r) (P z) :=
          lineSide_swap_left _ _ _
        linarith
      · rw [lineSide_self_left]
  · have hpos : 0 < lineSide (P l) (P v) (P r) := hcup hlC hvC hrC hlv hvr
    have hrel : lineSide (P r) (P l) (P v) = lineSide (P l) (P v) (P r) := by
      dsimp [lineSide]; ring
    linarith

#print axioms isCupSet_skipped_chord_sep

/-- **Universal Skipped-Vertex Chord Separation Lemma for Cap Sets**:
For any three consecutive indices $l < v < r$ in an all-triple cap set $C$, the directed chord
$P(l) \to P(r)$ keeps all $P(z)$ ($z \in C \setminus \{v\}$) on its non-positive side while placing
$P(v)$ on its strictly positive side. -/
theorem isCapSet_skipped_chord_sep {P : ℕ → ℝ²} {C : Finset ℕ} (hcap : IsCapSet P C)
    {l v r : ℕ} (hlC : l ∈ C) (hvC : v ∈ C) (hrC : r ∈ C)
    (hlv : l < v) (hvr : v < r) (hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z) :
    (∀ z ∈ C, z ≠ v → lineSide (P l) (P r) (P z) ≤ 0) ∧ 0 < lineSide (P l) (P r) (P v) := by
  have hlr : l < r := lt_trans hlv hvr
  refine ⟨?_, ?_⟩
  · intro z hzC hzv
    rcases hgap z hzC hzv with hzl | hrz
    · rcases lt_or_eq_of_le hzl with hlt | rfl
      · have hneg : lineSide (P z) (P l) (P r) < 0 := hcap hzC hlC hrC hlt hlr
        have hrel : lineSide (P l) (P r) (P z) = lineSide (P z) (P l) (P r) := by
          dsimp [lineSide]; ring
        linarith
      · rw [lineSide_self_left]
    · rcases lt_or_eq_of_le hrz with hlt | rfl
      · exact le_of_lt (hcap hlC hrC hzC hlr hlt)
      · rw [lineSide_self_right]
  · have hneg : lineSide (P l) (P v) (P r) < 0 := hcap hlC hvC hrC hlv hvr
    have hrel : lineSide (P l) (P r) (P v) = - lineSide (P l) (P v) (P r) := by
      dsimp [lineSide]; ring
    linarith

#print axioms isCapSet_skipped_chord_sep

/-- **Universal All-Triple Cup Convex Independence Theorem**:
For every finite index set $C \subseteq \mathbb{N}$ of arbitrary cardinality and every $x$-monotone
sequence $P$, if `IsCupSet P C` holds then the point set $P(C)$ is convex independent (`ConvexIndep`). -/
theorem convexIndep_of_isCupSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ}
    (hcup : IsCupSet P C) : ConvexIndep (P '' (C : Set ℕ)) := by
  apply convexIndep_of_pointwise_strict_sep
  rintro x ⟨v, hvC_coe, rfl⟩
  have hvC : v ∈ C := hvC_coe
  let L := C.filter (fun z => z < v)
  let R := C.filter (fun z => v < z)
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · let l := L.max' hL
      let r := R.min' hR
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hlC : l ∈ C := (Finset.mem_filter.mp hlL).1
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hrC : r ∈ C := (Finset.mem_filter.mp hrR).1
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z := by
        intro z hzC hzv
        rcases lt_or_gt_of_ne hzv with hlt | hgt
        · left
          exact Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC, hlt⟩)
        · right
          exact Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC, hgt⟩)
      obtain ⟨h_le, h_pos⟩ := isCupSet_skipped_chord_sep hcup hlC hvC hrC hlv hvr hgap
      refine ⟨lineNormX (P r) (P l), lineNormY (P r) (P l), lineConst (P r) (P l), ?_, ?_⟩
      · rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
        have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
        have h_side := h_le z hzC_coe hzv
        rw [lineSide_affine_decomp]
        linarith
      · rw [lineSide_affine_decomp]
        linarith
    · let l := L.max' hL
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hxlv : P l 0 < P v 0 := hmono hlv
      refine ⟨1, 0, P l 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · have hzl : z ≤ l := Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩)
        have hxz : P z 0 ≤ P l 0 := hmono.monotone hzl
        linarith
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩
  · by_cases hR : R.Nonempty
    · let r := R.min' hR
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hxvr : P v 0 < P r 0 := hmono hvr
      refine ⟨-1, 0, -P r 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · have hrz : r ≤ z := Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩)
        have hxz : P r 0 ≤ P z 0 := hmono.monotone hrz
        linarith
    · refine ⟨0, 0, -1, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩

#print axioms convexIndep_of_isCupSet

/-- **Universal All-Triple Cap Convex Independence Theorem**:
For every finite index set $C \subseteq \mathbb{N}$ of arbitrary cardinality and every $x$-monotone
sequence $P$, if `IsCapSet P C` holds then the point set $P(C)$ is convex independent (`ConvexIndep`). -/
theorem convexIndep_of_isCapSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ}
    (hcap : IsCapSet P C) : ConvexIndep (P '' (C : Set ℕ)) := by
  apply convexIndep_of_pointwise_strict_sep
  rintro x ⟨v, hvC_coe, rfl⟩
  have hvC : v ∈ C := hvC_coe
  let L := C.filter (fun z => z < v)
  let R := C.filter (fun z => v < z)
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · let l := L.max' hL
      let r := R.min' hR
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hlC : l ∈ C := (Finset.mem_filter.mp hlL).1
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hrC : r ∈ C := (Finset.mem_filter.mp hrR).1
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z := by
        intro z hzC hzv
        rcases lt_or_gt_of_ne hzv with hlt | hgt
        · left
          exact Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC, hlt⟩)
        · right
          exact Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC, hgt⟩)
      obtain ⟨h_le, h_pos⟩ := isCapSet_skipped_chord_sep hcap hlC hvC hrC hlv hvr hgap
      refine ⟨lineNormX (P l) (P r), lineNormY (P l) (P r), lineConst (P l) (P r), ?_, ?_⟩
      · rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
        have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
        have h_side := h_le z hzC_coe hzv
        rw [lineSide_affine_decomp]
        linarith
      · rw [lineSide_affine_decomp]
        linarith
    · let l := L.max' hL
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hxlv : P l 0 < P v 0 := hmono hlv
      refine ⟨1, 0, P l 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · have hzl : z ≤ l := Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩)
        have hxz : P z 0 ≤ P l 0 := hmono.monotone hzl
        linarith
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩
  · by_cases hR : R.Nonempty
    · let r := R.min' hR
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hxvr : P v 0 < P r 0 := hmono hvr
      refine ⟨-1, 0, -P r 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · have hrz : r ≤ z := Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩)
        have hxz : P r 0 ≤ P z 0 := hmono.monotone hrz
        linarith
    · refine ⟨0, 0, -1, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩

#print axioms convexIndep_of_isCapSet

/-! ## Section 2: Inductive $k$-Cup / $k$-Cap Polygon Forcing and the General Erdős–Szekeres Theorem -/

/-- Every $(m + 2)$-cup chain in $S$ ending at $(a, b)$ extracts an $(m + 2)$-element subset
$C \subseteq S$ with maximum $b$, second-largest element $a$, and `IsCupSet P C`. -/
theorem cupChainEnding_exists_isCupSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {S : Finset ℕ} :
    ∀ {m a b : ℕ}, CupChainEnding P S m a b →
      ∃ C : Finset ℕ, C ⊆ S ∧ C.card = m + 2 ∧ a ∈ C ∧ b ∈ C ∧
        (∀ x ∈ C, x ≤ b) ∧ (∀ x ∈ C, x < b → x ≤ a) ∧ IsCupSet P C
  | 0, a, b, ⟨ha, hb, hab⟩ => by
      refine ⟨{a, b}, ?_, ?_, by simp, by simp, ?_, ?_, isCupSet_pair P a b⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · have hne : a ≠ b := ne_of_lt hab
        simp [hne]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      · intro x hx hxb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
  | _ + 1, b, c, ⟨_, hc, hbc, a, hcup, hsl⟩ => by
      obtain ⟨C₀, hC₀sub, hC₀card, haC₀, hbC₀, hC₀le_b, hC₀le_a, hC₀cup⟩ :=
        cupChainEnding_exists_isCupSet hmono hcup
      have hab : a < b := cupChainEnding_lt hcup
      have hc_not_mem : c ∉ C₀ := fun hcC₀ => by
        have := hC₀le_b c hcC₀
        omega
      refine ⟨insert c C₀, ?_, ?_, by simp [hbC₀], by simp, ?_, ?_,
        isCupSet_insert_right hmono haC₀ hbC₀ hab hbc hC₀le_b hC₀le_a hC₀cup hsl⟩
      · exact Finset.insert_subset_iff.mpr ⟨hc, hC₀sub⟩
      · rw [Finset.card_insert_of_notMem hc_not_mem, hC₀card]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · exact le_rfl
        · exact le_trans (hC₀le_b x hx₀) (le_of_lt hbc)
      · intro x hx hxc
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · omega
        · exact hC₀le_b x hx₀

#print axioms cupChainEnding_exists_isCupSet

/-- Every $(k + 2)$-cap chain in $S$ starting at $(b, c)$ extracts a $(k + 2)$-element subset
$C \subseteq S$ with minimum $b$, second-smallest element $c$, and `IsCapSet P C`. -/
theorem capChainStarting_exists_isCapSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {S : Finset ℕ} :
    ∀ {k b c : ℕ}, CapChainStarting P S k b c →
      ∃ C : Finset ℕ, C ⊆ S ∧ C.card = k + 2 ∧ b ∈ C ∧ c ∈ C ∧
        (∀ x ∈ C, b ≤ x) ∧ (∀ x ∈ C, b < x → c ≤ x) ∧ IsCapSet P C
  | 0, b, c, ⟨hb, hc, hbc⟩ => by
      refine ⟨{b, c}, ?_, ?_, by simp, by simp, ?_, ?_, isCapSet_pair P b c⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · have hne : b ≠ c := ne_of_lt hbc
        simp [hne]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      · intro x hx hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
  | _ + 1, a, b, ⟨ha, _, hab, c, hsg, hcap⟩ => by
      obtain ⟨C₀, hC₀sub, hC₀card, hbC₀, hcC₀, hC₀ge_b, hC₀ge_c, hC₀cap⟩ :=
        capChainStarting_exists_isCapSet hmono hcap
      have hbc : b < c := capChainStarting_lt hcap
      have ha_not_mem : a ∉ C₀ := fun haC₀ => by
        have := hC₀ge_b a haC₀
        omega
      refine ⟨insert a C₀, ?_, ?_, by simp, by simp [hbC₀], ?_, ?_,
        isCapSet_insert_left hmono hbC₀ hcC₀ hab hbc hC₀ge_b hC₀ge_c hC₀cap hsg⟩
      · exact Finset.insert_subset_iff.mpr ⟨ha, hC₀sub⟩
      · rw [Finset.card_insert_of_notMem ha_not_mem, hC₀card]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · exact le_rfl
        · exact le_trans (le_of_lt hab) (hC₀ge_b x hx₀)
      · intro x hx hax
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · omega
        · exact hC₀ge_b x hx₀

#print axioms capChainStarting_exists_isCapSet

/-- Any $x$-monotone sequence $P : \mathbb{N} \to \mathbb{R}^2$ is injective. -/
theorem xMonotone_injective {P : ℕ → ℝ²} (hmono : IsXMonotone P) :
    Function.Injective P := by
  intro i j hij
  have h0 : P i 0 = P j 0 := congrArg (fun w : ℝ² => w 0) hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have := hmono hlt; linarith
  · rfl
  · have := hmono hgt; linarith

#print axioms xMonotone_injective

/-- **Inductive $(m + 2)$-Cup Convex Polygon Forcing Theorem**:
For every $m \in \mathbb{N}$, any $x$-monotone sequence $P$ on $S$ satisfying `HasCup P S m`
contains a convex $(m + 2)$-gon in $P(S)$. -/
theorem hasConvexNGon_of_hasCup {P : ℕ → ℝ²} {S : Finset ℕ} {m : ℕ}
    (hmono : IsXMonotone P) (hcup : HasCup P S m) :
    HasConvexNGon (m + 2) (P '' (S : Set ℕ)) := by
  rcases hcup with ⟨a, b, hab⟩
  obtain ⟨C, hCS, hCcard, _, _, _, _, hCcup⟩ := cupChainEnding_exists_isCupSet hmono hab
  refine ⟨C.image P, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective C (xMonotone_injective hmono), hCcard]
  · rw [Finset.coe_image]
    exact Set.image_mono (Finset.coe_subset.mpr hCS)
  · rw [Finset.coe_image]
    exact convexIndep_of_isCupSet hmono hCcup

#print axioms hasConvexNGon_of_hasCup

/-- **Inductive $(k + 2)$-Cap Convex Polygon Forcing Theorem**:
For every $k \in \mathbb{N}$, any $x$-monotone sequence $P$ on $S$ satisfying `HasCap P S k`
contains a convex $(k + 2)$-gon in $P(S)$. -/
theorem hasConvexNGon_of_hasCap {P : ℕ → ℝ²} {S : Finset ℕ} {k : ℕ}
    (hmono : IsXMonotone P) (hcap : HasCap P S k) :
    HasConvexNGon (k + 2) (P '' (S : Set ℕ)) := by
  rcases hcap with ⟨b, c, hbc⟩
  obtain ⟨C, hCS, hCcard, _, _, _, _, hCcap⟩ := capChainStarting_exists_isCapSet hmono hbc
  refine ⟨C.image P, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective C (xMonotone_injective hmono), hCcard]
  · rw [Finset.coe_image]
    exact Set.image_mono (Finset.coe_subset.mpr hCS)
  · rw [Finset.coe_image]
    exact convexIndep_of_isCapSet hmono hCcap

#print axioms hasConvexNGon_of_hasCap

/-- **Universal Inductive $k$-Cup / $k$-Cap Convex $k$-Gon Forcing Theorem**:
For every $k \ge 2$ (and in particular every $k \ge 3$), if an $x$-monotone sequence $P$ on $S$
satisfies `HasCup P S (k - 2) ∨ HasCap P S (k - 2)`, then $P(S)$ contains the vertices of a convex $k$-gon. -/
theorem hasConvexNGon_of_hasCup_or_hasCap {P : ℕ → ℝ²} {S : Finset ℕ} {k : ℕ}
    (hmono : IsXMonotone P) (hk : 2 ≤ k)
    (h : HasCup P S (k - 2) ∨ HasCap P S (k - 2)) :
    HasConvexNGon k (P '' (S : Set ℕ)) := by
  have hk_eq : k - 2 + 2 = k := Nat.sub_add_cancel hk
  rcases h with hcup | hcap
  · rw [← hk_eq]
    exact hasConvexNGon_of_hasCup hmono hcup
  · rw [← hk_eq]
    exact hasConvexNGon_of_hasCap hmono hcap

#print axioms hasConvexNGon_of_hasCup_or_hasCap

/-- **General Asymmetric Erdős–Szekeres $(r, s)$ Convex Polygon Theorem**:
For all $r, s \ge 2$, any $x$-monotone non-trilinear finite sequence $P$ on an index set $S$ with
`cupCapBound r s ≤ S.card` contains either a convex $r$-gon or a convex $s$-gon. -/
theorem erdos_szekeres_asymmetric_convex_ngon_dichotomy {P : ℕ → ℝ²} {S : Finset ℕ} {r s : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hcard : cupCapBound r s ≤ S.card) :
    HasConvexNGon r (P '' (S : Set ℕ)) ∨ HasConvexNGon s (P '' (S : Set ℕ)) := by
  rcases erdos_szekeres_cup_cap_of_ge_two hmono hnontri hr hs S hcard with hcup | hcap
  · exact Or.inl (hasConvexNGon_of_hasCup_or_hasCap hmono hr (Or.inl hcup))
  · exact Or.inr (hasConvexNGon_of_hasCup_or_hasCap hmono hs (Or.inr hcap))

#print axioms erdos_szekeres_asymmetric_convex_ngon_dichotomy

/-- **The General Erdős–Szekeres Convex $k$-Gon Theorem (1935)**:
For every $k \ge 2$, any $x$-monotone non-trilinear finite point sequence $P$ on an index set $S$
of size at least `erdosSzekeresUpper k = (2 * k - 4).choose (k - 2) + 1` contains the vertices of
a convex $k$-gon (`HasConvexNGon k (P '' (S : Set ℕ))`). -/
theorem erdos_szekeres_convex_ngon_theorem {P : ℕ → ℝ²} {S : Finset ℕ} {k : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hk : 2 ≤ k) (hcard : erdosSzekeresUpper k ≤ S.card) :
    HasConvexNGon k (P '' (S : Set ℕ)) :=
  hasConvexNGon_of_hasCup_or_hasCap hmono hk
    (erdos_szekeres_diagonal_cup_cap hmono hnontri hk S hcard)

#print axioms erdos_szekeres_convex_ngon_theorem

/-- **General Endpoint-Sharing Cup–Cap Polygon Forcing Recurrence**:
If an $(m + 2)$-cup ends at $b \in S$ and a $(k + 2)$-cap starts at the same vertex $b \in S$,
then $P(S)$ contains either a convex $(m + 3)$-gon or a convex $(k + 3)$-gon. -/
theorem endpoint_sharing_cup_cap_forces_convexNGon {P : ℕ → ℝ²} {S : Finset ℕ} {m k a b c : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hcup : CupChainEnding P S m a b) (hcap : CapChainStarting P S k b c) :
    HasConvexNGon (m + 3) (P '' (S : Set ℕ)) ∨ HasConvexNGon (k + 3) (P '' (S : Set ℕ)) := by
  rcases cup_end_meets_cap_start hmono hnontri hcup hcap with hcup' | hcap'
  · exact Or.inl (hasConvexNGon_of_hasCup hmono hcup')
  · exact Or.inr (hasConvexNGon_of_hasCap hmono hcap')

#print axioms endpoint_sharing_cup_cap_forces_convexNGon

/-- **General Tóth–Valtr Asymmetric Recurrence for All $k \ge 3$**:
In any $x$-monotone non-trilinear sequence $P$ on $S$ with `tothValtrUpper k ≤ S.card` ($k \ge 3$),
either $P(S)$ already contains a convex $k$-gon, or $S$ simultaneously contains both a $(k - 1)$-cup
and a $(k - 1)$-cap (and hence $P(S)$ contains a convex $(k - 1)$-gon). -/
theorem tothValtr_general_cup_cap_or_convexNGon {P : ℕ → ℝ²} {S : Finset ℕ} {k : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinear P)
    (hk : 3 ≤ k) (hcard : tothValtrUpper k ≤ S.card) :
    (HasCup P S (k - 3) ∧ HasCap P S (k - 3) ∧ HasConvexNGon (k - 1) (P '' (S : Set ℕ))) ∨
      HasConvexNGon k (P '' (S : Set ℕ)) := by
  have hk2 : 2 ≤ k := by omega
  have hk1_2 : 2 ≤ k - 1 := by omega
  have h_asym := tothValtrUpper_eq_cupCapBound_asymmetric hk
  have h_left : cupCapBound (k - 1) k ≤ S.card := by rw [← h_asym.1]; exact hcard
  have h_right : cupCapBound k (k - 1) ≤ S.card := by rw [← h_asym.2]; exact hcard
  have hsub : k - 1 - 2 = k - 3 := by omega
  rcases erdos_szekeres_cup_cap_of_ge_two hmono hnontri hk1_2 hk2 S h_left with hcup | hcap_k
  · rcases erdos_szekeres_cup_cap_of_ge_two hmono hnontri hk2 hk1_2 S h_right with hcup_k | hcap
    · exact Or.inr (hasConvexNGon_of_hasCup_or_hasCap hmono hk2 (Or.inl hcup_k))
    · left
      rw [hsub] at hcup hcap
      have hngon : HasConvexNGon (k - 1) (P '' (S : Set ℕ)) := by
        have hcup' : HasCup P S (k - 1 - 2) := by rw [hsub]; exact hcup
        exact hasConvexNGon_of_hasCup_or_hasCap hmono hk1_2 (Or.inl hcup')
      exact ⟨hcup, hcap, hngon⟩
  · exact Or.inr (hasConvexNGon_of_hasCup_or_hasCap hmono hk2 (Or.inr hcap_k))

#print axioms tothValtr_general_cup_cap_or_convexNGon

/-! ## Section 3: Universal Cyclic 10-Triple Pentagon Criterion and KKS $(4, 4, 1)$ Wedge-Pigeonhole Pentagon Forcing -/

/-- **Universal Cyclic 10-Triple Convex Pentagon Theorem (Without $x$-Monotonicity)**:
For any 5 points $p_1, p_2, p_3, p_4, p_5 \in \mathbb{R}^2$ (without any coordinate-order assumption),
if all 10 ordered triples $(p_i, p_j, p_k)$ ($1 \le i < j < k \le 5$) have `0 < lineSide p_i p_j p_k`,
then $\{p_1, p_2, p_3, p_4, p_5\}$ is convex independent (`ConvexIndep`), with each vertex $p_i$
strictly separated from the other four by the cyclic diagonal $p_{i+1} \to p_{i-1}$. -/
theorem convexIndep_five_of_all_triples_pos {p₁ p₂ p₃ p₄ p₅ : ℝ²}
    (h123 : 0 < lineSide p₁ p₂ p₃) (h124 : 0 < lineSide p₁ p₂ p₄) (h125 : 0 < lineSide p₁ p₂ p₅)
    (h134 : 0 < lineSide p₁ p₃ p₄) (h135 : 0 < lineSide p₁ p₃ p₅) (h145 : 0 < lineSide p₁ p₄ p₅)
    (h234 : 0 < lineSide p₂ p₃ p₄) (h235 : 0 < lineSide p₂ p₃ p₅) (h245 : 0 < lineSide p₂ p₄ p₅)
    (h345 : 0 < lineSide p₃ p₄ p₅) :
    ConvexIndep ({p₁, p₂, p₃, p₄, p₅} : Set ℝ²) := by
  apply convexIndep_five_of_strict_sep
  · have h3_le : lineSide p₂ p₅ p₃ ≤ 0 := by
      have h : lineSide p₂ p₅ p₃ = - lineSide p₂ p₃ p₅ := by dsimp [lineSide]; ring
      linarith
    have h4_le : lineSide p₂ p₅ p₄ ≤ 0 := by
      have h : lineSide p₂ p₅ p₄ = - lineSide p₂ p₄ p₅ := by dsimp [lineSide]; ring
      linarith
    have h1_pos : 0 < lineSide p₂ p₅ p₁ := by
      have h : lineSide p₂ p₅ p₁ = lineSide p₁ p₂ p₅ := by dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos h3_le h4_le h1_pos with ⟨u, v, k, h_2, h_5, h_3, h_4, h_1⟩
    exact ⟨u, v, k, h_2, h_3, h_4, h_5, h_1⟩
  · have h4_le : lineSide p₃ p₁ p₄ ≤ 0 := by
      have h : lineSide p₃ p₁ p₄ = - lineSide p₁ p₃ p₄ := lineSide_swap_left _ _ _
      linarith
    have h5_le : lineSide p₃ p₁ p₅ ≤ 0 := by
      have h : lineSide p₃ p₁ p₅ = - lineSide p₁ p₃ p₅ := lineSide_swap_left _ _ _
      linarith
    have h2_pos : 0 < lineSide p₃ p₁ p₂ := by
      have h : lineSide p₃ p₁ p₂ = lineSide p₁ p₂ p₃ := by dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos h4_le h5_le h2_pos with ⟨u, v, k, h_3, h_1, h_4, h_5, h_2⟩
    exact ⟨u, v, k, h_1, h_3, h_4, h_5, h_2⟩
  · have h1_le : lineSide p₄ p₂ p₁ ≤ 0 := by
      have h : lineSide p₄ p₂ p₁ = - lineSide p₁ p₂ p₄ := by dsimp [lineSide]; ring
      linarith
    have h5_le : lineSide p₄ p₂ p₅ ≤ 0 := by
      have h : lineSide p₄ p₂ p₅ = - lineSide p₂ p₄ p₅ := lineSide_swap_left _ _ _
      linarith
    have h3_pos : 0 < lineSide p₄ p₂ p₃ := by
      have h : lineSide p₄ p₂ p₃ = lineSide p₂ p₃ p₄ := by dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos h1_le h5_le h3_pos with ⟨u, v, k, h_4, h_2, h_1, h_5, h_3⟩
    exact ⟨u, v, k, h_1, h_2, h_4, h_5, h_3⟩
  · have h1_le : lineSide p₅ p₃ p₁ ≤ 0 := by
      have h : lineSide p₅ p₃ p₁ = - lineSide p₁ p₃ p₅ := by dsimp [lineSide]; ring
      linarith
    have h2_le : lineSide p₅ p₃ p₂ ≤ 0 := by
      have h : lineSide p₅ p₃ p₂ = - lineSide p₂ p₃ p₅ := by dsimp [lineSide]; ring
      linarith
    have h4_pos : 0 < lineSide p₅ p₃ p₄ := by
      have h : lineSide p₅ p₃ p₄ = lineSide p₃ p₄ p₅ := by dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos h1_le h2_le h4_pos with ⟨u, v, k, h_5, h_3, h_1, h_2, h_4⟩
    exact ⟨u, v, k, h_1, h_2, h_3, h_5, h_4⟩
  · have h2_le : lineSide p₁ p₄ p₂ ≤ 0 := by
      have h : lineSide p₁ p₄ p₂ = - lineSide p₁ p₂ p₄ := by dsimp [lineSide]; ring
      linarith
    have h3_le : lineSide p₁ p₄ p₃ ≤ 0 := by
      have h : lineSide p₁ p₄ p₃ = - lineSide p₁ p₃ p₄ := by dsimp [lineSide]; ring
      linarith
    rcases lineSide_sep_five_of_le_pos h2_le h3_le h145 with ⟨u, v, k, h_1, h_4, h_2, h_3, h_5⟩
    exact ⟨u, v, k, h_1, h_2, h_3, h_4, h_5⟩

#print axioms convexIndep_five_of_all_triples_pos

/-- **Universal Cyclic 5-Gon Forcing Theorem**:
If $p_1, p_2, p_3, p_4, p_5 \in P$ satisfy all 10 strict positive triple orientations, then they
are automatically pairwise distinct and form a convex pentagon in $P$ (`HasConvexNGon 5 P`). -/
theorem hasConvexFiveGon_of_all_triples_pos {P : Set ℝ²} {p₁ p₂ p₃ p₄ p₅ : ℝ²}
    (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (hp₃ : p₃ ∈ P) (hp₄ : p₄ ∈ P) (hp₅ : p₅ ∈ P)
    (h123 : 0 < lineSide p₁ p₂ p₃) (h124 : 0 < lineSide p₁ p₂ p₄) (h125 : 0 < lineSide p₁ p₂ p₅)
    (h134 : 0 < lineSide p₁ p₃ p₄) (h135 : 0 < lineSide p₁ p₃ p₅) (h145 : 0 < lineSide p₁ p₄ p₅)
    (h234 : 0 < lineSide p₂ p₃ p₄) (h235 : 0 < lineSide p₂ p₃ p₅) (h245 : 0 < lineSide p₂ p₄ p₅)
    (h345 : 0 < lineSide p₃ p₄ p₅) :
    HasConvexNGon 5 P := by
  have h₁₂ : p₁ ≠ p₂ := by intro h; subst h; dsimp [lineSide] at h123; linarith
  have h₁₃ : p₁ ≠ p₃ := by intro h; subst h; dsimp [lineSide] at h134; linarith
  have h₁₄ : p₁ ≠ p₄ := by intro h; subst h; dsimp [lineSide] at h145; linarith
  have h₁₅ : p₁ ≠ p₅ := by intro h; subst h; dsimp [lineSide] at h125; linarith
  have h₂₃ : p₂ ≠ p₃ := by intro h; subst h; dsimp [lineSide] at h234; linarith
  have h₂₄ : p₂ ≠ p₄ := by intro h; subst h; dsimp [lineSide] at h245; linarith
  have h₂₅ : p₂ ≠ p₅ := by intro h; subst h; dsimp [lineSide] at h125; linarith
  have h₃₄ : p₃ ≠ p₄ := by intro h; subst h; dsimp [lineSide] at h345; linarith
  have h₃₅ : p₃ ≠ p₅ := by intro h; subst h; dsimp [lineSide] at h135; linarith
  have h₄₅ : p₄ ≠ p₅ := by intro h; subst h; dsimp [lineSide] at h145; linarith
  refine ⟨{p₁, p₂, p₃, p₄, p₅}, ?_, ?_, ?_⟩
  · simp [h₁₂, h₁₃, h₁₄, h₁₅, h₂₃, h₂₄, h₂₅, h₃₄, h₃₅, h₄₅]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · simpa using convexIndep_five_of_all_triples_pos
      h123 h124 h125 h134 h135 h145 h234 h235 h245 h345

#print axioms hasConvexFiveGon_of_all_triples_pos

/-- **Kalbfleisch–Kalbfleisch–Stanton 4-Gon Cap-Wedge Pentagon Forcing Lemma**:
Given any positively oriented 4-gon $(q_1, q_2, q_3, q_4)$ in $P$, adjoining a fifth point $w \in P$
that lies on the positive open side of all 6 directed chords $q_i \to q_j$ ($1 \le i < j \le 4$)
yields a convex pentagon in $P$. -/
theorem kks_quad_cap_wedge_forces_fiveGon {P : Set ℝ²} {q₁ q₂ q₃ q₄ w : ℝ²}
    (hq₁ : q₁ ∈ P) (hq₂ : q₂ ∈ P) (hq₃ : q₃ ∈ P) (hq₄ : q₄ ∈ P) (hw : w ∈ P)
    (hq123 : 0 < lineSide q₁ q₂ q₃) (hq124 : 0 < lineSide q₁ q₂ q₄)
    (hq134 : 0 < lineSide q₁ q₃ q₄) (hq234 : 0 < lineSide q₂ q₃ q₄)
    (hw12 : 0 < lineSide q₁ q₂ w) (hw13 : 0 < lineSide q₁ q₃ w) (hw14 : 0 < lineSide q₁ q₄ w)
    (hw23 : 0 < lineSide q₂ q₃ w) (hw24 : 0 < lineSide q₂ q₄ w) (hw34 : 0 < lineSide q₃ q₄ w) :
    HasConvexNGon 5 P :=
  hasConvexFiveGon_of_all_triples_pos hq₁ hq₂ hq₃ hq₄ hw
    hq123 hq124 hw12 hq134 hw13 hw14 hq234 hw23 hw24 hw34

#print axioms kks_quad_cap_wedge_forces_fiveGon

/-- **Kalbfleisch–Kalbfleisch–Stanton $(4, 4, 1)$ Diagonal-Quadrant Partition Theorem**:
For any inner 4-gon $(q_1, q_2, q_3, q_4)$ and any innermost point $p \in \mathbb{R}^2$ non-collinear
with the two diagonals $\{q_1, q_3\}$ and $\{q_2, q_4\}$, $p$ lies in one of the four open diagonal
quadrants determined by the signs of `lineSide q₁ q₃ p` and `lineSide q₂ q₄ p`. -/
theorem kks_four_four_one_diagonal_quadrant_dichotomy {q₁ q₂ q₃ q₄ p : ℝ²}
    (hnc13 : ¬ Collinear ℝ ({q₁, q₃, p} : Set ℝ²))
    (hnc24 : ¬ Collinear ℝ ({q₂, q₄, p} : Set ℝ²)) :
    (0 < lineSide q₁ q₃ p ∧ 0 < lineSide q₂ q₄ p) ∨
    (0 < lineSide q₁ q₃ p ∧ 0 < lineSide q₄ q₂ p) ∨
    (0 < lineSide q₃ q₁ p ∧ 0 < lineSide q₂ q₄ p) ∨
    (0 < lineSide q₃ q₁ p ∧ 0 < lineSide q₄ q₂ p) := by
  rcases lineSide_pos_or_neg_of_not_collinear hnc13 with h13_pos | h13_neg
  · rcases lineSide_pos_or_neg_of_not_collinear hnc24 with h24_pos | h24_neg
    · exact Or.inl ⟨h13_pos, h24_pos⟩
    · right; left
      refine ⟨h13_pos, ?_⟩
      rw [lineSide_swap_left]; linarith
  · have h31_pos : 0 < lineSide q₃ q₁ p := by
      rw [lineSide_swap_left]; linarith
    rcases lineSide_pos_or_neg_of_not_collinear hnc24 with h24_pos | h24_neg
    · right; right; left
      exact ⟨h31_pos, h24_pos⟩
    · right; right; right
      refine ⟨h31_pos, ?_⟩
      rw [lineSide_swap_left]; linarith

#print axioms kks_four_four_one_diagonal_quadrant_dichotomy

/-- **Kalbfleisch–Kalbfleisch–Stanton $(4, 4, 1)$ Wedge-Pigeonhole Pentagon Reduction**:
In the $(4, 4, 1)$ nested-hull configuration where the single innermost point $p$ is non-collinear
with both diagonals $q_1 q_3$ and $q_2 q_4$ of the inner 4-gon, `HasConvexNGon 5 P` reduces to
pentagon forcing in each of the four open diagonal quadrants. -/
theorem kks_four_four_one_wedge_pentagon_reduction {P : Set ℝ²} {q₁ q₂ q₃ q₄ p : ℝ²}
    (hnc13 : ¬ Collinear ℝ ({q₁, q₃, p} : Set ℝ²))
    (hnc24 : ¬ Collinear ℝ ({q₂, q₄, p} : Set ℝ²))
    (hQ₁ : 0 < lineSide q₁ q₃ p → 0 < lineSide q₂ q₄ p → HasConvexNGon 5 P)
    (hQ₂ : 0 < lineSide q₁ q₃ p → 0 < lineSide q₄ q₂ p → HasConvexNGon 5 P)
    (hQ₃ : 0 < lineSide q₃ q₁ p → 0 < lineSide q₂ q₄ p → HasConvexNGon 5 P)
    (hQ₄ : 0 < lineSide q₃ q₁ p → 0 < lineSide q₄ q₂ p → HasConvexNGon 5 P) :
    HasConvexNGon 5 P := by
  rcases kks_four_four_one_diagonal_quadrant_dichotomy hnc13 hnc24 with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hQ₁ h1 h2
  · exact hQ₂ h1 h2
  · exact hQ₃ h1 h2
  · exact hQ₄ h1 h2

#print axioms kks_four_four_one_wedge_pentagon_reduction

/-! ## Section 4: KKS $(4, 3, 2)$ Wedge-Pigeonhole Pentagon Forcing and 9-Point Master Reduction -/

/-- **Kalbfleisch–Kalbfleisch–Stanton $(4, 3, 2)$ Inner-Line Convex 4-Gon Dichotomy**:
When two innermost points $p_1, p_2$ lie strictly inside the inner triangle $\{a, b, c\}$ and
none of $a, b, c$ is collinear with $\{p_1, p_2\}$, the line $p_1 \leftrightarrow p_2$ places
at least two vertices of $\{a, b, c\}$ on the same open half-plane, forcing at least one of
$\{a, b, p_1, p_2\}$, $\{b, c, p_1, p_2\}$, or $\{c, a, p_1, p_2\}$ to be `ConvexIndep`. -/
theorem kks_four_three_two_inner_quad_dichotomy {a b c p₁ p₂ : ℝ²}
    (habp₁ : 0 < lineSide a b p₁) (habp₂ : 0 < lineSide a b p₂)
    (hbcp₁ : 0 < lineSide b c p₁) (hbcp₂ : 0 < lineSide b c p₂)
    (hcap₁ : 0 < lineSide c a p₁) (hcap₂ : 0 < lineSide c a p₂)
    (hnca : ¬ Collinear ℝ ({p₁, p₂, a} : Set ℝ²))
    (hncb : ¬ Collinear ℝ ({p₁, p₂, b} : Set ℝ²))
    (hncc : ¬ Collinear ℝ ({p₁, p₂, c} : Set ℝ²)) :
    ConvexIndep ({a, b, p₁, p₂} : Set ℝ²) ∨
    ConvexIndep ({b, c, p₁, p₂} : Set ℝ²) ∨
    ConvexIndep ({c, a, p₁, p₂} : Set ℝ²) := by
  rcases three_vertices_same_open_side_of_line hnca hncb hncc with hab | hbc | hca
  · exact Or.inl (convexIndep_four_of_same_open_side habp₁ habp₂ hab)
  · exact Or.inr (Or.inl (convexIndep_four_of_same_open_side hbcp₁ hbcp₂ hbc))
  · exact Or.inr (Or.inr (convexIndep_four_of_same_open_side hcap₁ hcap₂ hca))

#print axioms kks_four_three_two_inner_quad_dichotomy

/-- **Kalbfleisch–Kalbfleisch–Stanton $(4, 3, 2)$ Three-Edge Wedge-Pigeonhole Pentagon Reduction**:
In the $(4, 3, 2)$ configuration with inner triangle $\{a, b, c\}$ and innermost pair $\{p_1, p_2\}$,
pigeonhole separation along the line $p_1 \leftrightarrow p_2$ reduces `HasConvexNGon 5 P` to the
three cyclic inner-edge cases in which $(a, b)$, $(b, c)$, or $(c, a)$ lie on the same open side of $p_1 p_2$. -/
theorem kks_four_three_two_wedge_pentagon_reduction {P : Set ℝ²} {a b c p₁ p₂ : ℝ²}
    (hnca : ¬ Collinear ℝ ({p₁, p₂, a} : Set ℝ²))
    (hncb : ¬ Collinear ℝ ({p₁, p₂, b} : Set ℝ²))
    (hncc : ¬ Collinear ℝ ({p₁, p₂, c} : Set ℝ²))
    (hab : ((0 < lineSide p₁ p₂ a ∧ 0 < lineSide p₁ p₂ b) ∨
      (lineSide p₁ p₂ a < 0 ∧ lineSide p₁ p₂ b < 0)) → HasConvexNGon 5 P)
    (hbc : ((0 < lineSide p₁ p₂ b ∧ 0 < lineSide p₁ p₂ c) ∨
      (lineSide p₁ p₂ b < 0 ∧ lineSide p₁ p₂ c < 0)) → HasConvexNGon 5 P)
    (hca : ((0 < lineSide p₁ p₂ c ∧ 0 < lineSide p₁ p₂ a) ∨
      (lineSide p₁ p₂ c < 0 ∧ lineSide p₁ p₂ a < 0)) → HasConvexNGon 5 P) :
    HasConvexNGon 5 P := by
  rcases three_vertices_same_open_side_of_line hnca hncb hncc with h_ab | h_bc | h_ca
  · exact hab h_ab
  · exact hbc h_bc
  · exact hca h_ca

#print axioms kks_four_three_two_wedge_pentagon_reduction

/-- **Kalbfleisch–Kalbfleisch–Stanton $(4, 5)$-Layer Complete Pentagon Reduction**:
For any 9-point set $P$ with outer 4-gon $H \subseteq P$ ($|H| = 4$) and inner sub-hull $H_2 \subseteq P \setminus H$
($3 \le |H_2|$, `ConvexIndep H₂`), `HasConvexNGon 5 (P : Set ℝ²)` holds whenever the two sub-cases
$(4, 4, 1)$ and $(4, 3, 2)$ force a convex pentagon. -/
theorem kks_four_five_layer_complete_reduction {P H H₂ : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH4 : H.card = 4)
    (hH₂ : H₂ ⊆ P \ H) (hH₂3 : 3 ≤ H₂.card) (hconv₂ : ConvexIndep (H₂ : Set ℝ²))
    (h441 : H₂.card = 4 → ((P \ H) \ H₂).card = 1 → HasConvexNGon 5 (P : Set ℝ²))
    (h432 : H₂.card = 3 → ((P \ H) \ H₂).card = 2 → HasConvexNGon 5 (P : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) := by
  rcases kks_nine_point_layer_four_five_subhull_dichotomy hP hHP hH4 hH₂ hH₂3 hconv₂ with
    h5 | ⟨h4, h1⟩ | ⟨h3, h2⟩
  · exact h5
  · exact h441 h4 h1
  · exact h432 h3 h2

#print axioms kks_four_five_layer_complete_reduction

/-- **Kalbfleisch–Kalbfleisch–Stanton 9-Point Four-Subcase Master Pentagon Reduction**:
For any 9-point set $P \subseteq \mathbb{R}^2$ with convex-independent outer hull $H \subseteq P$ ($3 \le |H|$)
and convex-independent second hull layer $H_2 \subseteq P \setminus H$ ($3 \le |H_2|$), `HasConvexNGon 5 (P : Set ℝ²)`
holds whenever the four 3-layer profiles $(4, 4, 1)$, $(4, 3, 2)$, $(3, 4, 2)$, and $(3, 3, 3)$ force a convex pentagon. -/
theorem kks_nine_point_nested_subhull_master_reduction {P H H₂ : Finset ℝ²}
    (hP : P.card = 9) (hHP : H ⊆ P) (hH3 : 3 ≤ H.card) (hconv : ConvexIndep (H : Set ℝ²))
    (hH₂ : H₂ ⊆ P \ H) (hH₂3 : 3 ≤ H₂.card) (hconv₂ : ConvexIndep (H₂ : Set ℝ²))
    (h441 : H.card = 4 → H₂.card = 4 → ((P \ H) \ H₂).card = 1 → HasConvexNGon 5 (P : Set ℝ²))
    (h432 : H.card = 4 → H₂.card = 3 → ((P \ H) \ H₂).card = 2 → HasConvexNGon 5 (P : Set ℝ²))
    (h342 : H.card = 3 → H₂.card = 4 → ((P \ H) \ H₂).card = 2 → HasConvexNGon 5 (P : Set ℝ²))
    (h333 : H.card = 3 → H₂.card = 3 → ((P \ H) \ H₂).card = 3 → HasConvexNGon 5 (P : Set ℝ²)) :
    HasConvexNGon 5 (P : Set ℝ²) := by
  rcases kks_nine_point_hull_layer_dichotomy hP hHP hH3 hconv with h5 | ⟨h4, _⟩ | ⟨h3, _⟩
  · exact h5
  · exact kks_four_five_layer_complete_reduction hP hHP h4 hH₂ hH₂3 hconv₂ (h441 h4) (h432 h4)
  · rcases kks_nine_point_layer_three_six_subhull_dichotomy hP hHP h3 hH₂ hH₂3 hconv₂ with
      h5 | ⟨h2_4, h3_2⟩ | ⟨h2_3, h3_3⟩
    · exact h5
    · exact h342 h3 h2_4 h3_2
    · exact h333 h3 h2_3 h3_3

#print axioms kks_nine_point_nested_subhull_master_reduction

end Erdos107
