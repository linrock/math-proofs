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
public import XMonotonePerturbationBridgeAndWedgePigeonholePentagon107

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
# Erdős Problem #107 (`Round 126`): Unconditional 5-Point Happy Ending Theorem ($f(4) = 5$) and 8-Point Pentagon-Free Certificate ($9 \le f(5)$)

This module extends `Erdos107Unified435.lean`,
`InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107.lean`, and
`XMonotonePerturbationBridgeAndWedgePigeonholePentagon107.lean` across four sections:

1. **Oriented-Area Triangle-Sum Identity, Plücker/Cramer Containment Transitivity, and Universal Barycentric Convex-Hull Membership**:
   We define `InPosTriangle a b c d` ($0 < \operatorname{lineSide}(a,b,d) \land 0 < \operatorname{lineSide}(b,c,d) \land 0 < \operatorname{lineSide}(c,a,d)$),
   prove the oriented-area decomposition `lineSide_triangle_sum` and the 5-point Plücker/Cramer syzygies
   (`lineSide_cramer_right`, `lineSide_cramer_left`), establish strict triangle-containment transitivity
   (`inPosTriangle_trans`), prove the explicit Cramer barycentric identity `barycentric_of_lineSide_ne_zero`,
   and show that every point satisfying `InPosTriangle a b c p` lies in `convexHull ℝ {a, b, c}`
   (`inPosTriangle_mem_convexHull`) and therefore refutes `ConvexIndep S` whenever $\{a, b, c, p\} \subseteq S$
   (`not_convexIndep_of_inPosTriangle`).

2. **Unconditional 5-Point Happy Ending Theorem (`five_mem_cardSet_four`, `f_four_eq_five`)**:
   We prove the universal 4-point positive-triangle dichotomy (`four_point_pos_triangle_dichotomy`): for any
   positively oriented triangle $(a, b, c)$ and fourth point $d$ in general position, either $\{a, b, c, d\}$
   already forms a convex 4-gon (`hasConvexFourGon_of_two_pos_one_neg`), or one of the four points lies
   strictly inside the positively oriented triangle formed by the other three. Combining this dichotomy with
   `inPosTriangle_trans` and the 3-outer + 2-interior Happy Ending lemma `hasConvexFourGon_of_triangle_two_interior`,
   we prove that any 5 distinct `NonTrilinear` points in $\mathbb{R}^2$ contain a convex 4-gon
   (`hasConvexFourGon_of_five_distinct_nonTrilinear`), establishing `5 ∈ cardSet 4` (`five_mem_cardSet_four`)
   and $f(4) = 5 = 2^{4-2} + 1$ unconditionally (`f_four_eq_five`, `f_four_eq_five_unconditional`).

3. **8-Point Erdős–Szekeres / Kalbfleisch–Stanton Pentagon-Free Certificate (`eight_not_mem_cardSet_five`, `nine_le_f_five`)**:
   We prove the universal 3-cap-plus-upper-point and 3-cup-plus-lower-point non-convexity criteria
   (`not_convexIndep_of_three_cap_and_above`, `not_convexIndep_of_three_cup_and_below`), construct the
   explicit 8-point integer configuration `esEightFinset` combining a 4-cap and a 4-cup, verify general
   position (`esEightFinset_nonTrilinear`, `esEightFinset_card`), and prove that no 5-point subset of
   `esEightFinset` is convex independent (`not_hasConvexFiveGon_esEightFinset`). This establishes
   `8 ∉ cardSet 5` (`eight_not_mem_cardSet_five`) and the unconditional lower bound $9 \le f(5)$
   (`nine_le_f_five`, `f_five_bounds_unconditional : 9 ≤ f 5 ∧ f 5 ≤ 21`).

4. **Complete Erdős–Szekeres Bounds for $3 \le n \le 5$ and Conditional Reductions for `erdos_107`**:
   We establish `f n = 2^(n - 2) + 1` unconditionally for $3 \le n \le 4$ (`f_eq_conjectured_of_le_four`),
   prove the full Erdős–Szekeres lower and upper bounds $2^{n-2} + 1 \le f(n) \le \binom{2n-4}{n-2} + 1$
   for all $3 \le n \le 5$ (`ersz_bounds_of_le_five`), upgrade the conditional $f(5) = 9$ characterization to
   require only `9 ∈ cardSet 5` (`f_five_eq_nine_of_nine_mem`), and prove zero-`sorry` top-down conditional
   reductions for the FormalConjectures target `erdos_107` (`erdos_107_of_ge_five`,
   `erdos_107_of_lower_ge_six_and_upper_ge_five`).
-/

namespace Erdos107

/-! ## Section 1: Oriented-Area Syzygies, Containment Transitivity, and Barycentric Convex-Hull Membership -/

/-- A point $d \in \mathbb{R}^2$ lies in the open interior of the positively oriented triangle $(a, b, c)$
if it lies on the strictly positive open side of all three directed edges $a \to b$, $b \to c$, and $c \to a$. -/
def InPosTriangle (a b c d : ℝ²) : Prop :=
  0 < lineSide a b d ∧ 0 < lineSide b c d ∧ 0 < lineSide c a d

/-- **Universal Oriented-Area Triangle-Sum Identity**:
For any four points $a, b, c, d \in \mathbb{R}^2$, the signed areas of $\triangle abd$, $\triangle bcd$,
and $\triangle cad$ sum identically to the signed area of $\triangle abc$. -/
theorem lineSide_triangle_sum (a b c d : ℝ²) :
    lineSide a b d + lineSide b c d + lineSide c a d = lineSide a b c := by
  dsimp [lineSide]; ring

#print axioms lineSide_triangle_sum

/-- **Five-Point Plücker/Cramer Identity at Vertex $b$**:
For any five points $a, b, c, d, e \in \mathbb{R}^2$,
$\operatorname{lineSide}(a,b,c)\operatorname{lineSide}(b,e,d) = \operatorname{lineSide}(a,b,d)\operatorname{lineSide}(b,e,c) + \operatorname{lineSide}(b,c,d)\operatorname{lineSide}(a,b,e)$. -/
theorem lineSide_cramer_right (a b c d e : ℝ²) :
    lineSide a b c * lineSide b e d =
      lineSide a b d * lineSide b e c + lineSide b c d * lineSide a b e := by
  dsimp [lineSide]; ring

#print axioms lineSide_cramer_right

/-- **Five-Point Plücker/Cramer Identity at Vertex $a$**:
For any five points $a, b, c, d, e \in \mathbb{R}^2$,
$\operatorname{lineSide}(a,b,c)\operatorname{lineSide}(e,a,d) = \operatorname{lineSide}(c,a,d)\operatorname{lineSide}(a,b,e) + \operatorname{lineSide}(a,b,d)\operatorname{lineSide}(e,a,c)$. -/
theorem lineSide_cramer_left (a b c d e : ℝ²) :
    lineSide a b c * lineSide e a d =
      lineSide c a d * lineSide a b e + lineSide a b d * lineSide e a c := by
  dsimp [lineSide]; ring

#print axioms lineSide_cramer_left

/-- Cyclic permutation of the outer triangle vertices preserves `InPosTriangle`. -/
theorem inPosTriangle_cycle {a b c d : ℝ²} (h : InPosTriangle a b c d) :
    InPosTriangle b c a d :=
  ⟨h.2.1, h.2.2, h.1⟩

#print axioms inPosTriangle_cycle

/-- Any triangle $(a, b, c)$ containing a point $d$ with `InPosTriangle a b c d` is positively oriented. -/
theorem inPosTriangle_pos_outer {a b c d : ℝ²} (h : InPosTriangle a b c d) :
    0 < lineSide a b c := by
  have hsum := lineSide_triangle_sum a b c d
  linarith [h.1, h.2.1, h.2.2]

#print axioms inPosTriangle_pos_outer

/-- **Strict Triangle-Containment Transitivity (`inPosTriangle_trans`)**:
If $d$ lies strictly inside $\triangle abc$ and $c$ lies strictly inside $\triangle abe$,
then $d$ also lies strictly inside $\triangle abe$. -/
theorem inPosTriangle_trans {a b c d e : ℝ²}
    (hd : InPosTriangle a b c d) (hc : InPosTriangle a b e c) :
    InPosTriangle a b e d := by
  have habc : 0 < lineSide a b c := hc.1
  have habe : 0 < lineSide a b e := inPosTriangle_pos_outer hc
  have habd : 0 < lineSide a b d := hd.1
  have hbcd : 0 < lineSide b c d := hd.2.1
  have hcad : 0 < lineSide c a d := hd.2.2
  have hbec : 0 < lineSide b e c := hc.2.1
  have heac : 0 < lineSide e a c := hc.2.2
  have hcr₁ := lineSide_cramer_right a b c d e
  have hcr₂ := lineSide_cramer_left a b c d e
  have hprod₁ : 0 < lineSide a b c * lineSide b e d := by
    rw [hcr₁]; positivity
  have hprod₂ : 0 < lineSide a b c * lineSide e a d := by
    rw [hcr₂]; positivity
  exact ⟨habd,
    pos_of_mul_pos_right hprod₁ (le_of_lt habc),
    pos_of_mul_pos_right hprod₂ (le_of_lt habc)⟩

#print axioms inPosTriangle_trans

/-- **Universal Cramer Barycentric Identity in $\mathbb{R}^2$**:
For any non-collinear triple $(a, b, c)$ with $\operatorname{lineSide}(a,b,c) \ne 0$ and any point $p \in \mathbb{R}^2$,
$p$ equals the affine combination of $a, b, c$ with weights $\operatorname{lineSide}(b,c,p)/\operatorname{lineSide}(a,b,c)$,
$\operatorname{lineSide}(c,a,p)/\operatorname{lineSide}(a,b,c)$, and $\operatorname{lineSide}(a,b,p)/\operatorname{lineSide}(a,b,c)$. -/
theorem barycentric_of_lineSide_ne_zero (a b c p : ℝ²) (h : lineSide a b c ≠ 0) :
    (lineSide b c p / lineSide a b c) • a +
    (lineSide c a p / lineSide a b c) • b +
    (lineSide a b p / lineSide a b c) • c = p := by
  ext i
  fin_cases i <;>
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [h]
    dsimp [lineSide]
    ring

#print axioms barycentric_of_lineSide_ne_zero

/-- **Universal Positive-Triangle Convex-Hull Membership Theorem**:
Whenever `InPosTriangle a b c p` holds, $p \in \operatorname{convexHull}\,\mathbb{R}\,\{a, b, c\}$. -/
theorem inPosTriangle_mem_convexHull {a b c p : ℝ²} (h : InPosTriangle a b c p) :
    p ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := by
  have habc : 0 < lineSide a b c := inPosTriangle_pos_outer h
  have habc_ne : lineSide a b c ≠ 0 := ne_of_gt habc
  have hbc : 0 < lineSide b c p := h.2.1
  have hca : 0 < lineSide c a p := h.2.2
  have hab : 0 < lineSide a b p := h.1
  have hbcca : 0 < lineSide b c p + lineSide c a p := by linarith
  have hbcca_ne : lineSide b c p + lineSide c a p ≠ 0 := ne_of_gt hbcca
  have hsum := lineSide_triangle_sum a b c p
  rw [← barycentric_of_lineSide_ne_zero a b c p habc_ne]
  have hdecomp :
      (lineSide b c p / lineSide a b c) • a +
      (lineSide c a p / lineSide a b c) • b +
      (lineSide a b p / lineSide a b c) • c =
      ((lineSide b c p + lineSide c a p) / lineSide a b c) •
        ((lineSide b c p / (lineSide b c p + lineSide c a p)) • a +
         (lineSide c a p / (lineSide b c p + lineSide c a p)) • b) +
      (lineSide a b p / lineSide a b c) • c := by
    ext i
    fin_cases i <;>
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [habc_ne, hbcca_ne]
  rw [hdecomp]
  have h_conv := convex_convexHull ℝ ({a, b, c} : Set ℝ²)
  have ha_mem : a ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
  have hb_mem : b ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
  have hc_mem : c ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
  have hmid :
      (lineSide b c p / (lineSide b c p + lineSide c a p)) • a +
      (lineSide c a p / (lineSide b c p + lineSide c a p)) • b ∈
        convexHull ℝ ({a, b, c} : Set ℝ²) := by
    apply h_conv ha_mem hb_mem
    · exact div_nonneg (le_of_lt hbc) (le_of_lt hbcca)
    · exact div_nonneg (le_of_lt hca) (le_of_lt hbcca)
    · field_simp [hbcca_ne]
  apply h_conv hmid hc_mem
  · exact div_nonneg (le_of_lt hbcca) (le_of_lt habc)
  · exact div_nonneg (le_of_lt hab) (le_of_lt habc)
  · field_simp [habc_ne]; linarith

#print axioms inPosTriangle_mem_convexHull

/-- **Universal Interior-Point Non-Convexity Criterion**:
If $a, b, c, p \in S$ satisfy `InPosTriangle a b c p`, then $S$ is not convex independent (`¬ ConvexIndep S`). -/
theorem not_convexIndep_of_inPosTriangle {S : Set ℝ²} {a b c p : ℝ²}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hpS : p ∈ S)
    (h : InPosTriangle a b c p) :
    ¬ ConvexIndep S := by
  intro hci
  apply hci p hpS
  have hpa : p ≠ a := by
    intro heq; subst heq; have := h.1; dsimp [lineSide] at this; linarith
  have hpb : p ≠ b := by
    intro heq; subst heq; have := h.1; dsimp [lineSide] at this; linarith
  have hpc : p ≠ c := by
    intro heq; subst heq; have := h.2.1; dsimp [lineSide] at this; linarith
  have hsub : ({a, b, c} : Set ℝ²) ⊆ S \ {p} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨haS, hpa.symm⟩
    · exact ⟨hbS, hpb.symm⟩
    · exact ⟨hcS, hpc.symm⟩
  exact convexHull_mono hsub (inPosTriangle_mem_convexHull h)

#print axioms not_convexIndep_of_inPosTriangle

/-! ## Section 2: Unconditional 5-Point Happy Ending Theorem (`5 ∈ cardSet 4` and `f 4 = 5`) -/

/-- When $d$ lies on the positive side of $a \to b$ and $b \to c$ and on the negative side of $c \to a$
around a positively oriented triangle $(a, b, c)$, the four points $\{a, b, c, d\}$ form a convex 4-gon in $P$. -/
theorem hasConvexFourGon_of_two_pos_one_neg {P : Set ℝ²} {a b c d : ℝ²}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (habc : 0 < lineSide a b c)
    (habd : 0 < lineSide a b d) (hbcd : 0 < lineSide b c d) (hcad : lineSide c a d < 0) :
    HasConvexNGon 4 P := by
  have hcd : c ≠ d := by
    intro h; subst h; dsimp [lineSide] at hcad; linarith
  have hcda : 0 < lineSide c d a := by
    have h : lineSide c d a = - lineSide c a d := by dsimp [lineSide]; ring
    linarith
  have hcdb : 0 < lineSide c d b := by
    have h : lineSide c d b = lineSide b c d := by dsimp [lineSide]; ring
    linarith
  exact hasConvexFourGon_of_same_open_side_edge ha hb hc hd hcd habc habd (Or.inl ⟨hcda, hcdb⟩)

#print axioms hasConvexFourGon_of_two_pos_one_neg

/-- **Universal Four-Point Convex-Quadrilateral or Interior-Triangle Dichotomy**:
For any positively oriented triangle $(a, b, c)$ in $P$ and any fourth point $d \in P$ non-collinear
with the three edges of $\triangle abc$, either $\{a, b, c, d\}$ forms a convex 4-gon in $P$, or one
of the four points lies strictly inside the positively oriented triangle formed by the other three. -/
theorem four_point_pos_triangle_dichotomy {P : Set ℝ²} {a b c d : ℝ²}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (habc : 0 < lineSide a b c)
    (habd_nc : ¬ Collinear ℝ ({a, b, d} : Set ℝ²))
    (hbcd_nc : ¬ Collinear ℝ ({b, c, d} : Set ℝ²))
    (hcad_nc : ¬ Collinear ℝ ({c, a, d} : Set ℝ²)) :
    HasConvexNGon 4 P ∨
    InPosTriangle a b c d ∨
    InPosTriangle a b d c ∨
    InPosTriangle b c d a ∨
    InPosTriangle c a d b := by
  have hbca : 0 < lineSide b c a := by rw [lineSide_cycle]; exact habc
  have hcab : 0 < lineSide c a b := by rw [lineSide_cycle]; exact hbca
  rcases lineSide_pos_or_neg_of_not_collinear habd_nc with s1p | s1n <;>
  rcases lineSide_pos_or_neg_of_not_collinear hbcd_nc with s2p | s2n <;>
  rcases lineSide_pos_or_neg_of_not_collinear hcad_nc with s3p | s3n
  · exact Or.inr (Or.inl ⟨s1p, s2p, s3p⟩)
  · exact Or.inl (hasConvexFourGon_of_two_pos_one_neg ha hb hc hd habc s1p s2p s3n)
  · exact Or.inl (hasConvexFourGon_of_two_pos_one_neg hc ha hb hd hcab s3p s1p s2n)
  · right; right; left
    refine ⟨habc, ?_, ?_⟩
    · rw [lineSide_swap_right]; linarith
    · have h : lineSide d a c = - lineSide c a d := by dsimp [lineSide]; ring
      linarith
  · exact Or.inl (hasConvexFourGon_of_two_pos_one_neg hb hc ha hd hbca s2p s3p s1n)
  · right; right; right; left
    refine ⟨hbca, ?_, ?_⟩
    · rw [lineSide_swap_right]; linarith
    · have h : lineSide d b a = - lineSide a b d := by dsimp [lineSide]; ring
      linarith
  · right; right; right; right
    refine ⟨hcab, ?_, ?_⟩
    · rw [lineSide_swap_right]; linarith
    · have h : lineSide d c b = - lineSide b c d := by dsimp [lineSide]; ring
      linarith
  · exfalso
    have hsum := lineSide_triangle_sum a b c d
    linarith

#print axioms four_point_pos_triangle_dichotomy

/-- In any `NonTrilinear` point set $P$, two distinct points $p \ne q$ satisfying `InPosTriangle a b c p`
and `InPosTriangle a b c q` force a convex 4-gon in $P$. -/
theorem hasConvexFourGon_of_two_inPosTriangle {P : Set ℝ²} {a b c p q : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hpP : p ∈ P) (hqP : q ∈ P)
    (hnt : NonTrilinear P) (hpq : p ≠ q)
    (hp : InPosTriangle a b c p) (hq : InPosTriangle a b c q) :
    HasConvexNGon 4 P := by
  have hpa : p ≠ a := by
    intro h; subst h; have := hp.1; dsimp [lineSide] at this; linarith
  have hqa : q ≠ a := by
    intro h; subst h; have := hq.1; dsimp [lineSide] at this; linarith
  have hpb : p ≠ b := by
    intro h; subst h; have := hp.1; dsimp [lineSide] at this; linarith
  have hqb : q ≠ b := by
    intro h; subst h; have := hq.1; dsimp [lineSide] at this; linarith
  have hpc : p ≠ c := by
    intro h; subst h; have := hp.2.1; dsimp [lineSide] at this; linarith
  have hqc : q ≠ c := by
    intro h; subst h; have := hq.2.1; dsimp [lineSide] at this; linarith
  exact hasConvexFourGon_of_triangle_two_interior haP hbP hcP hpP hqP hpq
    hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 hq.2.2
    (hnt hpP hqP haP hpq hqa hpa)
    (hnt hpP hqP hbP hpq hqb hpb)
    (hnt hpP hqP hcP hpq hqc hpc)

#print axioms hasConvexFourGon_of_two_inPosTriangle

/-- If $d \in P$ lies strictly inside $\triangle abc$ (`InPosTriangle a b c d`), then adjoining any fifth
distinct point $e \in P$ in a `NonTrilinear` point set $P$ forces `HasConvexNGon 4 P`. -/
theorem hasConvexFourGon_of_inPosTriangle_and_fifth_point {P : Set ℝ²} {a b c d e : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (hnt : NonTrilinear P) (hd : InPosTriangle a b c d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    HasConvexNGon 4 P := by
  have habc : 0 < lineSide a b c := inPosTriangle_pos_outer hd
  have hab : a ≠ b := by
    intro h; subst h; dsimp [lineSide] at habc; linarith
  have hbc : b ≠ c := by
    intro h; subst h; dsimp [lineSide] at habc; linarith
  have hca : c ≠ a := by
    intro h; subst h; dsimp [lineSide] at habc; linarith
  have had : a ≠ d := by
    intro h; subst h; have := hd.1; dsimp [lineSide] at this; linarith
  have hbd : b ≠ d := by
    intro h; subst h; have := hd.1; dsimp [lineSide] at this; linarith
  have hcd : c ≠ d := by
    intro h; subst h; have := hd.2.1; dsimp [lineSide] at this; linarith
  rcases four_point_pos_triangle_dichotomy haP hbP hcP heP habc
      (hnt haP hbP heP hab hbe hae)
      (hnt hbP hcP heP hbc hce hbe)
      (hnt hcP haP heP hca hae hce) with
    h4 | he | habec | hbcea | hcaeb
  · exact h4
  · exact hasConvexFourGon_of_two_inPosTriangle haP hbP hcP hdP heP hnt hde hd he
  · exact hasConvexFourGon_of_two_inPosTriangle haP hbP heP hcP hdP hnt hcd
      habec (inPosTriangle_trans hd habec)
  · have hd_bca : InPosTriangle b c a d := inPosTriangle_cycle hd
    exact hasConvexFourGon_of_two_inPosTriangle hbP hcP heP haP hdP hnt had
      hbcea (inPosTriangle_trans hd_bca hbcea)
  · have hd_cab : InPosTriangle c a b d := inPosTriangle_cycle (inPosTriangle_cycle hd)
    exact hasConvexFourGon_of_two_inPosTriangle hcP haP heP hbP hdP hnt hbd
      hcaeb (inPosTriangle_trans hd_cab hcaeb)

#print axioms hasConvexFourGon_of_inPosTriangle_and_fifth_point

/-- Any five distinct points $a, b, c, d, e$ in a `NonTrilinear` set $P$ with $0 < \operatorname{lineSide}(a,b,c)$
contain a convex 4-gon. -/
theorem hasConvexFourGon_of_pos_outer_and_two_points {P : Set ℝ²} {a b c d e : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (hnt : NonTrilinear P) (habc : 0 < lineSide a b c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    HasConvexNGon 4 P := by
  rcases four_point_pos_triangle_dichotomy haP hbP hcP hdP habc
      (hnt haP hbP hdP hab hbd had)
      (hnt hbP hcP hdP hbc hcd hbd)
      (hnt hcP haP hdP hca had hcd) with
    h4 | habcd | habdc | hbcda | hcadb
  · exact h4
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point haP hbP hcP hdP heP hnt habcd hae hbe hce hde
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point haP hbP hdP hcP heP hnt habdc hae hbe hde hce
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point hbP hcP hdP haP heP hnt hbcda hbe hce hde hae
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point hcP haP hdP hbP heP hnt hcadb hce hae hde hbe

#print axioms hasConvexFourGon_of_pos_outer_and_two_points

/-- **Esther Klein's 5-Point Happy Ending Theorem for Distinct Points**:
Any five pairwise distinct points $a, b, c, d, e$ in a `NonTrilinear` planar set $P \subseteq \mathbb{R}^2$
contain the vertices of a convex 4-gon (`HasConvexNGon 4 P`). -/
theorem hasConvexFourGon_of_five_distinct_nonTrilinear {P : Set ℝ²} {a b c d e : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (hnt : NonTrilinear P)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    HasConvexNGon 4 P := by
  rcases lineSide_pos_or_neg_of_not_collinear (hnt haP hbP hcP hab hbc hca.symm) with habc | hbac
  · exact hasConvexFourGon_of_pos_outer_and_two_points haP hbP hcP hdP heP hnt habc
      hab hbc hca had hbd hcd hae hbe hce hde
  · have hbac_pos : 0 < lineSide b a c := by rw [lineSide_swap_left]; linarith
    exact hasConvexFourGon_of_pos_outer_and_two_points hbP haP hcP hdP heP hnt hbac_pos
      hab.symm hca.symm hbc.symm hbd had hcd hbe hae hce hde

#print axioms hasConvexFourGon_of_five_distinct_nonTrilinear

/-- Extraction of 5 pairwise distinct points from any `pts : Finset ℝ²` with `pts.card = 5`. -/
theorem exists_five_distinct_of_card_eq_five {pts : Finset ℝ²} (hcard : pts.card = 5) :
    ∃ a b c d e : ℝ²,
      a ∈ pts ∧ b ∈ pts ∧ c ∈ pts ∧ d ∈ pts ∧ e ∈ pts ∧
      a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e := by
  obtain ⟨e, s₄, he_s₄, rfl, hs₄⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨d, s₃, hd_s₃, rfl, hs₃⟩ := Finset.card_eq_succ.mp hs₄
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs₃
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he_s₄ hd_s₃
  refine ⟨a, b, c, d, e, by simp, by simp, by simp, by simp, by simp,
    hab, hbc, hac.symm,
    Ne.symm hd_s₃.1, Ne.symm hd_s₃.2.1, Ne.symm hd_s₃.2.2,
    Ne.symm he_s₄.2.1, Ne.symm he_s₄.2.2.1, Ne.symm he_s₄.2.2.2, Ne.symm he_s₄.1⟩

#print axioms exists_five_distinct_of_card_eq_five

/-- **Unconditional 5-Point Happy Ending Membership Theorem (`5 ∈ cardSet 4`)**:
Every 5-point `NonTrilinear` set in $\mathbb{R}^2$ contains a convex 4-gon. -/
theorem five_mem_cardSet_four : (5 : ℕ) ∈ cardSet 4 := by
  intro pts hcard hnt
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he,
    hab, hbc, hca, had, hbd, hcd, hae, hbe, hce, hde⟩ :=
    exists_five_distinct_of_card_eq_five hcard
  exact hasConvexFourGon_of_five_distinct_nonTrilinear
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hc)
    (Finset.mem_coe.mpr hd) (Finset.mem_coe.mpr he)
    hnt hab hbc hca had hbd hcd hae hbe hce hde

#print axioms five_mem_cardSet_four

/-- **Unconditional Resolution of the 5-Point Happy Ending Value $f(4) = 5$**:
$f(4) = 5$ and $f(4) = \operatorname{erdosSzekeresConjectured}(4) = 2^{4-2} + 1$. -/
theorem f_four_eq_five : f 4 = 5 ∧ f 4 = erdosSzekeresConjectured 4 :=
  f_four_eq_five_of_mem_cardSet five_mem_cardSet_four

#print axioms f_four_eq_five

/-- Direct equation $f(4) = 5$. -/
theorem f_four_eq_five_unconditional : f 4 = 5 :=
  f_four_eq_five.1

#print axioms f_four_eq_five_unconditional

/-! ## Section 3: Universal 3-Cap/3-Cup Obstructions and the 8-Point Pentagon-Free Certificate (`8 ∉ cardSet 5`, `9 ≤ f 5`) -/

/-- **Universal 3-Cap Plus Upper-Point Interior Containment Lemma**:
If $(a, b, c)$ is a 3-cap turn ($\operatorname{lineSide}(a,b,c) < 0$) and $u$ lies on the positive open side
of both $a \to b$ and $b \to c$, then the middle cap vertex $b$ lies strictly inside $\triangle acu$. -/
theorem inPosTriangle_of_three_cap_and_above {a b c u : ℝ²}
    (hcap : lineSide a b c < 0) (habu : 0 < lineSide a b u) (hbcu : 0 < lineSide b c u) :
    InPosTriangle a c u b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lineSide_swap_right]; linarith
  · have h : lineSide c u b = lineSide b c u := by dsimp [lineSide]; ring
    linarith
  · have h : lineSide u a b = lineSide a b u := by dsimp [lineSide]; ring
    linarith

#print axioms inPosTriangle_of_three_cap_and_above

/-- **Universal 3-Cap Plus Upper-Point Non-Convexity Theorem**:
Any set $S \subseteq \mathbb{R}^2$ containing a 3-cap $(a, b, c)$ and a point $u$ above both secants
$a \to b$ and $b \to c$ fails to be `ConvexIndep`. -/
theorem not_convexIndep_of_three_cap_and_above {S : Set ℝ²} {a b c u : ℝ²}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (huS : u ∈ S)
    (hcap : lineSide a b c < 0) (habu : 0 < lineSide a b u) (hbcu : 0 < lineSide b c u) :
    ¬ ConvexIndep S :=
  not_convexIndep_of_inPosTriangle haS hcS huS hbS
    (inPosTriangle_of_three_cap_and_above hcap habu hbcu)

#print axioms not_convexIndep_of_three_cap_and_above

/-- **Universal 3-Cup Plus Lower-Point Interior Containment Lemma**:
If $(u, v, w)$ is a 3-cup turn ($0 < \operatorname{lineSide}(u,v,w)$) and $a$ lies on the negative open side
of both $u \to v$ and $v \to w$, then the middle cup vertex $v$ lies strictly inside $\triangle uaw$. -/
theorem inPosTriangle_of_three_cup_and_below {u v w a : ℝ²}
    (hcup : 0 < lineSide u v w) (huva : lineSide u v a < 0) (hvwa : lineSide v w a < 0) :
    InPosTriangle u a w v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lineSide_swap_right]; linarith
  · have h : lineSide a w v = - lineSide v w a := by dsimp [lineSide]; ring
    linarith
  · have h : lineSide w u v = lineSide u v w := by dsimp [lineSide]; ring
    linarith

#print axioms inPosTriangle_of_three_cup_and_below

/-- **Universal 3-Cup Plus Lower-Point Non-Convexity Theorem**:
Any set $S \subseteq \mathbb{R}^2$ containing a 3-cup $(u, v, w)$ and a point $a$ below both secants
$u \to v$ and $v \to w$ fails to be `ConvexIndep`. -/
theorem not_convexIndep_of_three_cup_and_below {S : Set ℝ²} {u v w a : ℝ²}
    (huS : u ∈ S) (hvS : v ∈ S) (hwS : w ∈ S) (haS : a ∈ S)
    (hcup : 0 < lineSide u v w) (huva : lineSide u v a < 0) (hvwa : lineSide v w a < 0) :
    ¬ ConvexIndep S :=
  not_convexIndep_of_inPosTriangle huS haS hwS hvS
    (inPosTriangle_of_three_cup_and_below hcup huva hvwa)

#print axioms not_convexIndep_of_three_cup_and_below

/-- Any finite set $J$ of size at least 3 contains three pairwise distinct elements. -/
theorem exists_three_distinct_of_three_le_card {α : Type*} [DecidableEq α] {J : Finset α}
    (hcard : 3 ≤ J.card) :
    ∃ x y z : α, x ∈ J ∧ y ∈ J ∧ z ∈ J ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  obtain ⟨x, hxJ⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
  have hcard1 : 2 ≤ (J.erase x).card := by
    rw [Finset.card_erase_of_mem hxJ]; omega
  obtain ⟨y, hyJ1⟩ := Finset.card_pos.mp (by omega : 0 < (J.erase x).card)
  have hcard2 : 1 ≤ ((J.erase x).erase y).card := by
    rw [Finset.card_erase_of_mem hyJ1]; omega
  obtain ⟨z, hzJ2⟩ := Finset.card_pos.mp (by omega : 0 < ((J.erase x).erase y).card)
  obtain ⟨hyx, hyJ⟩ := Finset.mem_erase.mp hyJ1
  obtain ⟨hzy, hzJ1⟩ := Finset.mem_erase.mp hzJ2
  obtain ⟨hzx, hzJ⟩ := Finset.mem_erase.mp hzJ1
  exact ⟨x, y, z, hxJ, hyJ, hzJ, hyx.symm, hzy.symm, hzx.symm⟩

#print axioms exists_three_distinct_of_three_le_card

/-- Any finite set $J$ in a linear order with $3 \le |J|$ contains a strictly increasing triple $a < b < c$. -/
theorem exists_strict_ordered_triple_of_three_le_card {α : Type*} [LinearOrder α] {J : Finset α}
    (hcard : 3 ≤ J.card) :
    ∃ a b c : α, a ∈ J ∧ b ∈ J ∧ c ∈ J ∧ a < b ∧ b < c := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hxz⟩ := exists_three_distinct_of_three_le_card hcard
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
  rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
  rcases lt_or_gt_of_ne hxz with h3 | h3
  · exact ⟨x, y, z, hx, hy, hz, h1, h2⟩
  · exfalso; exact lt_asymm (lt_trans h1 h2) h3
  · exact ⟨x, z, y, hx, hz, hy, h3, h2⟩
  · exact ⟨z, x, y, hz, hx, hy, h3, h1⟩
  · exact ⟨y, x, z, hy, hx, hz, h1, h3⟩
  · exact ⟨y, z, x, hy, hz, hx, h2, h3⟩
  · exfalso; exact lt_asymm h3 (lt_trans h2 h1)
  · exact ⟨z, y, x, hz, hy, hx, h2, h1⟩

#print axioms exists_strict_ordered_triple_of_three_le_card

/-- $x$-coordinates of the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup pentagon-free witness. -/
def esEightX : Fin 8 → ℤ := ![0, 1, 2, 3, 20, 21, 22, 23]

/-- $y$-coordinates of the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup pentagon-free witness. -/
def esEightY : Fin 8 → ℤ := ![0, 3, 5, 6, 100, 97, 95, 94]

/-- The 8-point Erdős–Szekeres point map `Fin 8 → ℝ²`. -/
def esEightPt (i : Fin 8) : ℝ² :=
  mkPt (esEightX i : ℝ) (esEightY i : ℝ)

/-- The 8-point Erdős–Szekeres finite point set in $\mathbb{R}^2$. -/
def esEightFinset : Finset ℝ² :=
  Finset.univ.image esEightPt

/-- Exact integer oriented-area determinant for triples in `esEightPt`. -/
def esEightCross (i j k : Fin 8) : ℤ :=
  (esEightX j - esEightX i) * (esEightY k - esEightY i) -
  (esEightY j - esEightY i) * (esEightX k - esEightX i)

/-- `lineSide` on `esEightPt` equals the cast of `esEightCross`. -/
theorem lineSide_esEightPt (i j k : Fin 8) :
    lineSide (esEightPt i) (esEightPt j) (esEightPt k) = (esEightCross i j k : ℝ) := by
  dsimp [lineSide, esEightPt, esEightCross]
  simp only [mkPt_zero, mkPt_one]
  push_cast
  ring

#print axioms lineSide_esEightPt

theorem esEightX_ne_of_ne : ∀ i j : Fin 8, i ≠ j → esEightX i ≠ esEightX j := by
  decide

#print axioms esEightX_ne_of_ne

/-- `esEightPt` is injective on `Fin 8`. -/
theorem esEightPt_injective : Function.Injective esEightPt := by
  intro i j hij
  by_contra hne
  have hx := congrArg (fun p : ℝ² => p 0) hij
  simp only [esEightPt, mkPt_zero, Int.cast_inj] at hx
  exact esEightX_ne_of_ne i j hne hx

#print axioms esEightPt_injective

/-- `esEightFinset` has cardinality 8. -/
theorem esEightFinset_card : esEightFinset.card = 8 := by
  dsimp [esEightFinset]
  rw [Finset.card_image_of_injective _ esEightPt_injective, Finset.card_univ, Fintype.card_fin]

#print axioms esEightFinset_card

/-- No three distinct indices in `Fin 8` have zero oriented area in `esEightPt`. -/
theorem esEightCross_ne_zero_of_distinct :
    ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k → esEightCross i j k ≠ 0 := by
  decide

#print axioms esEightCross_ne_zero_of_distinct

/-- `esEightFinset` is in general position (`NonTrilinear`). -/
theorem esEightFinset_nonTrilinear : NonTrilinear (esEightFinset : Set ℝ²) := by
  intro a ha b hb c hc hab hbc hac
  rw [esEightFinset, Finset.coe_image] at ha hb hc
  rcases ha with ⟨i, _, rfl⟩
  rcases hb with ⟨j, _, rfl⟩
  rcases hc with ⟨k, _, rfl⟩
  have hij : i ≠ j := fun h => hab (congrArg esEightPt h)
  have hjk : j ≠ k := fun h => hbc (congrArg esEightPt h)
  have hik : i ≠ k := fun h => hac (congrArg esEightPt h)
  intro hcoll
  have hzero := cross_eq_zero_of_collinear hcoll
  have hls : lineSide (esEightPt i) (esEightPt j) (esEightPt k) = 0 := by
    dsimp [lineSide]; linarith
  rw [lineSide_esEightPt, Int.cast_eq_zero] at hls
  exact esEightCross_ne_zero_of_distinct i j k hij hjk hik hls

#print axioms esEightFinset_nonTrilinear

/-- Every ordered triple $i < j < k < 4$ in the 4-cap and every index $u \ge 4$ in the 4-cup place
$j$ strictly inside the positively oriented triangle $(i, k, u)$. -/
theorem esEight_cap_triple_with_cup_pt :
    ∀ i j k u : Fin 8,
      i < j → j < k → k.val < 4 → 4 ≤ u.val →
      0 < esEightCross i k j ∧ 0 < esEightCross k u j ∧ 0 < esEightCross u i j := by
  decide

#print axioms esEight_cap_triple_with_cup_pt

/-- Every ordered triple $4 \le u < v < w$ in the 4-cup and every index $i < 4$ in the 4-cap place
$v$ strictly inside the positively oriented triangle $(u, i, w)$. -/
theorem esEight_cup_triple_with_cap_pt :
    ∀ u v w i : Fin 8,
      u < v → v < w → 4 ≤ u.val → i.val < 4 →
      0 < esEightCross u i v ∧ 0 < esEightCross i w v ∧ 0 < esEightCross w u v := by
  decide

#print axioms esEight_cup_triple_with_cap_pt

/-- Pigeonhole partition of any 5-element subset $I \subseteq \operatorname{Fin} 8$ across the 4-cap
$\{0, 1, 2, 3\}$ and 4-cup $\{4, 5, 6, 7\}$: either at least 3 elements lie in the 4-cap and at least 1
in the 4-cup, or at least 3 elements lie in the 4-cup and at least 1 in the 4-cap. -/
theorem fin8_cap_cup_split {I : Finset (Fin 8)} (hcard : I.card = 5) :
    let I₁ := I.filter (fun i : Fin 8 => i.val < 4)
    let I₂ := I \ I₁
    (3 ≤ I₁.card ∧ 1 ≤ I₂.card) ∨ (3 ≤ I₂.card ∧ 1 ≤ I₁.card) := by
  intro I₁ I₂
  have hsum : I₂.card + I₁.card = I.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ I)
  have hsub₁ : I₁ ⊆ Finset.univ.filter (fun i : Fin 8 => i.val < 4) :=
    Finset.filter_subset_filter _ (Finset.subset_univ I)
  have hsub₂ : I₂ ⊆ Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    have hi4 : ¬ i.val < 4 := fun h => hi.2 ⟨hi.1, h⟩
    exact ⟨Finset.mem_univ i, by omega⟩
  have hle₁ : I₁.card ≤ (Finset.univ.filter (fun i : Fin 8 => i.val < 4)).card :=
    Finset.card_le_card hsub₁
  have hle₂ : I₂.card ≤ (Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val)).card :=
    Finset.card_le_card hsub₂
  have hc₁ : (Finset.univ.filter (fun i : Fin 8 => i.val < 4)).card = 4 := by decide
  have hc₂ : (Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val)).card = 4 := by decide
  omega

#print axioms fin8_cap_cup_split

/-- **8-Point Pentagon-Free Certificate (`not_hasConvexFiveGon_esEightFinset`)**:
The 8-point general-position set `esEightFinset` contains no convex pentagon. -/
theorem not_hasConvexFiveGon_esEightFinset :
    ¬ HasConvexNGon 5 (esEightFinset : Set ℝ²) := by
  rintro ⟨S, hScard, hSsub, hSconv⟩
  have hSsub' : S ⊆ Finset.univ.image esEightPt := Finset.coe_subset.mp hSsub
  obtain ⟨I, _, rfl⟩ := Finset.subset_image_iff.mp hSsub'
  have hIcard : I.card = 5 := by
    rwa [Finset.card_image_of_injective _ esEightPt_injective] at hScard
  rcases fin8_cap_cup_split hIcard with ⟨hI₁, hI₂⟩ | ⟨hI₂, hI₁⟩
  · obtain ⟨i, j, k, hi, hj, hk, hij, hjk⟩ := exists_strict_ordered_triple_of_three_le_card hI₁
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (I \ I.filter (fun i : Fin 8 => i.val < 4)).card)
    obtain ⟨hiI, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjI, _⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkI, hk4⟩ := Finset.mem_filter.mp hk
    rw [Finset.mem_sdiff, Finset.mem_filter] at hu
    have hu4 : ¬ u.val < 4 := fun h => hu.2 ⟨hu.1, h⟩
    have hcr := esEight_cap_triple_with_cup_pt i j k u hij hjk hk4 (by omega)
    have htri : InPosTriangle (esEightPt i) (esEightPt k) (esEightPt u) (esEightPt j) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.2
    exact not_convexIndep_of_inPosTriangle
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hiI))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hkI))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu.1))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hjI))
      htri hSconv
  · obtain ⟨u, v, w, hu, hv, hw, huv, hvw⟩ := exists_strict_ordered_triple_of_three_le_card hI₂
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (I.filter (fun i : Fin 8 => i.val < 4)).card)
    rw [Finset.mem_sdiff, Finset.mem_filter] at hu hv hw
    have hu4 : ¬ u.val < 4 := fun h => hu.2 ⟨hu.1, h⟩
    obtain ⟨hiI, hi4⟩ := Finset.mem_filter.mp hi
    have hcr := esEight_cup_triple_with_cap_pt u v w i huv hvw (by omega) hi4
    have htri : InPosTriangle (esEightPt u) (esEightPt i) (esEightPt w) (esEightPt v) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.2
    exact not_convexIndep_of_inPosTriangle
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu.1))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hiI))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw.1))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv.1))
      htri hSconv

#print axioms not_hasConvexFiveGon_esEightFinset

/-- **Unconditional Non-Membership `8 ∉ cardSet 5`**:
Not every 8-point general-position set in $\mathbb{R}^2$ contains a convex pentagon. -/
theorem eight_not_mem_cardSet_five : (8 : ℕ) ∉ cardSet 5 := by
  intro h8
  exact not_hasConvexFiveGon_esEightFinset
    (h8 esEightFinset esEightFinset_card esEightFinset_nonTrilinear)

#print axioms eight_not_mem_cardSet_five

/-- Any $N \in \operatorname{cardSet}(5)$ satisfies $9 \le N$. -/
theorem nine_le_of_mem_cardSet_five {N : ℕ} (hN : N ∈ cardSet 5) : 9 ≤ N := by
  by_contra hlt
  have hle : N ≤ 8 := by omega
  exact eight_not_mem_cardSet_five (cardSet_upward_closed hle hN)

#print axioms nine_le_of_mem_cardSet_five

/-- **Unconditional Lower Bound $9 \le f(5)$**:
$f(5) \ge 2^{5-2} + 1 = 9$. -/
theorem nine_le_f_five : 9 ≤ f 5 :=
  le_csInf (nonempty_cardSet_all 5) (fun _ hN => nine_le_of_mem_cardSet_five hN)

#print axioms nine_le_f_five

/-- **Unconditional Bounds $9 \le f(5) \le 21$**:
Combines the 8-point pentagon-free lower bound $9 \le f(5)$ with the Erdős–Szekeres upper bound $f(5) \le 21$. -/
theorem f_five_bounds_unconditional : 9 ≤ f 5 ∧ f 5 ≤ 21 :=
  ⟨nine_le_f_five, f_five_upper_unconditional⟩

#print axioms f_five_bounds_unconditional

/-- Upgraded conditional completion theorem for $f(5) = 9$: since $8 \notin \operatorname{cardSet}(5)$
is now proved unconditionally, $f(5) = 9$ follows from $9 \in \operatorname{cardSet}(5)$ alone. -/
theorem f_five_eq_nine_of_nine_mem (h9 : (9 : ℕ) ∈ cardSet 5) :
    f 5 = 9 ∧ f 5 = erdosSzekeresConjectured 5 :=
  f_five_eq_nine_of_eight_not_mem_and_nine_mem eight_not_mem_cardSet_five h9

#print axioms f_five_eq_nine_of_nine_mem

/-! ## Section 4: Complete Erdős–Szekeres Bounds for $3 \le n \le 5$ and Top-Down Conditional Reductions -/

/-- **Exact Erdős–Szekeres Conjecture for $3 \le n \le 4$**:
For $n = 3$ and $n = 4$, $f(n) = 2^{n-2} + 1$ holds unconditionally. -/
theorem f_eq_conjectured_of_le_four {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) :
    f n = 2 ^ (n - 2) + 1 := by
  have hcases : n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl
  · simpa using f_three_eq
  · simpa using f_four_eq_five_unconditional

#print axioms f_eq_conjectured_of_le_four

/-- **Unconditional Erdős–Szekeres Lower Bound $2^{n-2} + 1 \le f(n)$ for $3 \le n \le 5$**:
Unifies $3 \le f(3)$, $5 \le f(4)$, and $9 \le f(5)$. -/
theorem conjectured_lower_bound_of_le_five {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    2 ^ (n - 2) + 1 ≤ f n := by
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [f_three_eq]; decide
  · rw [f_four_eq_five_unconditional]; decide
  · simpa using nine_le_f_five

#print axioms conjectured_lower_bound_of_le_five

/-- **Unconditional Resolution of `ersz_bounds` (`FormalConjectures/ErdosProblems/107.lean`) for $3 \le n \le 5$**:
For all $3 \le n \le 5$, $2^{n-2} + 1 \le f(n) \le \binom{2n-4}{n-2} + 1$. -/
theorem ersz_bounds_of_le_five {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 :=
  ⟨conjectured_lower_bound_of_le_five hn3 hn5,
   f_le_erdosSzekeresUpper (by omega : 2 ≤ n)⟩

#print axioms ersz_bounds_of_le_five

/-- **Top-Down Conditional Reduction 1 for `erdos_107`**:
Since $f(3) = 3$ and $f(4) = 5$ are proved unconditionally (`f_eq_conjectured_of_le_four`),
the full Erdős–Szekeres conjecture $\forall n \ge 3,\, f(n) = 2^{n-2} + 1$ reduces to $n \ge 5$. -/
theorem erdos_107_of_ge_five
    (hge5 : ∀ n ≥ 5, f n = 2 ^ (n - 2) + 1) :
    ∀ n ≥ 3, f n = 2 ^ (n - 2) + 1 := by
  intro n hn3
  by_cases hn4 : n ≤ 4
  · exact f_eq_conjectured_of_le_four hn3 hn4
  · exact hge5 n (by omega)

#print axioms erdos_107_of_ge_five

/-- **Top-Down Conditional Reduction 2 for `erdos_107`**:
Using `conjectured_lower_bound_of_le_five` ($2^{n-2} + 1 \le f(n)$ for $3 \le n \le 5$) and
`f_eq_conjectured_of_le_four` ($f(n) = 2^{n-2} + 1$ for $3 \le n \le 4$), the full Erdős–Szekeres
conjecture reduces to the lower bound $2^{n-2} + 1 \le f(n)$ for $n \ge 6$ together with upper-bound
membership $2^{n-2} + 1 \in \operatorname{cardSet}(n)$ for $n \ge 5$. -/
theorem erdos_107_of_lower_ge_six_and_upper_ge_five
    (hlower : ∀ n ≥ 6, 2 ^ (n - 2) + 1 ≤ f n)
    (hupper : ∀ n ≥ 5, 2 ^ (n - 2) + 1 ∈ cardSet n) :
    ∀ n ≥ 3, f n = 2 ^ (n - 2) + 1 := by
  apply erdos_107_of_ge_five
  intro n hn5
  have hle : f n ≤ 2 ^ (n - 2) + 1 := Nat.sInf_le (hupper n hn5)
  have hge : 2 ^ (n - 2) + 1 ≤ f n := by
    by_cases hn5_eq : n ≤ 5
    · exact conjectured_lower_bound_of_le_five (by omega) hn5_eq
    · exact hlower n (by omega)
  exact le_antisymm hle hge

#print axioms erdos_107_of_lower_ge_six_and_upper_ge_five

#print axioms nonempty_cardSet

end Erdos107
