module

public import SparseCut546
public import SparseCombination546


@[expose] public section

/-!
# Rounded sparse subsets of bounded-degree-copy-free graphs

Combines the bounded-degree sparse-cut contrapositive (`boundedDegree_sparse_cut`)
with the hereditary two-cleaning depth induction (`sparse_subset_density_of_hereditary_cuts`)
to extract a low-density subset inside any $G$-free host reservoir.
-/

namespace Erdos546

open Finset
open scoped Classical BigOperators

variable {V W : Type*} [Fintype V]

/-- Inclusion of a finite vertex set into its ambient vertex type. -/
def finsetInclusion (S : Finset W) : (S : Set W) ↪ W :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Mapping a cut out of an induced graph preserves its exact edge count. -/
theorem card_induced_interedges_map (H : SimpleGraph W) (S : Finset W)
    (X Y : Finset (S : Set W)) :
    (H.interedges (X.map (finsetInclusion S)) (Y.map (finsetInclusion S))).card =
      ((H.induce (S : Set W)).interedges X Y).card := by
  classical
  symm
  apply Finset.card_bij (fun e _ => (e.1.val, e.2.val))
  · intro e he
    obtain ⟨hx, hy, hadj⟩ := (SimpleGraph.mem_interedges_iff (H.induce (S : Set W))).mp he
    exact (SimpleGraph.mem_interedges_iff H).mpr
      ⟨Finset.mem_map.mpr ⟨e.1, hx, rfl⟩,
        Finset.mem_map.mpr ⟨e.2, hy, rfl⟩, hadj⟩
  · intro e he f hf heq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst heq)
    · exact Subtype.ext (congrArg Prod.snd heq)
  · intro e he
    obtain ⟨hx, hy, hadj⟩ := (SimpleGraph.mem_interedges_iff H).mp he
    obtain ⟨x, hxX, hxe⟩ := Finset.mem_map.mp hx
    obtain ⟨y, hyY, hye⟩ := Finset.mem_map.mp hy
    change x.val = e.1 at hxe
    change y.val = e.2 at hye
    refine ⟨(x, y), (SimpleGraph.mem_interedges_iff (H.induce (S : Set W))).mpr
      ⟨hxX, hyY, ?_⟩, ?_⟩
    · change H.Adj x.val y.val
      simpa only [hxe, hye] using hadj
    · exact Prod.ext hxe hye

theorem inverse_cut_size (c p a x r : ℝ) (hc : 0 < c)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hinverse : c ≤ p * r)
    (hsize : p * a / c ≤ x) : a ≤ r * x := by
  have hs := (div_le_iff₀ hc).mp hsize
  have hsr := mul_le_mul_of_nonneg_left hs hr
  have hi := mul_le_mul_of_nonneg_right hinverse ha
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith only [hsr, hi]

/-- A graph-free host has hereditary sparse cuts with an integer inverse
retained fraction `r`, down to sets of cardinality `r*q`. -/
theorem hereditary_cuts_of_no_copy (G : SimpleGraph V) (H : SimpleGraph W)
    (Δ r q : ℕ) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hinverse : 2 * (Δ + 1 : ℝ) ≤ (ε / 8)^Δ * r)
    (hq : Fintype.card V ≤ q) (hfree : ¬ Nonempty (SimpleGraph.Copy G H)) :
    ∀ T : Finset W, r * q ≤ T.card →
      ∃ X Y : Finset W, X ⊆ T ∧ Y ⊆ T ∧ Disjoint X Y ∧
        T.card ≤ r * X.card ∧ T.card ≤ r * Y.card ∧
        ((H.interedges X Y).card : ℝ) ≤ (ε / 2) / 4 * X.card * Y.card := by
  classical
  intro T hTsize
  have hp : 0 ≤ (ε / 8)^Δ := by positivity
  have hTn : r * Fintype.card V ≤ T.card :=
    (Nat.mul_le_mul_left r hq).trans hTsize
  have hTnreal : (r : ℝ) * Fintype.card V ≤ T.card := by exact_mod_cast hTn
  have hlarge : 2 * (Δ + 1 : ℝ) * Fintype.card V ≤ (ε / 8)^Δ * T.card := by
    have hi := mul_le_mul_of_nonneg_right hinverse
      (show (0 : ℝ) ≤ Fintype.card V by positivity)
    have ht := mul_le_mul_of_nonneg_left hTnreal hp
    nlinarith only [hi, ht]
  have hTfree : ¬ Nonempty (SimpleGraph.Copy G (H.induce (T : Set W))) := by
    rintro ⟨c⟩
    exact hfree ⟨(SimpleGraph.Copy.induce H (T : Set W)).comp c⟩
  obtain ⟨X, Y, hXY, hXYcard, hXlarge, hYlarge, hcross⟩ :=
    boundedDegree_sparse_cut G (H.induce (T : Set W)) Δ (ε / 8)
      (by positivity) (by linarith) hdegree (by simpa using hlarge) hTfree
  let X' := X.map (finsetInclusion T)
  let Y' := Y.map (finsetInclusion T)
  have hXsub : X' ⊆ T := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    exact z.property
  have hYsub : Y' ⊆ T := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    exact z.property
  have hden : 0 < 2 * (Δ + 1 : ℝ) := by positivity
  have hXsize : (T.card : ℝ) ≤ (r : ℝ) * X.card :=
    inverse_cut_size _ _ _ _ _ hden (by positivity) (by positivity)
      hinverse (by simpa using hXlarge)
  have hYsize : (T.card : ℝ) ≤ (r : ℝ) * Y.card :=
    inverse_cut_size _ _ _ _ _ hden (by positivity) (by positivity)
      hinverse (by simpa using hYlarge)
  refine ⟨X', Y', hXsub, hYsub, ?_, ?_, ?_, ?_⟩
  · exact (Finset.disjoint_map (finsetInclusion T)).mpr hXY
  · simpa [X'] using (show T.card ≤ r * X.card by exact_mod_cast hXsize)
  · simpa [Y'] using (show T.card ≤ r * Y.card by exact_mod_cast hYsize)
  · dsimp only [X', Y']
    rw [card_induced_interedges_map]
    simp only [Finset.card_map, show (ε / 2) / 4 = ε / 8 by ring]
    convert hcross using 1
    congr 1

/-- Rounded Corollary 2.6 with explicit integer inverse cut fraction and depth.
The returned density uses oriented internal edges divided by `|U|²`.
The host may be any prescribed finite reservoir `S` in a graph-free ambient
graph. Isolated target vertices are permitted; a positive target size is
required so that floor rounding retains at least one leaf vertex. -/
theorem sparse_subset_of_no_boundedDegree_copy (G : SimpleGraph V)
    (H : SimpleGraph W) (Δ r h : ℕ) (ε : ℝ) (hr : 1 ≤ r)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hn : 0 < Fintype.card V)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hinverse : 2 * (Δ + 1 : ℝ) ≤ (ε / 8)^Δ * r)
    (hdepth : 1 / (2^h : ℝ) ≤ ε / 2)
    (hfree : ¬ Nonempty (SimpleGraph.Copy G H))
    (S : Finset W) (hsize : (2 * r)^h * Fintype.card V ≤ S.card) :
    ∃ U : Finset W, U ⊆ S ∧
      (S.card : ℝ) / (2 * (r : ℝ)^h) ≤ U.card ∧
      ((H.interedges U U).card : ℝ) ≤ ε * (U.card : ℝ)^2 := by
  classical
  let T : ℕ := (2 * r)^h
  let q : ℕ := S.card / T
  have hTpos : 0 < T := pow_pos (by omega) h
  have hqn : Fintype.card V ≤ q := by
    apply (Nat.le_div_iff_mul_le hTpos).mpr
    simpa [T, Nat.mul_comm] using hsize
  have hqpos : 0 < q := lt_of_lt_of_le hn hqn
  have hstart : (2 * r)^h * q ≤ S.card := by
    simpa [q, T, Nat.mul_comm] using Nat.div_mul_le_self S.card T
  obtain ⟨U, hUsub, hUcard, hdensity⟩ := sparse_subset_density_of_hereditary_cuts
    H r q h (ε / 2) hr hqpos (by positivity)
    (hereditary_cuts_of_no_copy G H Δ r q ε hε hεone hdegree hinverse hqn hfree)
    S hstart
  have hNround : S.card ≤ 2 * T * q := by
    have hdecomp : q * T + S.card % T = S.card := by
      simpa [q, Nat.mul_comm] using Nat.div_add_mod S.card T
    have hmod : S.card % T < T := Nat.mod_lt S.card hTpos
    have hTq : T ≤ T * q := by
      simpa using Nat.mul_le_mul_left T (Nat.succ_le_of_lt hqpos)
    nlinarith
  have hUlower : (S.card : ℝ) / (2 * (r : ℝ)^h) ≤ U.card := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    apply (div_le_iff₀ (by positivity : 0 < 2 * (r : ℝ)^h)).mpr
    have hround : (S.card : ℝ) ≤ 2 * (T : ℝ) * q := by exact_mod_cast hNround
    rw [hUcard]
    dsimp only [T] at hround
    push_cast at hround ⊢
    rw [mul_pow] at hround
    nlinarith only [hround]
  have hUpos : (0 : ℝ) < U.card := by
    rw [hUcard]
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) h) hqpos
  have hcount : ((H.interedges U U).card : ℝ) ≤
      (ε / 2 + 1 / (2^h : ℝ)) * (U.card : ℝ)^2 := by
    rw [SimpleGraph.edgeDensity_def] at hdensity
    push_cast at hdensity
    have hc := (div_le_iff₀ (mul_pos hUpos hUpos)).mp hdensity
    simpa only [pow_two] using hc
  refine ⟨U, hUsub, hUlower, ?_⟩
  have hmult := mul_le_mul_of_nonneg_right hdepth (sq_nonneg (U.card : ℝ))
  nlinarith only [hcount, hmult]

end Erdos546
