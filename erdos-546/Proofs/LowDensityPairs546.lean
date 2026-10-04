module

public import MonochromaticPairs546
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset


@[expose] public section

/-!
# The finite mask argument in Sudakov's small-density pair lemma

The statements below formalize the combinatorial core of Lemma 2.3 of
Benny Sudakov, *A conjecture of Erdős on graph Ramsey numbers*, arXiv:1002.0095.
Every red-neighbor mask is extended to an `r`-element subset of a blue clique.
Pigeonhole then gives a reservoir with common blue neighbors. If the original
blue clique has maximum cardinality, the reservoir has no blue clique larger
than `r`, so the binomial pair recurrence must return the red outcome.
-/

namespace Erdos546

open Finset

variable {V : Type*} [DecidableEq V]

/-- A clique of maximum cardinality among all cliques inside `s`. -/
def MaximumClique (H : SimpleGraph V) (B s : Finset V) : Prop :=
  B ⊆ s ∧ H.IsClique (B : Set V) ∧
    ∀ Q : Finset V, Q ⊆ s → H.IsClique (Q : Set V) → Q.card ≤ B.card

theorem exists_maximumClique (H : SimpleGraph V) (s : Finset V) :
    ∃ B, MaximumClique H B s := by
  classical
  let cliques := s.powerset.filter (fun B : Finset V => H.IsClique (B : Set V))
  have hnonempty : cliques.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [cliques, SimpleGraph.IsClique]
  obtain ⟨B, hB, hmax⟩ := cliques.exists_max_image Finset.card hnonempty
  rcases mem_filter.mp hB with ⟨hBs, hBc⟩
  refine ⟨B, mem_powerset.mp hBs, hBc, ?_⟩
  intro Q hQs hQc
  exact hmax Q (mem_filter.mpr ⟨mem_powerset.mpr hQs, hQc⟩)

theorem monoPair_union_isClique {H : SimpleGraph V} {X Y : Finset V}
    (hp : MonoPair H X Y) (hY : H.IsClique (Y : Set V)) :
    H.IsClique ((X ∪ Y : Finset V) : Set V) := by
  rcases hp with ⟨hd, hX, hXY⟩
  intro a ha b hb hab
  rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
  · exact hX ha hb hab
  · exact hXY a ha b hb
  · exact (hXY b hb a ha).symm
  · exact hY ha hb hab

/-- A common red-neighbor mask leaves a blue monochromatic pair. -/
theorem monoPair_compl_of_mask {H : SimpleGraph V} {B R F : Finset V}
    (hB : Hᶜ.IsClique (B : Set V)) (hd : Disjoint B F)
    (hm : ∀ v ∈ F, ∀ b ∈ B, H.Adj v b → b ∈ R) :
    MonoPair Hᶜ (B \ R) F := by
  refine ⟨hd.mono Finset.sdiff_subset Subset.rfl, ?_, ?_⟩
  · exact hB.subset (by simp)
  · intro b hb v hv
    rcases mem_sdiff.mp hb with ⟨hb, hbR⟩
    rw [SimpleGraph.compl_adj]
    refine ⟨?_, ?_⟩
    · intro heq
      subst v
      exact Finset.disjoint_left.mp hd hb hv
    · intro hred
      exact hbR (hm v hv b hb hred.symm)

/-- Extend all red-neighbor masks to `r`-element subsets of `B`, then pigeonhole.
The multiplicative threshold is exactly the number of possible extended masks. -/
theorem exists_mask_monoPair (H : SimpleGraph V) [DecidableRel H.Adj]
    (B S : Finset V) (r q : ℕ)
    (hB : Hᶜ.IsClique (B : Set V)) (hd : Disjoint B S) (hr : r ≤ B.card)
    (hm : ∀ v ∈ S, (B.filter (H.Adj v)).card ≤ r)
    (hq : B.card.choose r * q ≤ S.card) :
    ∃ R F, R ⊆ B ∧ R.card = r ∧ F ⊆ S ∧ q ≤ F.card ∧
      MonoPair Hᶜ (B \ R) F := by
  classical
  have hcover : ∀ v ∈ S, ∃ R : Finset V,
      B.filter (H.Adj v) ⊆ R ∧ R ⊆ B ∧ R.card = r := by
    intro v hv
    exact exists_subsuperset_card_eq (filter_subset _ _) (hm v hv) hr
  let f : V → Finset V := fun v =>
    if hv : v ∈ S then Classical.choose (hcover v hv) else ∅
  have hf : ∀ v ∈ S, f v ∈ B.powersetCard r := by
    intro v hv
    simpa [f, hv] using mem_powersetCard.mpr (Classical.choose_spec (hcover v hv)).2
  obtain ⟨R, hR, hF⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := f) hf (powersetCard_nonempty.mpr hr)
    (by simpa only [card_powersetCard] using hq)
  let F := S.filter (fun v => f v = R)
  rcases mem_powersetCard.mp hR with ⟨hRB, hRcard⟩
  refine ⟨R, F, hRB, hRcard, filter_subset _ _, hF, ?_⟩
  apply monoPair_compl_of_mask hB (hd.mono Subset.rfl (filter_subset _ _))
  intro v hv b hb he
  rcases mem_filter.mp hv with ⟨hvS, hvf⟩
  have hmask := (Classical.choose_spec (hcover v hvS)).1
  have hfv : f v = Classical.choose (hcover v hvS) := by
    simp [f, hvS]
  rw [← hfv, hvf] at hmask
  exact hmask (mem_filter.mpr ⟨hb, he⟩)

/-- The large-blue-clique branch of the same mask argument. -/
theorem exists_blue_monoPair_of_clique_masks
    (H : SimpleGraph V) [DecidableRel H.Adj] (B S : Finset V) (r t q : ℕ)
    (hB : Hᶜ.IsClique (B : Set V)) (hd : Disjoint B S)
    (hr : r ≤ B.card) (ht : t + r ≤ B.card)
    (hm : ∀ v ∈ S, (B.filter (H.Adj v)).card ≤ r)
    (hsize : B.card.choose r * q ≤ S.card) :
    ∃ X Y, X ⊆ B ∧ Y ⊆ S ∧ MonoPair Hᶜ X Y ∧ X.card = t ∧ q ≤ Y.card := by
  obtain ⟨R, F, hRB, hRcard, hFS, hFcard, hp⟩ :=
    exists_mask_monoPair H B S r q hB hd hr hm hsize
  have hremain : t ≤ (B \ R).card := by
    rw [card_sdiff_of_subset hRB, hRcard]
    omega
  obtain ⟨X, hXR, hXcard⟩ := exists_subset_card_eq hremain
  exact ⟨X, F, hXR.trans Finset.sdiff_subset, hFS,
    monoPair_mono hp hXR Subset.rfl, hXcard, hFcard⟩

/-- Maximum cardinality, rather than inclusion maximality, bounds the blue
clique size in every common-mask reservoir. -/
theorem clique_card_le_mask_of_maximum {H : SimpleGraph V} {B U R F Q : Finset V}
    (hmax : MaximumClique H B U) (hRB : R ⊆ B) (hFU : F ⊆ U)
    (hp : MonoPair H (B \ R) F) (hQF : Q ⊆ F)
    (hQ : H.IsClique (Q : Set V)) : Q.card ≤ R.card := by
  have hpQ := monoPair_mono hp Subset.rfl hQF
  have hclique := monoPair_union_isClique hpQ hQ
  have hsub : (B \ R) ∪ Q ⊆ U :=
    union_subset (Finset.sdiff_subset.trans hmax.1) (hQF.trans hFU)
  have hc := hmax.2.2 ((B \ R) ∪ Q) hsub hclique
  rw [card_union_of_disjoint hpQ.1, card_sdiff_of_subset hRB] at hc
  have hcard : R.card ≤ B.card := card_le_card hRB
  omega

/-- The second half of the small-density argument, with no analytic estimates:
if a maximum blue clique has masks of size at most `r`, the pair recurrence
on one mask fiber cannot return a blue clique of size `l > r`. -/
theorem exists_red_monoPair_of_maximum_complClique_masks
    (H : SimpleGraph V) [DecidableRel H.Adj] (B U S : Finset V) (r t l q : ℕ)
    (hmax : MaximumClique Hᶜ B U) (hSU : S ⊆ U) (hd : Disjoint B S)
    (hr : r ≤ B.card) (hrl : r < l)
    (hm : ∀ v ∈ S, (B.filter (H.Adj v)).card ≤ r)
    (hsize : B.card.choose r * ((t + l).choose t * (q + 1)) ≤ S.card) :
    ∃ X Y, X ⊆ S ∧ Y ⊆ S ∧ MonoPair H X Y ∧ X.card = t ∧ q ≤ Y.card := by
  classical
  obtain ⟨R, F, hRB, hRcard, hFS, hFcard, hp⟩ :=
    exists_mask_monoPair H B S r ((t + l).choose t * (q + 1))
      hmax.2.1 hd hr hm hsize
  rcases exists_monoPair H t l q F hFcard with hred | hblue
  · rcases hred with ⟨X, Y, hXF, hYF, hpair, hXcard, hYcard⟩
    exact ⟨X, Y, hXF.trans hFS, hYF.trans hFS, hpair, hXcard, hYcard⟩
  · rcases hblue with ⟨X, Y, hXF, hYF, hpair, hXcard, hYcard⟩
    have hbound := clique_card_le_mask_of_maximum hmax hRB (hFS.trans hSU)
      hp hXF hpair.2.1
    rw [hXcard, hRcard] at hbound
    omega

end Erdos546
