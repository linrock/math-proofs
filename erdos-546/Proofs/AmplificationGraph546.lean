module

public import FreeGraphSparse546
public import LowDensityRounded546
public import PairLifting546


@[expose] public section

/-! Constructive graph part of amplification: a graph-free finite reservoir
gives a monochromatic pair through sparse extraction and the low-density
lemma. The exact natural-size and exponent hypotheses remain explicit;
their derivation from the original edge count is a separate obligation. -/

namespace Erdos546

open SimpleGraph Finset

theorem monochromatic_pair_in_free_reservoir {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (Y : Finset W) (D r h t u : ℕ) (ε : ℝ)
    (hr : 1 ≤ r) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8)
    (hn : 0 < Fintype.card V) (hdegree : ∀ v, G.degree v ≤ D)
    (hinverse : 2 * (D + 1 : ℝ) ≤ (ε / 8)^D * r)
    (hdepth : 1 / (2^h : ℝ) ≤ ε / 2)
    (hfree : ¬ G.IsContained (H.induce (Y : Set W)))
    (hextract : (2 * r)^h * Fintype.card V ≤ Y.card)
    (hεt : 1 ≤ ε * t) (hu : ε * t ≤ u) (hu1 : 1 ≤ u)
    (hpair : (t : ℝ) ≤ ε^(20 * u) * ((Y.card : ℝ) / (2 * (r : ℝ)^h))) :
    ∃ P Q : Finset W, P ⊆ Y ∧ Q ⊆ Y ∧
      (MonoPair H P Q ∨ MonoPair Hᶜ P Q) ∧ P.card = t ∧
      ε^(20 * u) * ((Y.card : ℝ) / (2 * (r : ℝ)^h)) ≤ Q.card := by
  classical
  obtain ⟨U, _, hUlower, hUdensity⟩ := sparse_subset_of_no_boundedDegree_copy
    G (H.induce (Y : Set W)) D r h ε hr hε (by linarith) hn
    (by
      intro v
      have hv := hdegree v
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv ⊢
      exact hv)
    hinverse hdepth hfree univ (by simpa using hextract)
  have hUlower' : (Y.card : ℝ) / (2 * (r : ℝ)^h) ≤ U.card := by
    simpa using hUlower
  have hsize : (t : ℝ) ≤ ε^(20 * u) * U.card :=
    hpair.trans (mul_le_mul_of_nonneg_left hUlower' (pow_nonneg hε.le _))
  have hdensity : (redDegreeSum (H.induce (Y : Set W)) U : ℝ) ≤
      ε * U.card ^ 2 := by
    rw [redDegreeSum_eq_card_interedges]
    exact hUdensity
  obtain ⟨P, Q, _, _, hp, hPcard, hQlower⟩ :=
    exists_monoPair_of_low_density_integer_power (H.induce (Y : Set W)) U ε t u
      hε hεsmall hεt hu hu1 hsize hdensity
  refine ⟨ambientFinset (Y : Set W) P, ambientFinset (Y : Set W) Q,
    ambientFinset_subset_coe Y P, ambientFinset_subset_coe Y Q, ?_, ?_, ?_⟩
  · rcases hp with hp | hp
    · exact Or.inl (monoPair_induce_lift H (Y : Set W) P Q hp)
    · exact Or.inr (monoPair_induce_compl_lift H (Y : Set W) P Q hp)
  · simpa only [ambientFinset_card] using hPcard
  · rw [ambientFinset_card]
    exact (mul_le_mul_of_nonneg_left hUlower' (pow_nonneg hε.le _)).trans hQlower

#print axioms monochromatic_pair_in_free_reservoir

end Erdos546
