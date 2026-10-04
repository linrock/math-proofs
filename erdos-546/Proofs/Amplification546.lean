module

public import AmplificationDegrees546
public import AmplificationGraph546
public import QuantitativeAmplificationParameters546


@[expose] public section

/-!
# One-color quantitative amplification

The deleted graph has its actual finite maximum degree. The quantitative
parameters are supplied by arithmetic proofs from the original edge count,
and the graph-free reservoir theorem then constructs the larger pair.
This is an auxiliary step toward the uniform Ramsey theorem.
-/

namespace Erdos546

open SimpleGraph Finset

/-- A monochromatic clique/reservoir pair in a graph-free host amplifies
its clique side; the resulting pair may use either color. -/
theorem quantitative_monoPair_amplification {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (m a : ℕ) (hm : 64 ≤ m) (hedges : G.edgeSet.ncard = m)
    (hvertices : Fintype.card V ≤ 2 * m)
    (ha : 3 ≤ a) (haA : a ≤ finalAmplificationParameter546 m)
    {X Y : Finset W} (hp : MonoPair H X Y)
    (hfree : ¬ G.IsContained H)
    (hX : (a : ℝ) ^ 3 * Real.sqrt m ≤ X.card)
    (hY : Real.rpow 2 (500 * Real.sqrt m / a) ≤ Y.card) :
    ∃ P Q : Finset W, P ⊆ Y ∧ Q ⊆ Y ∧
      (MonoPair H P Q ∨ MonoPair Hᶜ P Q) ∧
      (2 : ℝ) ^ (2 * a) * Real.sqrt m ≤ P.card ∧
      (Y.card : ℝ) * Real.rpow 2 (-400 * Real.sqrt m / a) ≤ Q.card := by
  classical
  obtain ⟨A, D, _, hn, hdegree, hD, hresidual_free⟩ :=
    residual_degree_data_of_monoPair G H m a (by omega) hedges hp hfree hX
  have hnupper : Fintype.card ↥((A : Set V)ᶜ) ≤ 2 * m :=
    (Fintype.card_subtype_le _).trans hvertices
  obtain ⟨ε, r, h, t, u, hr, hε, hεsmall, hinverse, hdepth,
    hextract, hεt, hu, hu1, hpair, ht, hretained⟩ :=
    quantitative_amplification_parameters546 m a D
      (Fintype.card ↥((A : Set V)ᶜ)) Y.card hm ha haA hD hnupper hY
  obtain ⟨P, Q, hPY, hQY, hmono, hPcard, hQlower⟩ :=
    monochromatic_pair_in_free_reservoir (G.induce ((A : Set V)ᶜ))
      H Y D r h t u ε hr hε hεsmall hn hdegree hinverse hdepth
      hresidual_free hextract hεt hu hu1 hpair
  refine ⟨P, Q, hPY, hQY, hmono, ?_, hretained.trans hQlower⟩
  simpa only [hPcard] using ht

#print axioms quantitative_monoPair_amplification

end Erdos546
