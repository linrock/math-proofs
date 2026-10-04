module

public import AmplificationDegrees546
public import AmplificationGraph546
public import QuantitativeAmplificationParameters546


@[expose] public section

/-!
# One-color quantitative amplification

Combines the residual degree bound (`residual_degree_data_of_monoPair`),
the quantitative parameter schedule (`quantitative_amplification_parameters546`),
and the graph-free reservoir extraction (`monochromatic_pair_in_free_reservoir`)
to prove Sudakov's single-step monochromatic-pair amplification theorem.
-/

namespace Erdos546

open SimpleGraph Finset

/-- Quantitative monochromatic-pair amplification step (Sudakov Section 3): for
$m \ge 64$, $|E(G)| = m$, $|V| \le 2m$, and scale
$3 \le a \le \lfloor \frac{1}{2}\log_2 m \rfloor$, a monochromatic pair
$(X, Y)$ in a $G$-free host $H$ with $|X| \ge a^3\sqrt{m}$ and
$|Y| \ge 2^{500\sqrt{m}/a}$ yields a monochromatic pair $(P, Q)$ inside $Y$
(in $H$ or $H^c$) with $|P| \ge 2^{2a}\sqrt{m}$ and
$|Q| \ge |Y| \cdot 2^{-400\sqrt{m}/a}$. -/
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

end Erdos546
