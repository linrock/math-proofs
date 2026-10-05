module

public import GoldbachCircleBase

@[expose] public section

set_option maxHeartbeats 4000000

namespace GoldbachChain
namespace MajorArcMainTerm
open Finset MinorArc
/-- **Euler product for the singular series** (from `Tarith_summable`): `𝔖(n) = ∑'_q T(q) =
    ∏'_p (1 + T(p))`. Combined with `one_add_Tarith_pos` (each factor `> 0` for even `n`) this is
    the route to `𝔖(n) ≥ c₀ > 0`. -/
lemma singSeries_eq_prod (n : ℕ) (hn : 1 ≤ n) :
    (∑' q, Tarith n q) = ∏' p : Nat.Primes, (1 + Tarith n (p : ℕ)) := by
  rw [← (isMult_Tarith n).eulerProduct_tprod (Tarith_summable n hn)]
  refine tprod_congr (fun p => ?_)
  exact Tarith_local (p : ℕ) n p.2

/-- `∏_{i∈s}(1-a_i) ≥ 1 - ∑_{i∈s} a_i` for `a_i ∈ [0,1]` (Weierstrass product inequality). -/
lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j t hj IH =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have haj0 : 0 ≤ a j := ha j (Finset.mem_insert_self j t)
    have hIH : 1 - ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 - a i) :=
      IH (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hsum0 : 0 ≤ ∑ i ∈ t, a i :=
      Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have h1 : (1 - a j) * (1 - ∑ i ∈ t, a i) ≤ (1 - a j) * ∏ i ∈ t, (1 - a i) :=
      mul_le_mul_of_nonneg_left hIH (by linarith [ha1 j (Finset.mem_insert_self j t)])
    nlinarith [h1, haj0, hsum0, mul_nonneg haj0 hsum0]

/-- Per-prime lower bound: for even `n` and prime `p`, `1 + T(p) ≥ 1 - 1/(p-1)²`. (Equality at
    `p∤n`; at `p∣n` the LHS is `≥ 1`.) -/
lemma one_add_Tarith_ge (p n : ℕ) (hp : p.Prime) (hn : Even n) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + Tarith n p := by
  rw [Tarith_prime p n hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  by_cases hd : p ∣ n
  · rw [if_pos hd]
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by positivity
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · rw [if_neg hd]
    have hrw : (-1 : ℝ) / ((p : ℝ) - 1) ^ 2 = -(1 / ((p : ℝ) - 1) ^ 2) := by ring
    rw [hrw]; linarith

/-- Telescoping: `∑_{k=2}^{M} (1/(k-1) - 1/k) = 1 - 1/M`. -/
lemma telescope_sum (M : ℕ) (hM : 2 ≤ M) :
    ∑ k ∈ Finset.Icc 2 M, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num [Finset.Icc_self, Finset.sum_singleton]
  | succ M hM IH =>
    rw [Finset.sum_Icc_succ_top (by omega), IH]
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    rw [show ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 by push_cast; ring,
      show ((M : ℝ) + 1) - 1 = (M : ℝ) by ring]
    field_simp
    ring

/-- `∑_{k∈T} 1/k² < 1` for any finite `T ⊆ {k : 2 ≤ k}` (Basel partial-sum bound, elementary:
    `1/k² ≤ 1/(k-1)-1/k`, telescope over `Icc 2 (max T)`). -/
lemma sum_inv_sq_lt_one (T : Finset ℕ) (hT : ∀ k ∈ T, 2 ≤ k) :
    ∑ k ∈ T, 1 / ((k : ℝ)) ^ 2 < 1 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  set M := T.max' hne with hMdef
  have hM2 : 2 ≤ M := hT _ (T.max'_mem hne)
  have hsub : T ⊆ Finset.Icc 2 M := by
    intro k hk
    rw [Finset.mem_Icc]
    exact ⟨hT k hk, T.le_max' k hk⟩
  have hterm : ∀ k ∈ T, 1 / ((k : ℝ)) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
    intro k hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hT k hk
    rw [div_sub_div _ _ (by linarith) (by linarith),
      div_le_div_iff₀ (by nlinarith [hkR]) (by nlinarith [hkR])]
    ring_nf
    nlinarith [hkR]
  calc ∑ k ∈ T, 1 / ((k : ℝ)) ^ 2
      ≤ ∑ k ∈ T, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := Finset.sum_le_sum hterm
    _ ≤ ∑ k ∈ Finset.Icc 2 M, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro k hk _
        rw [Finset.mem_Icc] at hk
        have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        apply div_nonneg <;> nlinarith [hkR]
    _ = 1 - 1 / (M : ℝ) := telescope_sum M hM2
    _ < 1 := by
        have hMpos : (0 : ℝ) < (M : ℝ) := by
          have : 0 < M := by omega
          exact_mod_cast this
        have : (0 : ℝ) < 1 / (M : ℝ) := by positivity
        linarith

/-- Uniform Basel partial bound: `∑_{k=2}^M 1/k² ≤ 3/4 - 1/M` (invariant induction, using
    `1/(M+1)² ≤ 1/(M(M+1)) = 1/M - 1/(M+1)`). -/
lemma sum_inv_sq_Icc_le (M : ℕ) (hM : 2 ≤ M) :
    ∑ k ∈ Finset.Icc 2 M, 1 / ((k : ℝ)) ^ 2 ≤ 3 / 4 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num [Finset.Icc_self, Finset.sum_singleton]
  | succ M hM IH =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    have hkey : 1 / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
      rw [hcast, div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      nlinarith [hM0]
    rw [hcast] at hkey ⊢
    linarith [IH, hkey]

/-- `∑_{k∈T} 1/k² ≤ 3/4` **uniformly**, for any finite `T ⊆ {k : 2 ≤ k}`. (The uniform bound
    the partial Euler product needs — the earlier `<1` bound isn't uniform in `T`.) -/
lemma sum_inv_sq_le34 (T : Finset ℕ) (hT : ∀ k ∈ T, 2 ≤ k) :
    ∑ k ∈ T, 1 / ((k : ℝ)) ^ 2 ≤ 3 / 4 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · norm_num
  set M := T.max' hne with hMdef
  have hM2 : 2 ≤ M := hT _ (T.max'_mem hne)
  have hsub : T ⊆ Finset.Icc 2 M := fun k hk => Finset.mem_Icc.mpr ⟨hT k hk, T.le_max' k hk⟩
  calc ∑ k ∈ T, 1 / ((k : ℝ)) ^ 2
      ≤ ∑ k ∈ Finset.Icc 2 M, 1 / ((k : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro k _ _; positivity
    _ ≤ 3 / 4 - 1 / (M : ℝ) := sum_inv_sq_Icc_le M hM2
    _ ≤ 3 / 4 := by
        have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        have hp : (0 : ℝ) < 1 / (M : ℝ) := by positivity
        linarith

/-- **Uniform partial Euler product bound**: for even `n`, every finite partial product
    `∏_{p∈S}(1+T(p)) ≥ 1/4`. Uses `a_p = [p≠2]·1/(p-1)²`: then `1+T(p) ≥ 1-a_p`, `∏(1-a) ≥ 1-∑a`
    (`prod_one_sub_ge`), and `∑ a_p ≤ 3/4` (`sum_inv_sq_le34` on the `p≠2` part). -/
lemma partial_prod_ge (n : ℕ) (hn : Even n) (S : Finset Nat.Primes) :
    (1 : ℝ) / 4 ≤ ∏ p ∈ S, (1 + Tarith n (↑p : ℕ)) := by
  classical
  set a : Nat.Primes → ℝ := fun p => if (↑p : ℕ) = 2 then 0 else 1 / ((↑p : ℝ) - 1) ^ 2 with ha
  have hfac : ∀ p ∈ S, 1 - a p ≤ 1 + Tarith n (↑p : ℕ) := by
    intro p _
    have hp2 : (2 : ℝ) ≤ (↑p : ℝ) := by exact_mod_cast p.2.two_le
    by_cases h2 : (↑p : ℕ) = 2
    · simp only [ha, if_pos h2]
      have hval : Tarith n (↑p : ℕ) = 1 := by
        rw [Tarith_prime _ n p.2, if_pos (h2 ▸ (even_iff_two_dvd.mp hn))]
        rw [h2]; norm_num
      rw [hval]; norm_num
    · simp only [ha, if_neg h2]
      exact one_add_Tarith_ge (↑p) n p.2 hn
  have ha01 : ∀ p ∈ S, 0 ≤ a p ∧ a p ≤ 1 := by
    intro p _
    have hp3 : (2 : ℝ) ≤ (↑p : ℝ) := by exact_mod_cast p.2.two_le
    by_cases h2 : (↑p : ℕ) = 2
    · simp only [ha, if_pos h2]; norm_num
    · simp only [ha, if_neg h2]
      have hp3' : (3 : ℝ) ≤ (↑p : ℝ) := by
        rcases (p.2.eq_two_or_odd').symm with hodd | h2'
        · rcases lt_or_eq_of_le p.2.two_le with h | h
          · exact_mod_cast h
          · exact absurd h.symm h2
        · exact absurd h2' h2
      constructor
      · positivity
      · rw [div_le_one (by nlinarith [hp3'])]; nlinarith [hp3']
  have hfac0 : ∀ p ∈ S, 0 ≤ 1 - a p := fun p hp => by linarith [(ha01 p hp).2]
  have hstep1 : ∏ p ∈ S, (1 - a p) ≤ ∏ p ∈ S, (1 + Tarith n (↑p : ℕ)) :=
    Finset.prod_le_prod₀ (fun p hp => hfac0 p hp) hfac
  have hstep2 : 1 - ∑ p ∈ S, a p ≤ ∏ p ∈ S, (1 - a p) :=
    prod_one_sub_ge S a (fun p hp => (ha01 p hp).1) (fun p hp => (ha01 p hp).2)
  have hsum : ∑ p ∈ S, a p ≤ 3 / 4 := by
    have hg : ∀ p ∈ S,
        a p = (if 2 ≤ (↑p : ℕ) - 1 then 1 / (((↑p : ℕ) - 1 : ℕ) : ℝ) ^ 2 else 0) := by
      intro p _
      have hp2 : 2 ≤ (↑p : ℕ) := p.2.two_le
      simp only [ha]
      by_cases h2 : (↑p : ℕ) = 2
      · rw [if_pos h2, if_neg (by omega)]
      · rw [if_neg h2, if_pos (by omega)]
        congr 1
        rw [Nat.cast_sub p.2.one_le]; norm_num
    have himg : (∑ p ∈ S,
          (if 2 ≤ (↑p : ℕ) - 1 then 1 / (((↑p : ℕ) - 1 : ℕ) : ℝ) ^ 2 else 0))
        = ∑ k ∈ S.image (fun p : Nat.Primes => (↑p : ℕ) - 1),
            (if 2 ≤ k then 1 / ((k : ℝ)) ^ 2 else 0) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      have hx2 : 1 ≤ (↑x : ℕ) := x.2.one_le
      have hy2 : 1 ≤ (↑y : ℕ) := y.2.one_le
      have hxy' : (↑x : ℕ) - 1 = (↑y : ℕ) - 1 := hxy
      exact Subtype.ext (by omega)
    rw [Finset.sum_congr rfl hg, himg, ← Finset.sum_filter]
    apply sum_inv_sq_le34
    intro k hk
    rw [Finset.mem_filter] at hk
    exact hk.2
  linarith [hstep1, hstep2, hsum]

/-- **Singular-series positivity** (conditional on `Tarith_summable`): `𝔖(n) = ∑'_q T(q) ≥ 1/4`
    for every even `n`. Passes the uniform partial-product bound `partial_prod_ge` through the
    `HasProd` limit (`eulerProduct_hasProd` + `Tarith_local`). This `c₀ = 1/4` is the constant
    `hmain` consumes: `𝔖(n)·r_N(n) ≥ (1/4)·(X/2)`. -/
lemma singSeries_ge (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) : (1 : ℝ) / 4 ≤ ∑' q, Tarith n q := by
  have hprod : HasProd (fun p : Nat.Primes => 1 + Tarith n (↑p : ℕ)) (∑' q, Tarith n q) := by
    have h := (isMult_Tarith n).eulerProduct_hasProd (Tarith_summable n hn1)
    have heq : (fun p : Nat.Primes => ∑' e, Tarith n ((↑p : ℕ) ^ e))
        = (fun p : Nat.Primes => 1 + Tarith n (↑p : ℕ)) := by
      funext p; exact Tarith_local (↑p) n p.2
    rwa [heq] at h
  exact ge_of_tendsto hprod (Filter.Eventually.of_forall (fun S => partial_prod_ge n hn S))

/-- The **Hardy–Littlewood main term** `m_X(n) = 𝔖(n)·r_{X+1}(n)` (singular series × kernel count). -/
noncomputable def mainTerm (X n : ℕ) : ℝ :=
  (∑' q, Tarith n q)
    * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun p => p.1 + p.2 = n)).card : ℝ)

/-- **`hmain` discharged** (conditional on `Tarith_summable`): with `δ X = (X+1)/16`, the main
    term dominates `δ X` on the upper block for even `n`. Combines `singSeries_ge` (`𝔖≥1/4`) and
    `kernel_real_lb` (`r_{X+1}(n)≥X/2`): `m_X(n) ≥ (1/4)(X/2) = X/8 ≥ (X+1)/16` for `X≥1`. -/
lemma hmain_bound :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X → Even n →
      ((X : ℝ) + 1) / 16 ≤ mainTerm X n := by
  refine ⟨1, fun X hX n hn1 hn2 hne => ?_⟩
  rw [mainTerm]
  have hS : (1 : ℝ) / 4 ≤ ∑' q, Tarith n q := singSeries_ge n (by omega) hne
  have hK : (X : ℝ) / 2 ≤ (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
      (fun p => p.1 + p.2 = n)).card : ℝ) := kernel_real_lb X n hn1 hn2
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hprod : (1 / 4) * ((X : ℝ) / 2)
      ≤ (∑' q, Tarith n q) * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p => p.1 + p.2 = n)).card : ℝ) :=
    mul_le_mul hS hK (by positivity) (by linarith)
  have hcmp : ((X : ℝ) + 1) / 16 ≤ (1 / 4) * ((X : ℝ) / 2) := by nlinarith [hXR]
  linarith [hprod, hcmp]

/-- **`hvar` reduction (abstract triangle inequality)**: the reduction's weighted variance
    `∑(repW − mterm)² ≤ εXδ²` follows from the two L²-in-`n` bounds — the core variance
    `∑(repW − cmodelRe)² ≤ εX³` (banked `core_variance_repWeight`) and the **major-arc L² error**
    `∑(cmodelRe − mterm)² ≤ εX³` (the one remaining analytic gap) — plus `δX² ≥ (X²)/256`.
    Isolates the arc error as the sole missing input. -/
lemma hvar_of_arc_error
    (repW cmodelRe mterm : ℕ → ℕ → ℝ)
    (hcore : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (repW X n - cmodelRe X n) ^ 2 ≤ ε * (X : ℝ) ^ 3)
    (harc : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (cmodelRe X n - mterm X n) ^ 2 ≤ ε * (X : ℝ) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (repW X n - mterm X n) ^ 2
        ≤ ε * (X : ℝ) * (((X : ℝ) + 1) / 16) ^ 2 := by
  intro ε hε
  obtain ⟨X₁, hX₁⟩ := hcore (ε / 1024) (by positivity)
  obtain ⟨X₂, hX₂⟩ := harc (ε / 1024) (by positivity)
  refine ⟨max 1 (max X₁ X₂), fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hX1X : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX2X : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hpt : ∀ n ∈ Finset.Ioc (X / 2) X, (repW X n - mterm X n) ^ 2
      ≤ 2 * (repW X n - cmodelRe X n) ^ 2 + 2 * (cmodelRe X n - mterm X n) ^ 2 := by
    intro n _; nlinarith [sq_nonneg (repW X n - cmodelRe X n - (cmodelRe X n - mterm X n))]
  calc ∑ n ∈ Finset.Ioc (X / 2) X, (repW X n - mterm X n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          (2 * (repW X n - cmodelRe X n) ^ 2 + 2 * (cmodelRe X n - mterm X n) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * (∑ n ∈ Finset.Ioc (X / 2) X, (repW X n - cmodelRe X n) ^ 2)
          + 2 * (∑ n ∈ Finset.Ioc (X / 2) X, (cmodelRe X n - mterm X n) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (ε / 1024 * (X : ℝ) ^ 3) + 2 * (ε / 1024 * (X : ℝ) ^ 3) := by
        have h1 := hX₁ X hX1X
        have h2 := hX₂ X hX2X
        linarith
    _ ≤ ε * (X : ℝ) * (((X : ℝ) + 1) / 16) ^ 2 := by
        have hkey : (X : ℝ) ^ 3 ≤ (X : ℝ) * ((X : ℝ) + 1) ^ 2 := by nlinarith [hXR]
        have hrhs : ε * (X : ℝ) * (((X : ℝ) + 1) / 16) ^ 2
            = ε / 256 * ((X : ℝ) * ((X : ℝ) + 1) ^ 2) := by ring
        have hlhs : 2 * (ε / 1024 * (X : ℝ) ^ 3) + 2 * (ε / 1024 * (X : ℝ) ^ 3)
            = ε / 256 * (X : ℝ) ^ 3 := by ring
        rw [hrhs, hlhs]
        exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **L² triangle split** for the major-arc error: `∑(f−h)² ≤ εX³` follows from the two L²-in-`n`
    bounds `∑(f−g)² ≤ εX³` and `∑(g−h)² ≤ εX³`. Isolates `harc` (with `f = Re coeffModel`,
    `g = 𝔖_P·r_N`, `h = 𝔖·r_N`) into the **arc-tail** error `f−g` and the **truncation** error
    `g−h` — the two deepest circle-method sub-pieces. -/
lemma l2_error_triangle (f g h : ℕ → ℕ → ℝ)
    (h1 : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (f X n - g X n) ^ 2 ≤ ε * (X : ℝ) ^ 3)
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (g X n - h X n) ^ 2 ≤ ε * (X : ℝ) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (f X n - h X n) ^ 2 ≤ ε * (X : ℝ) ^ 3 := by
  intro ε hε
  obtain ⟨X₁, hX₁⟩ := h1 (ε / 4) (by positivity)
  obtain ⟨X₂, hX₂⟩ := h2 (ε / 4) (by positivity)
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  have hX1X : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX2X : X₂ ≤ X := le_trans (le_max_right _ _) hX
  have hpt : ∀ n ∈ Finset.Ioc (X / 2) X, (f X n - h X n) ^ 2
      ≤ 2 * (f X n - g X n) ^ 2 + 2 * (g X n - h X n) ^ 2 := by
    intro n _; nlinarith [sq_nonneg (f X n - g X n - (g X n - h X n))]
  calc ∑ n ∈ Finset.Ioc (X / 2) X, (f X n - h X n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          (2 * (f X n - g X n) ^ 2 + 2 * (g X n - h X n) ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * (∑ n ∈ Finset.Ioc (X / 2) X, (f X n - g X n) ^ 2)
          + 2 * (∑ n ∈ Finset.Ioc (X / 2) X, (g X n - h X n) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (ε / 4 * (X : ℝ) ^ 3) + 2 * (ε / 4 * (X : ℝ) ^ 3) := by
        have := hX₁ X hX1X; have := hX₂ X hX2X; linarith
    _ = ε * (X : ℝ) ^ 3 := by ring

/-- The truncated singular series is the partial sum of the arithmetic function `T`:
    `𝔖_P(n) = ∑_{1≤q≤P} T(q)`. Bridges `singSeries` (the `hvar`-side truncation) to `Tarith`
    (whose tsum is `𝔖(n)`), so the truncation error `𝔖_P − 𝔖 = −∑_{q>P} T(q)` is a `Tarith` tail. -/
lemma singSeries_eq_sum_Tarith (P n : ℕ) :
    singSeries P n = ∑ q ∈ Finset.Icc 1 P, Tarith n q := by
  rw [singSeries]
  apply Finset.sum_congr rfl
  intro q _
  rw [Tarith_apply]


/-- **Finite geometric character sum**: `∑_{n<N} e(nθ) = N` if `e(θ)=1`, else `(e(Nθ)−1)/(e(θ)−1)`.
    The Dirichlet-kernel identity underlying finite character orthogonality — the seed of the
    Ramanujan-sum orthogonality `∑_{n<N} c_q(n)c_{q'}(n)` for `harc`'s truncation error. -/
lemma sum_e_geom (θ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, e ((n : ℝ) * θ)
      = if e θ = 1 then (N : ℂ) else (e ((N : ℝ) * θ) - 1) / (e θ - 1) := by
  have hsum : ∑ n ∈ Finset.range N, e ((n : ℝ) * θ) = ∑ n ∈ Finset.range N, (e θ) ^ n := by
    apply Finset.sum_congr rfl; intro n _; exact e_pow θ n
  rw [hsum]
  by_cases h : e θ = 1
  · rw [if_pos h]; simp [h]
  · rw [if_neg h, geom_sum_eq h, e_pow θ N]


/-- Trivial bound `‖∑_{n<N} e(nθ)‖ ≤ N`. -/
lemma sum_e_norm_le_card (θ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, e ((n : ℝ) * θ)‖ ≤ (N : ℝ) := by
  calc ‖∑ n ∈ Finset.range N, e ((n : ℝ) * θ)‖
      ≤ ∑ n ∈ Finset.range N, ‖e ((n : ℝ) * θ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro n _; exact e_norm _
    _ = (N : ℝ) := by simp

/-- Geometric bound `‖∑_{n<N} e(nθ)‖ ≤ 2/‖e(θ)−1‖` for `e(θ) ≠ 1` — the off-diagonal decay that
    powers Ramanujan-sum orthogonality (`harc` truncation error). -/
lemma sum_e_norm_le_geom (θ : ℝ) (N : ℕ) (h : e θ ≠ 1) :
    ‖∑ n ∈ Finset.range N, e ((n : ℝ) * θ)‖ ≤ 2 / ‖e θ - 1‖ := by
  rw [sum_e_geom θ N, if_neg h, norm_div]
  have hn : ‖e ((N : ℝ) * θ) - 1‖ ≤ 2 := by
    calc ‖e ((N : ℝ) * θ) - 1‖ ≤ ‖e ((N : ℝ) * θ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [e_norm]; norm_num
  gcongr


/-- `e θ · e(−θ) = 1`. -/
lemma e_mul_neg (θ : ℝ) : e θ * e (-θ) = 1 := by
  simp only [e, ← Complex.exp_add]
  rw [← Complex.exp_zero]
  congr 1
  push_cast
  ring

/-- **Trivial pointwise bound**: `‖c_q(n)‖ ≤ φ(q)` — the Ramanujan sum is `φ(q)` unit-modulus
    terms. The length-capped mean square `∑_{n<N}‖c_q‖² ≤ N·φ(q)²` (harc `q > X` diagonal) rests on
    this. -/
lemma ramSum_norm_le (q n : ℕ) : ‖ramSum q n‖ ≤ (Nat.totient q : ℝ) := by
  simp only [ramSum]
  calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((n : ℝ) * r / q)‖
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), ‖e ((n : ℝ) * r / q)‖ :=
        norm_sum_le _ _
    _ = ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).card := by simp [e_norm]
    _ = (Nat.totient q : ℝ) := by
        rw [Nat.totient]; congr 2; ext r; simp [Nat.Coprime, Nat.gcd_comm]

/-- **Ramanujan-sum full-period mean square (complex form)**: `∑_{n<q} c_q(n)·conj c_q(n) = q·φ(q)`.
    The diagonal of Ramanujan orthogonality — the L² engine of the harc truncation error: the
    character double-sum collapses via `char_orthogonality` to the diagonal `r = r'`, giving
    `q` per unit and `φ(q)` units. -/
lemma ramSum_mean_square_complex (q : ℕ) (hq : 0 < q) :
    ∑ n ∈ Finset.range q, ramSum q n * (starRingEnd ℂ) (ramSum q n)
      = (q : ℂ) * (Nat.totient q) := by
  set U := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hU
  have step1 : ∀ n ∈ Finset.range q,
      ramSum q n * (starRingEnd ℂ) (ramSum q n)
        = ∑ r ∈ U, ∑ r' ∈ U, e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) := by
    intro n _
    simp only [ramSum]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro r' _
    rw [e_conj, e_add]
    congr 1
    push_cast; ring
  have step2 : ∑ n ∈ Finset.range q, ∑ r ∈ U, ∑ r' ∈ U,
        e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q)
      = ∑ r ∈ U, ∑ r' ∈ U, (if (q : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) then (q : ℂ) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r' _
    exact char_orthogonality ((r : ℤ) - (r' : ℤ)) q hq.ne'
  have hdiag : ∀ r ∈ U,
      (∑ r' ∈ U, (if (q : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) then (q : ℂ) else 0)) = (q : ℂ) := by
    intro r hr
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' hr' hne
      rw [if_neg]
      intro hdvd
      have hrq : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hr'q : r' < q := Finset.mem_range.mp (Finset.mem_filter.mp hr').1
      have hri : (0 : ℤ) ≤ (r : ℤ) := by positivity
      have hr'i : (0 : ℤ) ≤ (r' : ℤ) := by positivity
      have hrqi : (r : ℤ) < q := by exact_mod_cast hrq
      have hr'qi : (r' : ℤ) < q := by exact_mod_cast hr'q
      obtain ⟨c, hc⟩ := hdvd
      rcases lt_trichotomy c 0 with h1 | h1 | h1
      · have hle : (r : ℤ) - (r' : ℤ) ≤ -(q : ℤ) := by
          rw [hc]
          nlinarith [mul_le_mul_of_nonneg_left (show c ≤ -1 by omega)
            (show (0 : ℤ) ≤ (q : ℤ) by positivity)]
        omega
      · apply hne
        have hz : (r' : ℤ) = (r : ℤ) := by rw [h1, mul_zero] at hc; omega
        exact_mod_cast hz
      · have hge : (q : ℤ) ≤ (r : ℤ) - (r' : ℤ) := by
          rw [hc]
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ c by omega)
            (show (0 : ℤ) ≤ (q : ℤ) by positivity)]
        omega
    · intro hnr; exact absurd hr hnr
  have hcard : U.card = Nat.totient q := by
    rw [hU, Nat.totient]
    apply Finset.card_nbij' id id <;> intro x hx <;>
      simp_all [Finset.mem_filter, Nat.Coprime, Nat.gcd_comm]
  rw [Finset.sum_congr rfl step1, step2, Finset.sum_congr rfl hdiag,
    Finset.sum_const, hcard, nsmul_eq_mul, mul_comm]

/-- **Ramanujan-sum full-period mean square (real form)**: `∑_{n<q} ‖c_q(n)‖² = q·φ(q)`. The
    L²-per-period identity feeding the harc truncation bound `∑_n(𝔖_P−𝔖)²r_N² ≲ X³/P²`. -/
lemma ramSum_mean_square (q : ℕ) (hq : 0 < q) :
    ∑ n ∈ Finset.range q, ‖ramSum q n‖ ^ 2 = (q : ℝ) * (Nat.totient q) := by
  have h := ramSum_mean_square_complex q hq
  have hterm : ∀ n, ramSum q n * (starRingEnd ℂ) (ramSum q n)
      = ((‖ramSum q n‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun n _ => hterm n), ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- **Ramanujan-sum off-diagonal orthogonality**: for `q ≠ q'`, `∑_{n<qq'} c_q(n)·conj c_{q'}(n) = 0`.
    Distinct moduli are orthogonal — coprimality (`gcd(r,q)=gcd(r',q')=1`) forces `qq'∤(rq'−r'q)`,
    so every character cross-term vanishes. This is what kills the `σ(n)²` loss: in the truncation
    L², `∑_n(∑_{q>P}T_q)²` has no surviving cross terms, collapsing to the diagonal mean squares. -/
lemma ramSum_orthogonal_offdiag (q q' : ℕ) (hq : 0 < q) (hq' : 0 < q') (hne : q ≠ q') :
    ∑ n ∈ Finset.range (q * q'), ramSum q n * (starRingEnd ℂ) (ramSum q' n) = 0 := by
  set Uq := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hUq
  set Uq' := (Finset.range q').filter (fun r => Nat.gcd r q' = 1) with hUq'
  have hmul : 0 < q * q' := Nat.mul_pos hq hq'
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hq'R : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne'
  have step1 : ∀ n ∈ Finset.range (q * q'),
      ramSum q n * (starRingEnd ℂ) (ramSum q' n)
        = ∑ r ∈ Uq, ∑ r' ∈ Uq',
            e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ)) := by
    intro n _
    simp only [ramSum]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro r' _
    rw [e_conj, e_add]
    congr 1
    push_cast
    field_simp
    ring
  have step2 : (∑ n ∈ Finset.range (q * q'), ∑ r ∈ Uq, ∑ r' ∈ Uq',
        e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ)))
      = ∑ r ∈ Uq, ∑ r' ∈ Uq',
          (if ((q * q' : ℕ) : ℤ) ∣ ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) then
            ((q * q' : ℕ) : ℂ) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r' _
    exact char_orthogonality ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) (q * q') hmul.ne'
  rw [Finset.sum_congr rfl step1, step2]
  apply Finset.sum_eq_zero; intro r hr
  apply Finset.sum_eq_zero; intro r' hr'
  rw [if_neg]
  intro hdvd
  have hrc : Nat.gcd r q = 1 := (Finset.mem_filter.mp hr).2
  have hr'c : Nat.gcd r' q' = 1 := (Finset.mem_filter.mp hr').2
  have hqdvd_prod : (q : ℤ) ∣ ((q * q' : ℕ) : ℤ) := ⟨(q' : ℤ), by push_cast; ring⟩
  have h1 : (q : ℤ) ∣ ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) := dvd_trans hqdvd_prod hdvd
  have h2 : (q : ℤ) ∣ (r : ℤ) * (q' : ℤ) := by
    have h3 := dvd_add h1 (dvd_mul_left (q : ℤ) (r' : ℤ))
    have he : (r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) + (r' : ℤ) * (q : ℤ) = (r : ℤ) * (q' : ℤ) := by
      ring
    rwa [he] at h3
  have hcopq : IsCoprime (q : ℤ) (r : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hrc
  have hqq' : (q : ℤ) ∣ (q' : ℤ) := hcopq.dvd_of_dvd_mul_left h2
  have hq'dvd_prod : (q' : ℤ) ∣ ((q * q' : ℕ) : ℤ) := ⟨(q : ℤ), by push_cast; ring⟩
  have h1' : (q' : ℤ) ∣ ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) := dvd_trans hq'dvd_prod hdvd
  have h2' : (q' : ℤ) ∣ (r' : ℤ) * (q : ℤ) := by
    have h3 := dvd_sub (dvd_mul_left (q' : ℤ) (r : ℤ)) h1'
    have he : (r : ℤ) * (q' : ℤ) - ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) = (r' : ℤ) * (q : ℤ) := by
      ring
    rwa [he] at h3
  have hcopq' : IsCoprime (q' : ℤ) (r' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hr'c
  have hq'q : (q' : ℤ) ∣ (q : ℤ) := hcopq'.dvd_of_dvd_mul_left h2'
  exact hne (Nat.dvd_antisymm (by exact_mod_cast hqq') (by exact_mod_cast hq'q))

/-- `e(m) = 1` for integer `m` (period-1 of the additive character). -/
lemma e_natCast_eq_one (m : ℕ) : e (m : ℝ) = 1 := by
  simp only [e]
  rw [show (2 * Real.pi * Complex.I * (m : ℝ)) = ((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- **Ramanujan sum is `q`-periodic in `n`**: `c_q(n+q) = c_q(n)`. Lets a mean square over any
    multiple of the period reduce to the one-period identity (`ramSum_mean_square`). -/
lemma ramSum_periodic (q n : ℕ) : ramSum q (n + q) = ramSum q n := by
  simp only [ramSum]
  apply Finset.sum_congr rfl
  intro r hr
  have hqn : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqn.ne'
  have hid : ((n + q : ℕ) : ℝ) * (r : ℝ) / q = (n : ℝ) * (r : ℝ) / q + (r : ℝ) := by
    rw [Nat.cast_add]; field_simp
  rw [hid, ← e_add, e_natCast_eq_one, mul_one]

/-- **Period divides**: `c_q(n + kq) = c_q(n)` for all `k` — iterated `ramSum_periodic`. -/
lemma ramSum_periodic_mul (q n k : ℕ) : ramSum q (n + k * q) = ramSum q n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : n + (k + 1) * q = (n + k * q) + q := by ring
    rw [h, ramSum_periodic, ih]

/-- **Sum over multiple periods**: for `q`-periodic `f`, `∑_{n<kq} f = k·∑_{n<q} f`. Splits
    `range (kq)` into `k` consecutive period blocks, each equal to the base sum. -/
lemma periodic_sum_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (q : ℕ)
    (hper : ∀ n, f (n + q) = f n) (k : ℕ) :
    ∑ n ∈ Finset.range (k * q), f n = k • ∑ n ∈ Finset.range q, f n := by
  have hperk : ∀ j i, f (i + j * q) = f i := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have h : i + (j + 1) * q = (i + j * q) + q := by ring
      rw [h, hper, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q = k * q + q by ring, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive f (Nat.zero_le (k * q)) (Nat.le_add_right (k * q) q),
      ← Finset.range_eq_Ico, ih, succ_nsmul]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm (k * q) i, hperk]

/-- **Multi-period mean square (diagonal over a common period)**: `∑_{n<kq} ‖c_q(n)‖² = kq·φ(q)`.
    Applies `periodic_sum_mul` to the `q`-periodic `‖c_q‖²` and the one-period identity. -/
lemma ramSum_mean_square_multi (q k : ℕ) (hq : 0 < q) :
    ∑ n ∈ Finset.range (k * q), ‖ramSum q n‖ ^ 2 = (k * q : ℝ) * (Nat.totient q) := by
  have hper : ∀ n, ‖ramSum q (n + q)‖ ^ 2 = ‖ramSum q n‖ ^ 2 := by
    intro n; rw [ramSum_periodic]
  rw [periodic_sum_mul (fun n => ‖ramSum q n‖ ^ 2) q hper k, ramSum_mean_square q hq,
    nsmul_eq_mul]
  push_cast; ring

/-- **Multi-period off-diagonal**: `∑_{n<k(qq')} c_q(n)·conj c_{q'}(n) = 0` for `q ≠ q'`. The
    product is `(qq')`-periodic (both factors' periods divide `qq'`), so `periodic_sum_mul`
    reduces to the one-period vanishing `ramSum_orthogonal_offdiag`. -/
lemma ramSum_orthogonal_offdiag_multi (q q' k : ℕ) (hq : 0 < q) (hq' : 0 < q') (hne : q ≠ q') :
    ∑ n ∈ Finset.range (k * (q * q')), ramSum q n * (starRingEnd ℂ) (ramSum q' n) = 0 := by
  have hper : ∀ n, ramSum q (n + q * q') * (starRingEnd ℂ) (ramSum q' (n + q * q'))
      = ramSum q n * (starRingEnd ℂ) (ramSum q' n) := by
    intro n
    have e1 : ramSum q (n + q * q') = ramSum q n := by
      rw [show n + q * q' = n + q' * q by ring]; exact ramSum_periodic_mul q n q'
    have e2 : ramSum q' (n + q * q') = ramSum q' n := ramSum_periodic_mul q' n q
    rw [e1, e2]
  rw [periodic_sum_mul (fun n => ramSum q n * (starRingEnd ℂ) (ramSum q' n)) (q * q') hper k,
    ramSum_orthogonal_offdiag q q' hq hq' hne, smul_zero]

/-- Ramanujan sum is real: `(c_q(n)).im = 0` (it equals the integer `cRam q n`). -/
lemma ramSum_im_zero (q n : ℕ) (hq : 0 < q) : (ramSum q n).im = 0 := by
  rw [ramSum_eq_cRam q n hq, Complex.intCast_im]

/-- **Real multi-period off-diagonal**: `∑_{n<k(qq')} (c_q(n)).re·(c_{q'}(n)).re = 0` for `q≠q'`.
    The real part of the complex vanishing (both sums real, so cross-terms drop). -/
lemma ramSum_re_orthogonal_offdiag_multi (q q' k : ℕ) (hq : 0 < q) (hq' : 0 < q') (hne : q ≠ q') :
    ∑ n ∈ Finset.range (k * (q * q')), (ramSum q n).re * (ramSum q' n).re = 0 := by
  have h := ramSum_orthogonal_offdiag_multi q q' k hq hq' hne
  have hre : ∀ n, ((ramSum q n) * (starRingEnd ℂ) (ramSum q' n)).re
      = (ramSum q n).re * (ramSum q' n).re := by
    intro n
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ramSum_im_zero q' n hq']
    ring
  have hsum : (∑ n ∈ Finset.range (k * (q * q')),
      (ramSum q n) * (starRingEnd ℂ) (ramSum q' n)).re = 0 := by rw [h]; simp
  rw [Complex.re_sum] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl; intro n _; exact (hre n).symm

/-- **Real multi-period diagonal**: `∑_{n<kq} (c_q(n)).re² = kq·φ(q)`. -/
lemma ramSum_re_sq_sum_multi (q k : ℕ) (hq : 0 < q) :
    ∑ n ∈ Finset.range (k * q), (ramSum q n).re ^ 2 = (k * q : ℝ) * (Nat.totient q) := by
  rw [← ramSum_mean_square_multi q k hq]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ramSum_im_zero q n hq]
  ring

/-- **Aggregate quadratic form over a common period** (Ramanujan-sum large sieve): with `M` a
    common multiple of every `q∈S` and every `qq'` (`q≠q'∈S`), the mean square of the character
    combination collapses to the diagonal:
    `∑_{n<M} (∑_{q∈S} a_q c_q(n))² = ∑_{q∈S} a_q²·M·φ(q)`.
    Off-diagonal cross-terms vanish by orthogonality; each diagonal contributes `M·φ(q)`. This is
    the engine that removes the `σ(n)²` loss in the harc truncation error. -/
lemma aggregate_meansq (S : Finset ℕ) (a : ℕ → ℝ) (M : ℕ)
    (hpos : ∀ q ∈ S, 0 < q)
    (hdvd : ∀ q ∈ S, q ∣ M)
    (hdvd2 : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → (q * q') ∣ M) :
    ∑ n ∈ Finset.range M, (∑ q ∈ S, a q * (ramSum q n).re) ^ 2
      = ∑ q ∈ S, (a q) ^ 2 * (M : ℝ) * (Nat.totient q) := by
  have hexp : ∀ n ∈ Finset.range M, (∑ q ∈ S, a q * (ramSum q n).re) ^ 2
      = ∑ q ∈ S, ∑ q' ∈ S, (a q * (ramSum q n).re) * (a q' * (ramSum q' n).re) := by
    intro n _
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single q]
  · have hqpos : 0 < q := hpos q hq
    have hMq : (M / q) * q = M := Nat.div_mul_cancel (hdvd q hq)
    have hdiag : ∑ n ∈ Finset.range M, (ramSum q n).re ^ 2 = (M : ℝ) * (Nat.totient q) := by
      have h := ramSum_re_sq_sum_multi q (M / q) hqpos
      rw [hMq] at h
      have hMqR : (↑(M / q) : ℝ) * ↑q = (↑M : ℝ) := by rw [← Nat.cast_mul, hMq]
      rw [hMqR] at h
      exact h
    calc ∑ n ∈ Finset.range M, (a q * (ramSum q n).re) * (a q * (ramSum q n).re)
        = a q ^ 2 * ∑ n ∈ Finset.range M, (ramSum q n).re ^ 2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
      _ = a q ^ 2 * ((M : ℝ) * (Nat.totient q)) := by rw [hdiag]
      _ = a q ^ 2 * (M : ℝ) * (Nat.totient q) := by ring
  · intro q' hq' hne
    have hMqq' : (M / (q * q')) * (q * q') = M := Nat.div_mul_cancel (hdvd2 q hq q' hq' hne.symm)
    have hoff : ∑ n ∈ Finset.range M, (ramSum q n).re * (ramSum q' n).re = 0 := by
      have h := ramSum_re_orthogonal_offdiag_multi q q' (M / (q * q')) (hpos q hq) (hpos q' hq') hne.symm
      rwa [hMqq'] at h
    calc ∑ n ∈ Finset.range M, (a q * (ramSum q n).re) * (a q' * (ramSum q' n).re)
        = a q * a q' * ∑ n ∈ Finset.range M, (ramSum q n).re * (ramSum q' n).re := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
      _ = a q * a q' * 0 := by rw [hoff]
      _ = 0 := by ring
  · intro hnq; exact absurd hq hnq

/-- **Minkowski-route summability**: `∑_q μ(q)²/φ(q)^{3/2} < ∞`. From `sqfree_totient_strong`
    (`φ² ≥ q^{3/2}/8` ⇒ `φ^{3/2} ≥ q^{9/8}/2^{9/4}`) vs the summable `∑ 1/q^{9/8}` (9/8 > 1). This is the
    convergent Minkowski bound `√L·∑ μ²/φ^{3/2}` the harc truncation needs (the naive diagonal+off-
    diagonal route diverges — the signed off-diagonal's large-sieve cancellation is lost to triangle). -/
lemma phi_pow32_summable :
    Summable (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) := by
  apply Summable.of_nonneg_of_le (fun q => by positivity)
    (f := fun q : ℕ => (2 : ℝ) ^ ((9 : ℝ) / 4) * (1 / (q : ℝ) ^ ((9 : ℝ) / 8)))
  · intro q
    by_cases hsq : Squarefree q
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hsq.ne_zero
      have hφpos : 0 < (Nat.totient q : ℝ) := by
        have := Nat.totient_pos.mpr hqpos; positivity
      have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
        have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [h1, abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ),
          sq_abs ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
      have hts := sqfree_totient_strong q hsq
      have h8 : (8 : ℝ) ^ ((3 : ℝ) / 4) = (2 : ℝ) ^ ((9 : ℝ) / 4) := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 3,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      have hpow : (q : ℝ) ^ ((9 : ℝ) / 8) ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) * (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) := by
        have hφ2 : (Nat.totient q : ℝ) ^ 2 = (Nat.totient q : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
        have hts' : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 * (Nat.totient q : ℝ) ^ (2 : ℝ) := by rw [← hφ2]; exact hts
        have hb := Real.rpow_le_rpow (by positivity) hts' (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)
        rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (q : ℝ)),
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))] at hb
        norm_num at hb
        rw [h8] at hb
        exact hb
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      calc (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ ((9 : ℝ) / 8)
          ≤ 1 * (q : ℝ) ^ ((9 : ℝ) / 8) := mul_le_mul_of_nonneg_right hμ2 (by positivity)
        _ = (q : ℝ) ^ ((9 : ℝ) / 8) := one_mul _
        _ ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) * (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) := hpow
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      have hz : ((0 : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) = 0 := by norm_num
      rw [hz]; positivity
  · exact (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left _

/-- Telescoping: `∑_{n=2}^{m} 1/(n(n-1)) = 1 - 1/m` for `m ≥ 2`. -/
lemma sum_Icc_inv_mul_pred (m : ℕ) (hm : 2 ≤ m) :
    ∑ n ∈ Finset.Icc 2 m, 1 / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (m : ℝ) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · norm_num [Finset.Icc_self]
    · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1), ih hk]
      have hk0 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hk2 : (k : ℝ) ≠ 0 := by linarith
      have hterm : (1 : ℝ) / ((↑(k + 1) : ℝ) * ((↑(k + 1) : ℝ) - 1)) = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
        push_cast
        rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) from by ring]
        field_simp
        ring
      rw [hterm]
      push_cast
      ring

/-- **The carefree product** `∏_{p|q}(1 + 1/(p(p-1))) ≤ e` (absolute constant). Via `1+x ≤ exp x`
    and `∑_{p|q} 1/(p(p-1)) ≤ 1` (telescoping over `p ∈ [2,q]`). This is the `C₀ = e` in the
    arithmetic length-capped mean square `∑_{n<N} c_q(n)² ≤ C₀·N·φ(q)` — the only such bound that
    closes the Minkowski route for `q > N` (the cosecant/min boundary `~φq` diverges there). -/
lemma carefree_prod_le (q : ℕ) :
    ∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.exp 1 := by
  have hstep : ∀ p ∈ q.primeFactors,
      (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 1)))]
  have hnn : ∀ p ∈ q.primeFactors, (0 : ℝ) ≤ 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    positivity
  calc ∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∏ p ∈ q.primeFactors, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.prod_le_prod₀ hnn hstep
    _ = Real.exp (∑ p ∈ q.primeFactors, 1 / ((p : ℝ) * ((p : ℝ) - 1))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        rcases Nat.lt_or_ge q 2 with hq | hq
        · interval_cases q <;> simp
        · have hsub : q.primeFactors ⊆ Finset.Icc 2 q := by
            intro p hp
            rw [Finset.mem_Icc]
            exact ⟨(Nat.prime_of_mem_primeFactors hp).two_le, Nat.le_of_mem_primeFactors hp⟩
          calc ∑ p ∈ q.primeFactors, 1 / ((p : ℝ) * ((p : ℝ) - 1))
              ≤ ∑ n ∈ Finset.Icc 2 q, 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub
                intro n hn _
                rw [Finset.mem_Icc] at hn
                have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
                have : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
                positivity
            _ = 1 - 1 / (q : ℝ) := sum_Icc_inv_mul_pred q hq
            _ ≤ 1 := by
                have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
                linarith [div_nonneg (zero_le_one) hqR]

/-- `h(g) = φ(g)²/g` as a multiplicative arithmetic function (the summand of the length-capped
    mean-square divisor sum). -/
noncomputable def hphi : ArithmeticFunction ℝ :=
  ⟨fun g => (Nat.totient g : ℝ) ^ 2 / (g : ℝ), by simp⟩

lemma hphi_apply (g : ℕ) : hphi g = (Nat.totient g : ℝ) ^ 2 / (g : ℝ) := rfl

lemma isMult_hphi : hphi.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [hphi_apply]
  · intro a b hab
    simp only [hphi_apply, Nat.totient_mul hab]
    push_cast
    rw [mul_pow, div_mul_div_comm]

/-- **Multiplicative divisor sum**: `∑_{g|q} φ(g)²/g = ∏_{p|q}(1+(p-1)²/p)` for squarefree `q`.
    Via `∑_{d|q} h(d) = (ζ ⋆ h)(q)` (multiplicative, `IsMultiplicative.multiplicative_factorization`)
    factoring over `primeFactors` at squarefree `q`, with `(ζ⋆h)(p) = h(1)+h(p) = 1+(p-1)²/p`. -/
lemma div_sum_phisq (q : ℕ) (hq : Squarefree q) :
    ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2 / (g : ℝ)
      = ∏ p ∈ q.primeFactors, (1 + ((p : ℝ) - 1) ^ 2 / (p : ℝ)) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hzm : (↑(ArithmeticFunction.zeta) : ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.natCast ArithmeticFunction.isMultiplicative_zeta
  have hmultF : ((↑(ArithmeticFunction.zeta) : ArithmeticFunction ℝ) * hphi).IsMultiplicative :=
    hzm.mul isMult_hphi
  have hconv : ((↑(ArithmeticFunction.zeta) : ArithmeticFunction ℝ) * hphi) q
      = ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2 / (g : ℝ) := by
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    exact Finset.sum_congr rfl (fun g _ => hphi_apply g)
  rw [← hconv,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hmultF hq0,
    Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
  have hfp : q.factorization p = 1 := by
    have h1 : q.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hq0).mp hq p
    have h2 : 0 < q.factorization p := hpp.factorization_pos_of_dvd hq0 hpdvd
    omega
  rw [hfp, pow_one, ArithmeticFunction.coe_zeta_mul_apply, hpp.divisors,
    Finset.sum_pair hpp.one_lt.ne, hphi_apply, hphi_apply, Nat.totient_one, Nat.totient_prime hpp]
  push_cast [Nat.cast_sub hpp.one_le]
  ring

/-- `∏_{p|q}(p-1) = φ(q)` for squarefree `q`. -/
lemma prod_sub_one_eq_totient (q : ℕ) (hq : Squarefree q) :
    ∏ p ∈ q.primeFactors, (p - 1) = Nat.totient q := by
  rw [Nat.totient_eq_prod_factorization hq.ne_zero, Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hfp : q.factorization p = 1 := by
    have h1 : q.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hq.ne_zero).mp hq p
    have h2 : 0 < q.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hq.ne_zero
        (Nat.dvd_of_mem_primeFactors hp)
    omega
  rw [hfp]; simp

/-- **`∑_{g|q} φ(g)²/g ≤ e·φ(q)`** for squarefree `q` — the sharp divisor-sum bound. Combines the
    multiplicative identity `= ∏(1+(p-1)²/p) = φ(q)·∏(1+1/(p(p-1)))` with `carefree_prod_le ≤ e`. The
    RHS of the arithmetic length-capped mean square `∑_{n<N} c_q² ≤ (N-1)·(∑φ(g)²/g) ≤ e·N·φ(q)`. -/
lemma div_sum_phisq_le (q : ℕ) (hq : Squarefree q) :
    ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2 / (g : ℝ) ≤ Real.exp 1 * (Nat.totient q : ℝ) := by
  rw [div_sum_phisq q hq]
  have hfact : ∏ p ∈ q.primeFactors, (1 + ((p : ℝ) - 1) ^ 2 / (p : ℝ))
      = (∏ p ∈ q.primeFactors, ((p : ℝ) - 1))
        * ∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpne : (p : ℝ) ≠ 0 := by linarith
    have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hphiprod : (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) = (Nat.totient q : ℝ) := by
    rw [← prod_sub_one_eq_totient q hq, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [hfact, hphiprod, mul_comm (Real.exp 1)]
  exact mul_le_mul_of_nonneg_left (carefree_prod_le q) (by positivity)

/-- **Length-capped mean square (assembled)**: `∑_{n∈[1,N)} c_q(n)² ≤ e·φ(q)·(N-1)` for squarefree `q`.
    The arithmetic bound that closes the Minkowski route (the cosecant/min boundary `~φq` diverges for
    `q>N`). Via `cRam_sq_sqfree` (`c_q(n)²=φ(gcd(q,n))²`, constant on gcd-fibers), regroup over `g|q`
    (`sum_fiberwise_of_maps_to`), bound each fiber `#{n:gcd=g} ≤ #{n:g∣n} ≤ (N-1)/g`
    (`card_multiples_Ico_le`), then the sharp divisor sum `∑φ(g)²/g ≤ e·φ(q)` (`div_sum_phisq_le`). -/
lemma cRam_meansq_Ico_le (q N : ℕ) (hq : Squarefree q) :
    ∑ n ∈ Finset.Ico 1 N, ((cRam q n : ℝ)) ^ 2
      ≤ Real.exp 1 * (Nat.totient q : ℝ) * ((N - 1 : ℕ) : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hrw : ∀ n, ((cRam q n : ℝ)) ^ 2 = ((Nat.totient (Nat.gcd q n) : ℝ)) ^ 2 := by
    intro n; exact_mod_cast cRam_sq_sqfree q n hq
  simp_rw [hrw]
  have hmaps : ∀ n ∈ Finset.Ico 1 N, Nat.gcd q n ∈ q.divisors := by
    intro n hn
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left q n, hq0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => (Nat.totient (Nat.gcd q n) : ℝ) ^ 2)]
  calc ∑ g ∈ q.divisors, ∑ n ∈ (Finset.Ico 1 N).filter (fun n => Nat.gcd q n = g),
          (Nat.totient (Nat.gcd q n) : ℝ) ^ 2
      = ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2
          * (((Finset.Ico 1 N).filter (fun n => Nat.gcd q n = g)).card : ℝ) := by
        apply Finset.sum_congr rfl; intro g _
        have heq : ∀ n ∈ (Finset.Ico 1 N).filter (fun n => Nat.gcd q n = g),
            (Nat.totient (Nat.gcd q n) : ℝ) ^ 2 = (Nat.totient g : ℝ) ^ 2 := by
          intro n hn; rw [(Finset.mem_filter.mp hn).2]
        rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2 * (((N - 1) / g : ℕ) : ℝ) := by
        apply Finset.sum_le_sum; intro g hg
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsub : (Finset.Ico 1 N).filter (fun n => Nat.gcd q n = g)
            ⊆ (Finset.Ico 1 N).filter (fun n => g ∣ n) := by
          intro n hn; rw [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1, hn.2 ▸ Nat.gcd_dvd_right q n⟩
        have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
        have hc := le_trans (Finset.card_le_card hsub) (card_multiples_Ico_le N g hg1)
        exact_mod_cast hc
    _ ≤ ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2 * (((N - 1 : ℕ) : ℝ) / (g : ℝ)) := by
        apply Finset.sum_le_sum; intro g _
        apply mul_le_mul_of_nonneg_left (Nat.cast_div_le) (by positivity)
    _ = ((N - 1 : ℕ) : ℝ) * ∑ g ∈ q.divisors, (Nat.totient g : ℝ) ^ 2 / (g : ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring
    _ ≤ ((N - 1 : ℕ) : ℝ) * (Real.exp 1 * (Nat.totient q : ℝ)) :=
        mul_le_mul_of_nonneg_left (div_sum_phisq_le q hq) (by positivity)
    _ = Real.exp 1 * (Nat.totient q : ℝ) * ((N - 1 : ℕ) : ℝ) := by ring

/-- **Per-q bound**: `√(∑_{n∈(X/2,X]}(Tarith n q)²) ≤ √(eX)·μ(q)²/φ(q)^{3/2}` for squarefree `q`. The
    per-modulus ℓ² norm feeding the truncation Minkowski assembly (its RHS is exactly the summand of
    `phi_pow32_summable`). Uses `μ(q)²=1` (squarefree) + `cRam_meansq_Ico_le` (`∑c_q²≤eφ(q)X`). -/
lemma tarith_l2_le (q X : ℕ) (hq : Squarefree q) :
    Real.sqrt (∑ n ∈ Finset.Ioc (X / 2) X, (Tarith n q) ^ 2)
      ≤ Real.sqrt (Real.exp 1 * (X : ℝ))
        * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hFpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have := Nat.totient_pos.mpr hqpos; positivity
  have hmu : ((ArithmeticFunction.moebius q : ℝ)) ^ 2 = 1 := by
    have hne : ArithmeticFunction.moebius q ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hq
    have habs : |ArithmeticFunction.moebius q| = 1 :=
      le_antisymm ArithmeticFunction.abs_moebius_le_one (Int.one_le_abs hne)
    have : (ArithmeticFunction.moebius q) ^ 2 = 1 := by rw [← sq_abs, habs]; norm_num
    exact_mod_cast this
  have hcm : ∑ n ∈ Finset.Ioc (X / 2) X, ((cRam q n : ℝ)) ^ 2
      ≤ Real.exp 1 * (Nat.totient q : ℝ) * (X : ℝ) := by
    calc ∑ n ∈ Finset.Ioc (X / 2) X, ((cRam q n : ℝ)) ^ 2
        ≤ ∑ n ∈ Finset.Ico 1 (X + 1), ((cRam q n : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Ico] at *; omega
          · intro n _ _; positivity
      _ ≤ Real.exp 1 * (Nat.totient q : ℝ) * (((X + 1) - 1 : ℕ) : ℝ) := cRam_meansq_Ico_le q (X + 1) hq
      _ = Real.exp 1 * (Nat.totient q : ℝ) * (X : ℝ) := by norm_num
  have hexp2 : ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2
      = 1 / (Nat.totient q : ℝ) ^ 3 := by
    rw [div_pow, hmu, one_pow, ← Real.rpow_natCast ((Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) 2,
      ← Real.rpow_mul hFpos.le]
    norm_num
  have hpull : ∑ n ∈ Finset.Ioc (X / 2) X, (Tarith n q) ^ 2
      = (1 / (Nat.totient q : ℝ) ^ 4) * ∑ n ∈ Finset.Ioc (X / 2) X, ((cRam q n : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [Tarith_apply, hmu]
    field_simp
  have hsq : ∑ n ∈ Finset.Ioc (X / 2) X, (Tarith n q) ^ 2
      ≤ Real.exp 1 * (X : ℝ)
        * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
    rw [hexp2, hpull]
    calc (1 / (Nat.totient q : ℝ) ^ 4) * ∑ n ∈ Finset.Ioc (X / 2) X, ((cRam q n : ℝ)) ^ 2
        ≤ (1 / (Nat.totient q : ℝ) ^ 4) * (Real.exp 1 * (Nat.totient q : ℝ) * (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hcm (by positivity)
      _ = Real.exp 1 * (X : ℝ) * (1 / (Nat.totient q : ℝ) ^ 3) := by field_simp
  calc Real.sqrt (∑ n ∈ Finset.Ioc (X / 2) X, (Tarith n q) ^ 2)
      ≤ Real.sqrt (Real.exp 1 * (X : ℝ)
          * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Real.exp 1 * (X : ℝ))
          * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Per-q ℓ² bound for ALL q** (non-squarefree ⇒ `μ=0` ⇒ both sides 0). The all-`q` form that
    plugs into the truncation Minkowski assembly's finite sum over `q ∈ S`. -/
lemma tarith_l2_le_all (q X : ℕ) :
    Real.sqrt (∑ n ∈ Finset.Ioc (X / 2) X, (Tarith n q) ^ 2)
      ≤ Real.sqrt (Real.exp 1 * (X : ℝ))
        * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) := by
  by_cases hq : Squarefree q
  · exact tarith_l2_le q X hq
  · have hmu : (ArithmeticFunction.moebius q : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]; norm_num
    have hz : ∀ n ∈ Finset.Ioc (X / 2) X, (Tarith n q) ^ 2 = 0 := by
      intro n _; rw [Tarith_apply, hmu]; ring
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, Real.sqrt_zero, hmu]
    simp

/-- `∑_q μ(q)²/φ(q)³` converges — bounded termwise by `4/q^{6/5}` (via `1/φ³ ≤ 1/φ²` for `φ ≥ 1`
    and `sqfree_totient`). This is the diagonal of the aggregate at `a_q = μ(q)²/φ(q)²`, so its
    tail `∑_{q>P} μ(q)²/φ(q)³ → 0` bounds the harc truncation error. -/
lemma phi_cube_summable :
    Summable (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 3) := by
  apply Summable.of_nonneg_of_le (fun q => by positivity)
    (f := fun q : ℕ => 4 * (1 / (q : ℝ) ^ ((6 : ℝ) / 5)))
  · intro q
    by_cases hsf : Squarefree q
    · have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
        have : 0 < Nat.totient q := Nat.totient_pos.mpr hsf.ne_zero.bot_lt
        positivity
      have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
        have : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hsf.ne_zero.bot_lt
        exact_mod_cast this
      have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
        have h' : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
        nlinarith [sq_abs (ArithmeticFunction.moebius q : ℝ),
          abs_nonneg (ArithmeticFunction.moebius q : ℝ), h']
      have hq6 : (0 : ℝ) < (q : ℝ) ^ ((6 : ℝ) / 5) := by
        have hq0 : 0 < q := hsf.ne_zero.bot_lt
        have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
        positivity
      have hst := sqfree_totient q hsf
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hq6]
      nlinarith [hst, hμ2, hφ1, hφpos, hq6.le,
        mul_nonneg (show (0 : ℝ) ≤ 1 - (ArithmeticFunction.moebius q : ℝ) ^ 2 by linarith) hq6.le,
        mul_nonneg (sq_nonneg (Nat.totient q : ℝ)) (show (0 : ℝ) ≤ (Nat.totient q : ℝ) - 1 by linarith)]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp
      positivity
  · apply Summable.mul_left
    exact (Real.summable_one_div_nat_rpow).mpr (by norm_num)

/-- `(c_q(n)).re = cRam q n` (the Ramanujan sum is that integer). -/
lemma ramSum_re_eq_cRam (q n : ℕ) (hq : 0 < q) : (ramSum q n).re = (cRam q n : ℝ) := by
  rw [ramSum_eq_cRam q n hq, Complex.intCast_re]

/-- **Bridge**: `Tarith n q = (μ(q)²/φ(q)²)·(c_q(n)).re` — the singular-series term as a coefficient
    times the (real) Ramanujan sum, matching the aggregate's shape (`a_q = μ(q)²/φ(q)²`). -/
lemma Tarith_eq (q n : ℕ) (hq : 0 < q) :
    Tarith n q
      = ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) * (ramSum q n).re := by
  rw [Tarith_apply, ramSum_re_eq_cRam q n hq]
  ring

/-- **Singular-series mean square over a period**: `∑_{n<M}(∑_{q∈S} Tarith n q)² = ∑_{q∈S}(μ²/φ²)²·M·φ`.
    Combines the aggregate large sieve with the `Tarith → a_q·c_q` bridge — the truncation-tail L²
    over a full period, before instantiating `S = {q > P}` and bounding by `phi_cube_summable`. -/
lemma Tarith_aggregate_meansq (S : Finset ℕ) (M : ℕ)
    (hpos : ∀ q ∈ S, 0 < q) (hdvd : ∀ q ∈ S, q ∣ M)
    (hdvd2 : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → (q * q') ∣ M) :
    ∑ n ∈ Finset.range M, (∑ q ∈ S, Tarith n q) ^ 2
      = ∑ q ∈ S, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) ^ 2
          * (M : ℝ) * (Nat.totient q) := by
  have hbridge : ∀ n ∈ Finset.range M, (∑ q ∈ S, Tarith n q) ^ 2
      = (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2)
          * (ramSum q n).re) ^ 2 := by
    intro n _
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    exact Tarith_eq q n (hpos q hq)
  rw [Finset.sum_congr rfl hbridge]
  exact aggregate_meansq S (fun q => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2)
    M hpos hdvd hdvd2

/-- **Clean truncation-tail L² over a period**: `∑_{n<M}(∑_{q∈S} Tarith n q)² = M·∑_{q∈S} μ(q)²/φ(q)³`.
    Simplifies the aggregate's diagonal via `μ⁴=μ²`. With `S = {q ∈ (P, …]}` this is exactly the tail
    controlled by `phi_cube_summable` — the σ(n)²-free bound the harc truncation needs. -/
lemma Tarith_aggregate_meansq_clean (S : Finset ℕ) (M : ℕ)
    (hpos : ∀ q ∈ S, 0 < q) (hdvd : ∀ q ∈ S, q ∣ M)
    (hdvd2 : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → (q * q') ∣ M) :
    ∑ n ∈ Finset.range M, (∑ q ∈ S, Tarith n q) ^ 2
      = (M : ℝ) * ∑ q ∈ S, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 3 := by
  rw [Tarith_aggregate_meansq S M hpos hdvd hdvd2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have : 0 < Nat.totient q := Nat.totient_pos.mpr (hpos q hq)
    positivity
  have hμ4 : (ArithmeticFunction.moebius q : ℝ) ^ 4 = (ArithmeticFunction.moebius q : ℝ) ^ 2 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := q)
    rw [abs_le] at h
    have hm : ArithmeticFunction.moebius q = -1 ∨ ArithmeticFunction.moebius q = 0
        ∨ ArithmeticFunction.moebius q = 1 := by omega
    rcases hm with h1 | h1 | h1 <;> rw [h1] <;> norm_num
  rw [div_pow, show ((ArithmeticFunction.moebius q : ℝ) ^ 2) ^ 2
      = (ArithmeticFunction.moebius q : ℝ) ^ 4 by ring, hμ4]
  field_simp

/-- **Interval expansion**: `∑_{n<N} c_q(n)·conj c_q(n) = ∑_{r,r'∈U_q} ∑_{n<N} e((r−r')n/q)` — the
    character double-sum over an ARBITRARY interval (the direct route to the interval mean square,
    which the full-period aggregate cannot reach since `lcm(moduli) ≫ N`). No collapse yet: the
    inner `∑_{n<N} e(·)` is bounded by `N` on the diagonal, by `2/‖e(θ)−1‖` off it. -/
lemma ramSum_sq_interval_expand (q N : ℕ) :
    ∑ n ∈ Finset.range N, ramSum q n * (starRingEnd ℂ) (ramSum q n)
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
          ∑ r' ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
            ∑ n ∈ Finset.range N, e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) := by
  have step1 : ∀ n ∈ Finset.range N, ramSum q n * (starRingEnd ℂ) (ramSum q n)
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
          ∑ r' ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
            e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) := by
    intro n _
    simp only [ramSum]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro r' _
    rw [e_conj, e_add]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.sum_comm]


/-- Off the integers, `e θ ≠ 1` — the non-degeneracy that makes the off-diagonal geometric bound
    `sum_e_norm_le_geom` apply to `θ = (r−r')/q` when `0 < |r−r'| < q`. -/
lemma e_ne_one_of_not_int (x : ℝ) (h : ∀ m : ℤ, x ≠ m) : e x ≠ 1 := by
  intro he
  rw [e_eq_one_iff] at he
  obtain ⟨m, hm⟩ := he
  exact h m hm

/-- **Off-diagonal geometric bound**: for `r ≠ r'` with `r, r' < q`, the interval character sum
    `∑_{n<N} e((r−r')n/q)` is bounded — independent of `N` — by `2/‖e((r−r')/q)−1‖`. The `N`-free
    boundary term of the interval mean square. -/
lemma offdiag_geom_bound (q N r r' : ℕ) (hq : 0 < q) (hr : r < q) (hr' : r' < q) (hne : r ≠ r') :
    ‖∑ n ∈ Finset.range N, e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / (q : ℝ))‖
      ≤ 2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖ := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hθne : e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) ≠ 1 := by
    apply e_ne_one_of_not_int
    intro m hm
    rw [div_eq_iff hqR] at hm
    have hint : (r : ℤ) - (r' : ℤ) = m * q := by exact_mod_cast hm
    have hri : (0 : ℤ) ≤ (r : ℤ) := by positivity
    have hr'i : (0 : ℤ) ≤ (r' : ℤ) := by positivity
    have hrqi : (r : ℤ) < q := by exact_mod_cast hr
    have hr'qi : (r' : ℤ) < q := by exact_mod_cast hr'
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · have : (r : ℤ) - (r' : ℤ) ≤ -(q : ℤ) := by
        rw [hint]; nlinarith [mul_le_mul_of_nonneg_right (show m ≤ -1 by omega) hqz.le]
      omega
    · rw [hm0, zero_mul] at hint; omega
    · have : (q : ℤ) ≤ (r : ℤ) - (r' : ℤ) := by
        rw [hint]; nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ m by omega) hqz.le]
      omega
  have hrw : ∀ n : ℕ, e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / (q : ℝ))
      = e ((n : ℝ) * ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ))) := by
    intro n; congr 1; ring
  rw [Finset.sum_congr rfl (fun n _ => hrw n)]
  exact sum_e_norm_le_geom ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) N hθne

/-- **Interval diagonal extraction**: the interval mean square `∑_{n<N} c_q(n)·conj c_q(n)` splits
    into `N·φ(q)` (diagonal `r'=r`, each inner sum `= N`) plus an off-diagonal remainder (bounded
    by `offdiag_geom_bound` per pair). The `N·φ(q)` main term is exactly the full-period value's
    per-period average times `N`. -/
lemma ramSum_sq_interval_diag (q N : ℕ) (hq : 0 < q) :
    ∑ n ∈ Finset.range N, ramSum q n * (starRingEnd ℂ) (ramSum q n)
      = (N : ℂ) * (Nat.totient q)
        + ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
            ∑ r' ∈ ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).erase r,
              ∑ n ∈ Finset.range N, e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) := by
  set U := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hU
  have he0 : e 0 = 1 := by simp [e]
  rw [ramSum_sq_interval_expand q N]
  have hsplit : ∀ r ∈ U, ∑ r' ∈ U, (∑ n ∈ Finset.range N,
        e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q))
      = (∑ n ∈ Finset.range N, e ((((r : ℤ) - (r : ℤ) : ℤ) : ℝ) * (n : ℝ) / q))
        + ∑ r' ∈ U.erase r, ∑ n ∈ Finset.range N,
            e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) := by
    intro r hr
    exact (Finset.add_sum_erase U _ hr).symm
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  have hdiag : ∀ r ∈ U, ∑ n ∈ Finset.range N,
      e ((((r : ℤ) - (r : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) = (N : ℂ) := by
    intro r _
    have hone : ∀ n : ℕ, e ((((r : ℤ) - (r : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) = 1 := by
      intro n
      rw [show ((((r : ℤ) - (r : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) = 0 by push_cast; ring]
      exact he0
    rw [Finset.sum_congr rfl (fun n _ => hone n)]
    simp
  have hcard : U.card = Nat.totient q := by
    rw [hU, Nat.totient]
    apply Finset.card_nbij' id id <;> intro x hx <;>
      simp_all [Finset.mem_filter, Nat.Coprime, Nat.gcd_comm]
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, hcard, nsmul_eq_mul, mul_comm]

/-- **Interval single-modulus mean square bound**: `|∑_{n<N}‖c_q(n)‖² − N·φ(q)|` is at most the
    summed off-diagonal geometric bounds — an `N`-free error. This is the interval analogue of the
    full-period identity `∑‖c_q‖²=q·φ(q)`: main term `N·φ(q)`, boundary `O_q(1)` in `N`. -/
lemma ramSum_sq_interval_bound (q N : ℕ) (hq : 0 < q) :
    |(∑ n ∈ Finset.range N, ‖ramSum q n‖ ^ 2) - (N : ℝ) * (Nat.totient q)|
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
          ∑ r' ∈ ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).erase r,
            2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖ := by
  set U := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hU
  set D := ∑ r ∈ U, ∑ r' ∈ U.erase r, ∑ n ∈ Finset.range N,
    e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q) with hD
  have hre : ∑ n ∈ Finset.range N, ‖ramSum q n‖ ^ 2
      = (∑ n ∈ Finset.range N, ramSum q n * (starRingEnd ℂ) (ramSum q n)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hre, ramSum_sq_interval_diag q N hq, Complex.add_re]
  have hNφ : ((N : ℂ) * (Nat.totient q)).re = (N : ℝ) * (Nat.totient q) := by simp
  rw [hNφ, show (N : ℝ) * (Nat.totient q) + D.re - (N : ℝ) * (Nat.totient q) = D.re by ring]
  calc |D.re| ≤ ‖D‖ := by
        have h1 : D.re ^ 2 ≤ ‖D‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith [sq_nonneg D.im]
        nlinarith [h1, norm_nonneg D, abs_nonneg D.re, sq_abs D.re]
    _ ≤ ∑ r ∈ U, ‖∑ r' ∈ U.erase r, ∑ n ∈ Finset.range N,
          e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ U, ∑ r' ∈ U.erase r, ‖∑ n ∈ Finset.range N,
          e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) * (n : ℝ) / q)‖ := by
        apply Finset.sum_le_sum; intro r _; exact norm_sum_le _ _
    _ ≤ ∑ r ∈ U, ∑ r' ∈ U.erase r,
          2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖ := by
        apply Finset.sum_le_sum; intro r hr
        apply Finset.sum_le_sum; intro r' hr'
        have hrq : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
        have hr'mem : r' ∈ U := Finset.mem_of_mem_erase hr'
        have hr'q : r' < q := Finset.mem_range.mp (Finset.mem_filter.mp hr'mem).1
        have hne : r ≠ r' := (Finset.ne_of_mem_erase hr').symm
        exact offdiag_geom_bound q N r r' hq hrq hr'q hne

/-- **Cross-moduli interval bound**: for `q ≠ q'`, `∑_{n<N} c_q(n)·conj c_{q'}(n)` has NO main term
    (unlike the `q=q'` diagonal `ramSum_sq_interval_bound`) — over any interval it is at most the
    summed off-diagonal cosecant boundary. This is the orthogonality that kills the pointwise
    `σ(n)²` loss for the harc truncation's cross terms. Holds for ANY distinct `q,q'` (no coprimality
    needed): the full-period contradiction `qq'|(rq'−r'q) ⟹ q|q' ∧ q'|q ⟹ q=q'` (same as
    `ramSum_orthogonal_offdiag`) makes every character `e((rq'−r'q)/(qq'))≠1`. -/
lemma ramSum_cross_interval_bound (q q' N : ℕ) (hq : 0 < q) (hq' : 0 < q') (hne : q ≠ q') :
    ‖∑ n ∈ Finset.range N, ramSum q n * (starRingEnd ℂ) (ramSum q' n)‖
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
          ∑ r' ∈ (Finset.range q').filter (fun r => Nat.gcd r q' = 1),
            2 / ‖e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ)
                      / ((q * q' : ℕ) : ℝ)) - 1‖ := by
  set Uq := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hUq
  set Uq' := (Finset.range q').filter (fun r => Nat.gcd r q' = 1) with hUq'
  have hmul : 0 < q * q' := Nat.mul_pos hq hq'
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hq'R : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne'
  have step1 : ∀ n ∈ Finset.range N,
      ramSum q n * (starRingEnd ℂ) (ramSum q' n)
        = ∑ r ∈ Uq, ∑ r' ∈ Uq',
            e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ)) := by
    intro n _
    simp only [ramSum]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro r' _
    rw [e_conj, e_add]
    congr 1
    push_cast; field_simp; ring
  rw [Finset.sum_congr rfl step1]
  have hswap : ∑ n ∈ Finset.range N, ∑ r ∈ Uq, ∑ r' ∈ Uq',
        e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ))
      = ∑ r ∈ Uq, ∑ r' ∈ Uq', ∑ n ∈ Finset.range N,
        e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ)) := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r _; rw [Finset.sum_comm]
  rw [hswap]
  calc ‖∑ r ∈ Uq, ∑ r' ∈ Uq', ∑ n ∈ Finset.range N,
          e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ))‖
      ≤ ∑ r ∈ Uq, ‖∑ r' ∈ Uq', ∑ n ∈ Finset.range N,
          e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r ∈ Uq, ∑ r' ∈ Uq', ‖∑ n ∈ Finset.range N,
          e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ))‖ := by
        apply Finset.sum_le_sum; intro r _; exact norm_sum_le _ _
    _ ≤ ∑ r ∈ Uq, ∑ r' ∈ Uq',
          2 / ‖e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) / ((q * q' : ℕ) : ℝ)) - 1‖ := by
        apply Finset.sum_le_sum; intro r hr
        apply Finset.sum_le_sum; intro r' hr'
        have hrc : Nat.gcd r q = 1 := (Finset.mem_filter.mp hr).2
        have hr'c : Nat.gcd r' q' = 1 := (Finset.mem_filter.mp hr').2
        have hθne : e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ)
                        / ((q * q' : ℕ) : ℝ)) ≠ 1 := by
          apply e_ne_one_of_not_int
          intro m hm
          have hDR : ((q * q' : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmul.ne'
          rw [div_eq_iff hDR] at hm
          have hM : (r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) = m * ((q * q' : ℕ) : ℤ) := by
            exact_mod_cast hm
          have hdvd : ((q * q' : ℕ) : ℤ) ∣ ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) :=
            ⟨m, by rw [hM]; ring⟩
          have hqdvd_prod : (q : ℤ) ∣ ((q * q' : ℕ) : ℤ) := ⟨(q' : ℤ), by push_cast; ring⟩
          have h1 : (q : ℤ) ∣ ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) := dvd_trans hqdvd_prod hdvd
          have h2 : (q : ℤ) ∣ (r : ℤ) * (q' : ℤ) := by
            have h3 := dvd_add h1 (dvd_mul_left (q : ℤ) (r' : ℤ))
            have he : (r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) + (r' : ℤ) * (q : ℤ)
                = (r : ℤ) * (q' : ℤ) := by ring
            rwa [he] at h3
          have hcopq : IsCoprime (q : ℤ) (r : ℤ) := by
            rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hrc
          have hqq' : (q : ℤ) ∣ (q' : ℤ) := hcopq.dvd_of_dvd_mul_left h2
          have hq'dvd_prod : (q' : ℤ) ∣ ((q * q' : ℕ) : ℤ) := ⟨(q : ℤ), by push_cast; ring⟩
          have h1' : (q' : ℤ) ∣ ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ)) := dvd_trans hq'dvd_prod hdvd
          have h2' : (q' : ℤ) ∣ (r' : ℤ) * (q : ℤ) := by
            have h3 := dvd_sub (dvd_mul_left (q' : ℤ) (r : ℤ)) h1'
            have he : (r : ℤ) * (q' : ℤ) - ((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ))
                = (r' : ℤ) * (q : ℤ) := by ring
            rwa [he] at h3
          have hcopq' : IsCoprime (q' : ℤ) (r' : ℤ) := by
            rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hr'c
          have hq'q : (q' : ℤ) ∣ (q : ℤ) := hcopq'.dvd_of_dvd_mul_left h2'
          exact hne (Nat.dvd_antisymm (by exact_mod_cast hqq') (by exact_mod_cast hq'q))
        have hrw : ∀ n : ℕ,
            e ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ) * (n : ℝ) / ((q * q' : ℕ) : ℝ))
              = e ((n : ℝ) * ((((r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) : ℤ) : ℝ)
                    / ((q * q' : ℕ) : ℝ))) := by
          intro n; congr 1; ring
        rw [Finset.sum_congr rfl (fun n _ => hrw n)]
        exact sum_e_norm_le_geom _ N hθne

/-- `‖e θ − 1‖² = 2 − 2cos(2πθ)` (`= 4 sin²(πθ)`). The magnitude of the additive-character
    displacement — the analytic input to bounding the off-diagonal boundary term `∑ 2/‖e(θ)−1‖`. -/
lemma norm_e_sub_one_sq (θ : ℝ) : ‖e θ - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * θ) := by
  have he : e θ = Complex.exp (↑(2 * Real.pi * θ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hre : (e θ).re = Real.cos (2 * Real.pi * θ) := by
    rw [he]; exact Complex.exp_ofReal_mul_I_re _
  have him : (e θ).im = Real.sin (2 * Real.pi * θ) := by
    rw [he]; exact Complex.exp_ofReal_mul_I_im _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, hre, him]
  linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * θ)

/-- `‖e θ − 1‖ = 2|sin(πθ)|` — the exact character-displacement magnitude. The off-diagonal
    boundary bound becomes `∑ 1/|sin(π(r−r')/q)|`, a cosecant sum controlled by `|sin| ≥ 2·dist(·,ℤ)`. -/
lemma norm_e_sub_one (θ : ℝ) : ‖e θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  have hcos : 2 - 2 * Real.cos (2 * Real.pi * θ) = (2 * |Real.sin (Real.pi * θ)|) ^ 2 := by
    rw [show 2 * Real.pi * θ = 2 * (Real.pi * θ) by ring, Real.cos_two_mul, mul_pow, sq_abs]
    linear_combination (-4 : ℝ) * Real.sin_sq_add_cos_sq (Real.pi * θ)
  have h2 : ‖e θ - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * θ)|) ^ 2 := by
    rw [norm_e_sub_one_sq, hcos]
  rw [← Real.sqrt_sq (norm_nonneg (e θ - 1)), h2, Real.sqrt_sq (by positivity)]

/-- **Jordan-type bound**: `2x ≤ sin(πx)` for `x ∈ [0, 1/2]` (from Mathlib's `Real.mul_le_sin`).
    Converts `1/|sin(π(r−r')/q)|` into the harmonic bound `q/(2·min(r−r', q−(r−r')))` — the seed
    of the `O(q log q)` cosecant boundary sum. -/
lemma two_mul_le_sin_pi_mul (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    2 * x ≤ Real.sin (Real.pi * x) := by
  have hpx : Real.pi * x ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left h1 Real.pi_pos.le]
  have h := Real.mul_le_sin (x := Real.pi * x) (by positivity) hpx
  have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
  rwa [heq] at h

/-- **Per-term cosecant lower bound**: `2·min(k,q−k)/q ≤ |sin(πk/q)|` for `0 < k < q`. The
    `sin(π−x)=sin x` symmetry folds the upper half `k > q/2` onto Jordan's inequality for `q−k`. -/
lemma sin_pi_ratio_lower (q k : ℕ) (hq : 0 < q) (hk : 0 < k) (hkq : k < q) :
    (2 : ℝ) * (min k (q - k) : ℕ) / q ≤ |Real.sin (Real.pi * (k : ℝ) / q)| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have helper : ∀ j : ℕ, 2 * j ≤ q → (2 : ℝ) * (j : ℝ) / q ≤ Real.sin (Real.pi * (j : ℝ) / q) := by
    intro j hj2
    have hjR : 2 * (j : ℝ) ≤ (q : ℝ) := by exact_mod_cast hj2
    have hx : (j : ℝ) / q ≤ 1 / 2 := by rw [div_le_div_iff₀ hqR (by norm_num)]; nlinarith [hjR]
    have hjb := two_mul_le_sin_pi_mul ((j : ℝ) / q) (by positivity) hx
    calc (2 : ℝ) * (j : ℝ) / q = 2 * ((j : ℝ) / q) := by ring
      _ ≤ Real.sin (Real.pi * ((j : ℝ) / q)) := hjb
      _ = Real.sin (Real.pi * (j : ℝ) / q) := by rw [mul_div_assoc]
  by_cases hcase : 2 * k ≤ q
  · have hmin : min k (q - k) = k := by omega
    have hkb := helper k hcase
    rw [hmin, abs_of_nonneg (le_trans (by positivity) hkb)]
    exact hkb
  · have hc2 : q < 2 * k := Nat.lt_of_not_le hcase
    have hle : k ≤ q := le_of_lt hkq
    have hqk2 : 2 * (q - k) ≤ q := by omega
    have hmin : min k (q - k) = q - k := by omega
    have hjb := helper (q - k) hqk2
    have hsub : Real.sin (Real.pi * ((q - k : ℕ) : ℝ) / q) = Real.sin (Real.pi * (k : ℝ) / q) := by
      have heq : Real.pi * ((q - k : ℕ) : ℝ) / q = Real.pi - Real.pi * (k : ℝ) / q := by
        rw [Nat.cast_sub hle]; field_simp
      rw [heq, Real.sin_pi_sub]
    rw [hmin]
    rw [hsub] at hjb
    rw [abs_of_nonneg (le_trans (by positivity) hjb)]
    exact hjb

/-- Boundary term in cosecant form: `2/‖e θ − 1‖ = 1/|sin(πθ)|` (both `0` when `sin πθ = 0`). With
    `sin_pi_ratio_lower` this bounds each boundary summand by `q/(2·min(r−r',q−(r−r')))`. -/
lemma two_div_norm_e_sub_one (θ : ℝ) : 2 / ‖e θ - 1‖ = 1 / |Real.sin (Real.pi * θ)| := by
  rw [norm_e_sub_one]
  by_cases h : Real.sin (Real.pi * θ) = 0
  · rw [h]; simp
  · have hne : |Real.sin (Real.pi * θ)| ≠ 0 := abs_ne_zero.mpr h
    rw [mul_comm]; field_simp

/-- **Per-pair boundary bound**: `2/‖e((r−r')/q)−1‖ ≤ q/(2·min(d,q−d))`, `d = |r−r'|`. Combines the
    cosecant form with the Jordan-based `sin_pi_ratio_lower`; the signed `r−r'` reduces via `|sin|`
    evenness. Each interval-boundary summand is thus at most `q/(2·min)`. -/
lemma boundary_summand_bound (q r r' : ℕ) (hq : 0 < q) (hr : r < q) (hr' : r' < q) (hne : r ≠ r') :
    2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖
      ≤ (q : ℝ) / (2 * (min (max r r' - min r r') (q - (max r r' - min r r')) : ℕ)) := by
  set d := max r r' - min r r' with hd
  have hd0 : 0 < d := by omega
  have hdq : d < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hminpos : 0 < min d (q - d) := by omega
  have habs : |Real.sin (Real.pi * (((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / q)|
      = |Real.sin (Real.pi * (d : ℝ) / q)| := by
    rcases Nat.le_total r' r with h | h
    · have he : (((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) = (d : ℝ) := by
        rw [hd, max_eq_left h, min_eq_right h, Nat.cast_sub h]; push_cast; ring
      rw [he]
    · rcases eq_or_lt_of_le h with heq | hlt
      · exact absurd heq hne
      · have he : (((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) = -(d : ℝ) := by
          rw [hd, max_eq_right (le_of_lt hlt), min_eq_left (le_of_lt hlt), Nat.cast_sub (le_of_lt hlt)]
          push_cast; ring
        rw [he, show Real.pi * (-(d : ℝ)) / q = -(Real.pi * (d : ℝ) / q) by ring,
          Real.sin_neg, abs_neg]
  have hlow := sin_pi_ratio_lower q d hq hd0 hdq
  rw [two_div_norm_e_sub_one, ← mul_div_assoc, habs]
  have hspos : (0 : ℝ) < 2 * ((min d (q - d) : ℕ) : ℝ) / q := by
    have : (0 : ℝ) < ((min d (q - d) : ℕ) : ℝ) := by exact_mod_cast hminpos
    positivity
  have hsinpos : 0 < |Real.sin (Real.pi * (d : ℝ) / q)| := lt_of_lt_of_le hspos hlow
  rw [div_le_div_iff₀ hsinpos (by positivity)]
  have h2 : 2 * ((min d (q - d) : ℕ) : ℝ) ≤ |Real.sin (Real.pi * (d : ℝ) / q)| * q :=
    (div_le_iff₀ hqR).mp hlow
  nlinarith [h2]

/-- `∑_{k=1}^{q-1} 1/min(k,q−k) ≤ 2·∑_{k=1}^{q-1} 1/k` — termwise `1/min(a,b) ≤ 1/a+1/b`, then the
    reflection `k ↦ q−k` folds `∑ 1/(q−k)` back to `∑ 1/k`. With `harmonic_le_one_add_log` this
    gives the `O(log q)` needed to keep the cosecant boundary at `O(q² log q)` (summable vs coeffs). -/
lemma min_sum_le (q : ℕ) (hq : 2 ≤ q) :
    ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ 2 * ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (k : ℝ) := by
  have hterm : ∀ k ∈ Finset.Icc 1 (q - 1),
      (1 : ℝ) / ((min k (q - k) : ℕ) : ℝ) ≤ (1 : ℝ) / (k : ℝ) + (1 : ℝ) / ((q - k : ℕ) : ℝ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rcases le_total k (q - k) with h | h
    · rw [min_eq_left h]; have : (0 : ℝ) ≤ 1 / ((q - k : ℕ) : ℝ) := by positivity
      linarith
    · rw [min_eq_right h]; have : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      linarith
  have hreflect : ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((q - k : ℕ) : ℝ)
      = ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (k : ℝ) := by
    refine Finset.sum_nbij' (fun k => q - k) (fun k => q - k) ?_ ?_ ?_ ?_ ?_ <;>
      intro k hk <;> simp only [Finset.mem_Icc] at hk ⊢ <;> first | omega | rfl
  calc ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 (q - 1), ((1 : ℝ) / (k : ℝ) + (1 : ℝ) / ((q - k : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (k : ℝ))
        + ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((q - k : ℕ) : ℝ) := Finset.sum_add_distrib
    _ = 2 * ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (k : ℝ) := by rw [hreflect]; ring

/-- `∑_{k=1}^{q-1} 1/min(k,q−k) ≤ 2(1 + log q)` — `min_sum_le` chained with `harmonic_eq_sum_Icc`
    and `harmonic_le_one_add_log`. The explicit `O(log q)` bound on the per-modulus cosecant sum. -/
lemma min_sum_le_log (q : ℕ) (hq : 2 ≤ q) :
    ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((min k (q - k) : ℕ) : ℝ) ≤ 2 * (1 + Real.log q) := by
  have hharm : ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (k : ℝ) = ((harmonic (q - 1) : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl; intro k _; rw [one_div]
  have hlog := harmonic_le_one_add_log (q - 1)
  have hq1 : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    have : 1 ≤ q - 1 := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlogq : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log hq1
    have : q - 1 ≤ q := by omega
    exact_mod_cast this
  calc ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ 2 * ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (k : ℝ) := min_sum_le q hq
    _ = 2 * ((harmonic (q - 1) : ℚ) : ℝ) := by rw [hharm]
    _ ≤ 2 * (1 + Real.log ((q - 1 : ℕ) : ℝ)) := by linarith [hlog]
    _ ≤ 2 * (1 + Real.log (q : ℝ)) := by linarith [hlogq]

/-- **Erase→min-sum bijection**: `∑_{r'∈(range q)\{r}} 1/min(|r−r'|,q−|r−r'|) = ∑_{m=1}^{q-1} 1/min(m,q−m)`
    via the circular representative `r' ↦ (r−r' mod q)` (`min(|r−r'|,q−|r−r'|)=min(m,q−m)`, a clean
    bijection with NO multiplicity). Lets the per-`r` boundary sum inherit `min_sum_le_log`. -/
lemma erase_min_sum (q r : ℕ) (hq2 : 2 ≤ q) (hr : r < q) :
    ∑ r' ∈ (Finset.range q).erase r,
        (1 : ℝ) / ((min (max r r' - min r r') (q - (max r r' - min r r')) : ℕ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((min m (q - m) : ℕ) : ℝ) := by
  refine Finset.sum_nbij' (fun r' => if r' ≤ r then r - r' else q - (r' - r))
    (fun m => if m ≤ r then r - m else r + q - m) ?_ ?_ ?_ ?_ ?_
  · intro r' hr'; simp only [Finset.mem_erase, Finset.mem_range] at hr'
    simp only [Finset.mem_Icc]; split_ifs with h <;> omega
  · intro m hm; simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_erase, Finset.mem_range]; split_ifs with h <;> omega
  · intro r' hr'; simp only [Finset.mem_erase, Finset.mem_range] at hr'; split_ifs <;> omega
  · intro m hm; simp only [Finset.mem_Icc] at hm; split_ifs <;> omega
  · intro r' hr'; simp only [Finset.mem_erase, Finset.mem_range] at hr'
    have h : min (max r r' - min r r') (q - (max r r' - min r r'))
        = min (if r' ≤ r then r - r' else q - (r' - r))
            (q - (if r' ≤ r then r - r' else q - (r' - r))) := by
      split_ifs <;> omega
    rw [h]

/-- **Per-`r` boundary bound**: `∑_{r'∈U_q\{r}} 2/‖e((r−r')/q)−1‖ ≤ q(1+log q)`. Chains
    `boundary_summand_bound` (per term `≤ q/(2·min)`) → superset `U_q ⊆ range q` → `erase_min_sum`
    → `min_sum_le_log`. The inner sum of the interval boundary. -/
lemma erase_boundary_le (q r : ℕ) (hq2 : 2 ≤ q) (hr : r < q) :
    ∑ r' ∈ ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).erase r,
        2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖
      ≤ (q : ℝ) * (1 + Real.log q) := by
  have hq0 : 0 < q := by omega
  set U := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hU
  set g : ℕ → ℝ := fun r' => (q : ℝ) / (2 * ((min (max r r' - min r r')
    (q - (max r r' - min r r')) : ℕ) : ℝ)) with hg
  calc ∑ r' ∈ U.erase r, 2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖
      ≤ ∑ r' ∈ U.erase r, g r' := by
        apply Finset.sum_le_sum; intro r' hr'
        have hr'q : r' < q :=
          Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr')).1
        have hne : r ≠ r' := (Finset.ne_of_mem_erase hr').symm
        exact boundary_summand_bound q r r' hq0 hr hr'q hne
    _ ≤ ∑ r' ∈ (Finset.range q).erase r, g r' := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.erase_subset_erase r (Finset.filter_subset _ _)
        · intro r' _ _; rw [hg]; positivity
    _ = (q : ℝ) / 2 * ∑ r' ∈ (Finset.range q).erase r,
          (1 : ℝ) / ((min (max r r' - min r r') (q - (max r r' - min r r')) : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r' _; rw [hg]; ring
    _ = (q : ℝ) / 2 * ∑ m ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((min m (q - m) : ℕ) : ℝ) := by
        rw [erase_min_sum q r hq2 hr]
    _ ≤ (q : ℝ) * (1 + Real.log q) := by
        have hml := min_sum_le_log q hq2
        have hqh : (0 : ℝ) ≤ (q : ℝ) / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hml hqh]

end MajorArcMainTerm

open MajorArcMainTerm

/-- **Pointwise Dirichlet-L⁴ bound**: `‖D_N(β)²‖² = ‖D_N(β)‖⁴ ≤ 1/(16|β−round β|⁴)` for `β ∉ ℤ`
    (`sin πβ ≠ 0`). From `exp_sum_bound`. The integrand of the arc-tail L⁴ integral `∫_{tail}|D_N|⁴`
    (`rho_bessel`); on the tail `‖α−c‖ > δ_q`, giving `∫_{|β|>δ_q}|D_N|⁴ ≲ 1/δ_q³`. -/
lemma dirichlet_pow4_pt (N : ℕ) (β : ℝ) (hβ : Real.sin (Real.pi * β) ≠ 0) :
    ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * β)) ^ 2‖ ^ 2 ≤ 1 / (16 * |β - round β| ^ 4) := by
  have hb := exp_sum_bound β hβ N
  have hnorm : ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * β)) ^ 2‖ ^ 2
      = ‖∑ k ∈ Finset.range N, e ((k : ℝ) * β)‖ ^ 4 := by
    rw [norm_pow]; ring
  rw [hnorm]
  have h4 : ‖∑ k ∈ Finset.range N, e ((k : ℝ) * β)‖ ^ 4 ≤ (1 / (2 * |β - round β|)) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 4
  refine le_trans h4 (le_of_eq ?_)
  rw [div_pow, one_pow, mul_pow]
  norm_num

set_option maxHeartbeats 1000000
open Finset


/-- **harc brick B0: the squarefree totient seed for the arc-tail diagonal** —
    `(q:ℝ) ≤ 4·φ(q)²` for squarefree `q` (from `sqfree_totient` via `q ≤ q^{6/5}`). -/
lemma sqfree_totient_linear (q : ℕ) (hq : Squarefree q) :
    (q : ℝ) ≤ 4 * (Nat.totient q : ℝ) ^ 2 := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (q : ℝ) ^ ((6 : ℝ) / 5) :=
        Real.rpow_le_rpow_of_exponent_le hq1R (by norm_num)
    _ ≤ 4 * (Nat.totient q : ℝ) ^ 2 := sqfree_totient q hq


end GoldbachChain
