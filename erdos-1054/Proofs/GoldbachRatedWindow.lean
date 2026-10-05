module

public import GoldbachCircleBase
public import GoldbachSW3

@[expose] public section

set_option maxHeartbeats 4000000

namespace GoldbachChain

open MinorArc

set_option maxHeartbeats 1000000
open scoped ArithmeticFunction

-- ===== duplicated defs (verbatim from MinorArcExpSum.lean) =====



section CrossFileInputs

/-- Alias of the fully machine-verified `siegel_walfisz_proven` (SiegelWalfiszMaster gate,
    `#print axioms = [propext, Classical.choice, Quot.sound]`). -/
theorem siegel_walfisz (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log X ^ (B : ℝ) →
    ∀ a : ZMod q, IsUnit a →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), if a = ((n : ZMod q)) then Λ n else 0)
      - X / q.totient| ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10)) :=
  siegel_walfisz_proven B hB



end CrossFileInputs

-- ===== Phase-C numerics =====

/-- `x ≤ exp(x/8)` once `256 ≤ x` (via `(x/16+1)² ≥ x²/256 ≥ x`). -/
lemma self_le_exp_eighth {x : ℝ} (hx : 256 ≤ x) : x ≤ Real.exp (x / 8) := by
  have h2 := Real.add_one_le_exp (x/16)
  have h1 : Real.exp (x/8) = Real.exp (x/16) * Real.exp (x/16) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (x/16 + 1) * (x/16 + 1) ≤ Real.exp (x/16) * Real.exp (x/16) := by
    have h4 : (0:ℝ) ≤ x/16 + 1 := by linarith
    exact mul_le_mul h2 h2 h4 (Real.exp_pos _).le
  rw [h1]
  nlinarith [h3, mul_nonneg (show (0:ℝ) ≤ x from by linarith)
    (show (0:ℝ) ≤ x - 256 from by linarith)]

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Rated progression bound, unit residues** (brick C1a): uniformly for
    `q ≤ (log N)^B` and coprime `r < q`, every initial segment `t ≤ N` of the
    progression Λ-sum is within `C·N·exp(−c(log N)^{1/10})` of `t/φ(q)`.
    Route: `siegel_walfisz` at exponent `2B` (the window survives `t ≥ √N`,
    where `log t ≥ (log N)/2`) + √N head/tail split (the head is trivially
    `≤ 4√N·log N`, beaten by the exponential margin). -/
theorem rated_progression_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ r : ℕ, r < q → Nat.gcd r q = 1 →
    ∀ t : ℕ, t ≤ N →
    ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
      - (t : ℂ) * (1 / (q.totient : ℂ))‖
      ≤ C * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, X₀, hSW⟩ := siegel_walfisz (2*B) (by linarith)
  refine ⟨c/2, C + 6, by positivity, by positivity, ?_⟩
  obtain ⟨Λ₂, hΛ₂def⟩ : ∃ x : ℝ, x = 256 + (4*c+1)^(10:ℕ) + 4 := ⟨_, rfl⟩
  have hΛ₂256 : 256 ≤ Λ₂ := by
    rw [hΛ₂def]
    have h1 : (0:ℝ) ≤ (4*c+1)^(10:ℕ) := by positivity
    linarith
  refine ⟨max (⌈Real.exp Λ₂⌉₊ + 2) (⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ + 2), ?_⟩
  intro N hN₀ q hq0 hqB r hrq hgcd t htN
  haveI : NeZero q := ⟨hq0.ne'⟩
  -- ===== scale facts =====
  have hNexp : ⌈Real.exp Λ₂⌉₊ + 2 ≤ N := le_trans (le_max_left _ _) hN₀
  have hNX₀ : ⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ + 2 ≤ N := le_trans (le_max_right _ _) hN₀
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h1 : 1 ≤ N := by omega
    exact_mod_cast h1
  have hNR : Real.exp Λ₂ ≤ (N:ℝ) := by
    have h1 : (⌈Real.exp Λ₂⌉₊ : ℝ) ≤ (N:ℝ) := by
      have h2 : ⌈Real.exp Λ₂⌉₊ ≤ N := by omega
      exact_mod_cast h2
    linarith [Nat.le_ceil (Real.exp Λ₂)]
  have hlogN : Λ₂ ≤ Real.log N := by
    calc Λ₂ = Real.log (Real.exp Λ₂) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNR
  have hlogN4 : (4:ℝ) ≤ Real.log N := by linarith
  have hlogN0 : (0:ℝ) < Real.log N := by linarith
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log N ^ ((1:ℝ)/10) := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    rw [hLdef]
    exact Real.rpow_pos_of_pos hlogN0 _
  have hLpow : L ^ (10:ℕ) = Real.log N := by
    rw [hLdef, ← Real.rpow_natCast (Real.log N ^ ((1:ℝ)/10)) 10,
      ← Real.rpow_mul hlogN0.le]
    norm_num
  have hL256 : 256 ≤ L ^ (10:ℕ) := by rw [hLpow]; linarith
  have hL4c : 4*c + 1 ≤ L := by
    by_contra hcon
    push_neg at hcon
    have h1 : L ^ (10:ℕ) < (4*c+1) ^ (10:ℕ) :=
      pow_lt_pow_left₀ hcon hL0.le (by norm_num)
    have h2 : (0:ℝ) ≤ (4*c+1)^(10:ℕ) := by positivity
    rw [hLpow] at h1
    rw [hΛ₂def] at hlogN
    linarith
  have hL1 : 1 ≤ L := by
    have h1 : (0:ℝ) ≤ 4*c := by positivity
    linarith
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt N := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hN1
  have hsqrtX₀ : max X₀ 0 + 1 ≤ Real.sqrt N := by
    have h1 : ((max X₀ 0 + 2)^(2:ℕ) : ℝ) ≤ (N:ℝ) := by
      have h2 : (⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ : ℝ) ≤ (N:ℝ) := by
        have h3 : ⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ ≤ N := by omega
        exact_mod_cast h3
      linarith [Nat.le_ceil ((max X₀ 0 + 2)^(2:ℕ))]
    have h4 : (0:ℝ) ≤ max X₀ 0 + 2 := by
      have h5 := le_max_right X₀ (0:ℝ)
      linarith
    have h6 : max X₀ 0 + 2 ≤ Real.sqrt N := by
      rw [show max X₀ 0 + 2 = Real.sqrt ((max X₀ 0 + 2)^(2:ℕ)) from
        (Real.sqrt_sq h4).symm]
      exact Real.sqrt_le_sqrt h1
    linarith
  have hlogsqrt : Real.log (Real.sqrt N) = Real.log N / 2 :=
    Real.log_sqrt (by positivity)
  have hE0 : (0:ℝ) < Real.exp (-(c/2) * L) := Real.exp_pos _
  have hEbig : 1 ≤ (N:ℝ) * Real.exp (-(c/2) * L) := by
    have h1 : Real.exp ((c/2) * L) ≤ (N:ℝ) := by
      have h2 : (c/2) * L ≤ L ^ (10:ℕ) := by
        have h4 : c/2 ≤ L ^ (9:ℕ) := by
          have h5 : L ≤ L ^ (9:ℕ) := le_self_pow₀ hL1 (by norm_num)
          linarith
        have h3 : (c/2) * L ≤ (L^(9:ℕ)) * L :=
          mul_le_mul_of_nonneg_right h4 hL0.le
        have h6 : (L^(9:ℕ)) * L = L ^ (10:ℕ) := by ring
        linarith
      calc Real.exp ((c/2) * L) ≤ Real.exp (L ^ (10:ℕ)) := Real.exp_le_exp.mpr h2
        _ = (N:ℝ) := by rw [hLpow]; exact Real.exp_log (by linarith)
    calc (1:ℝ) = Real.exp ((c/2) * L) * Real.exp (-(c/2) * L) := by
          rw [← Real.exp_add]
          simp
      _ ≤ (N:ℝ) * Real.exp (-(c/2) * L) :=
          mul_le_mul_of_nonneg_right h1 hE0.le
  -- ===== split at √N =====
  rcases lt_or_ge ((t:ℝ) - 1) (Real.sqrt N) with hhead | htail
  · -- HEAD: trivial bound 4√N·log N
    have hsum_le : ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
        ≤ (t:ℝ) * Real.log N := by
      calc ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
          ≤ ∑ n ∈ Finset.range t, Λ n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro n _ _
            exact ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ ∑ _n ∈ Finset.range t, Real.log N := by
            apply Finset.sum_le_sum
            intro n hn
            rcases Nat.eq_zero_or_pos n with rfl | hn0
            · rw [show Λ 0 = 0 from ArithmeticFunction.map_zero]
              linarith
            · calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
                _ ≤ Real.log N := by
                    apply Real.log_le_log (by exact_mod_cast hn0)
                    rw [Finset.mem_range] at hn
                    have h1 : n ≤ N := by omega
                    exact_mod_cast h1
        _ = (t:ℝ) * Real.log N := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    have hsum_nn : (0:ℝ) ≤ ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n :=
      Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hφ1 : (1:ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hcast : ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
        - (t : ℂ) * (1 / (q.totient : ℂ))‖
        = |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - (t:ℝ) * (1 / (q.totient : ℝ))| := by
      rw [show (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
          - (t : ℂ) * (1 / (q.totient : ℂ))
          = ((((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - (t:ℝ) * (1 / (q.totient : ℝ)) : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hcast]
    have htR : (t:ℝ) ≤ Real.sqrt N + 1 := by linarith
    have habs : |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
        - (t:ℝ) * (1 / (q.totient : ℝ))| ≤ 4 * Real.sqrt N * Real.log N := by
      rw [abs_le]
      have h2 : (t:ℝ) ≤ 2 * Real.sqrt N := by linarith [hsqrt1]
      constructor
      · have h1 : (t:ℝ) * (1 / (q.totient : ℝ)) ≤ (t:ℝ) := by
          rw [mul_one_div]
          apply div_le_self (by positivity) hφ1
        nlinarith [hsqrt1, hlogN4]
      · have h3 : (t:ℝ) * Real.log N ≤ 2 * Real.sqrt N * Real.log N :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
        have h4 : (0:ℝ) ≤ (t:ℝ) * (1 / (q.totient : ℝ)) := by positivity
        linarith [hsum_le]
    refine habs.trans ?_
    have hkey : 4 * Real.log N * Real.exp ((c/2) * L) ≤ Real.sqrt N := by
      have h1 : Real.sqrt N = Real.exp (L ^ (10:ℕ) / 2) := by
        rw [hLpow, ← hlogsqrt]
        exact (Real.exp_log (by positivity)).symm
      have h4exp : (4:ℝ) ≤ Real.exp (L ^ (10:ℕ) / 8) := by
        have h2 : (4:ℝ) ≤ L ^ (10:ℕ) / 8 := by linarith
        have h3 := Real.add_one_le_exp (L ^ (10:ℕ) / 8)
        linarith
      have hlogexp : Real.log N ≤ Real.exp (L ^ (10:ℕ) / 8) := by
        rw [← hLpow]
        exact self_le_exp_eighth hL256
      have hcLexp : Real.exp ((c/2) * L) ≤ Real.exp (L ^ (10:ℕ) / 8) := by
        apply Real.exp_le_exp.mpr
        have h6 : L ≤ L ^ (9:ℕ) := le_self_pow₀ hL1 (by norm_num)
        have h5 : (c/2) * L ≤ (L^(9:ℕ)/8) * L := by
          apply mul_le_mul_of_nonneg_right ?_ hL0.le
          linarith [hL4c]
        have h7 : (L^(9:ℕ)/8) * L = L ^ (10:ℕ) / 8 := by ring
        linarith
      calc 4 * Real.log N * Real.exp ((c/2) * L)
          ≤ Real.exp (L ^ (10:ℕ) / 8) * Real.exp (L ^ (10:ℕ) / 8)
            * Real.exp (L ^ (10:ℕ) / 8) := by
            apply mul_le_mul ?_ hcLexp (Real.exp_pos _).le (by positivity)
            exact mul_le_mul h4exp hlogexp (by linarith) (Real.exp_pos _).le
        _ = Real.exp (3 * (L ^ (10:ℕ) / 8)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp (L ^ (10:ℕ) / 2) := by
            apply Real.exp_le_exp.mpr
            have h8 : (0:ℝ) ≤ L ^ (10:ℕ) := by positivity
            linarith
        _ = Real.sqrt N := h1.symm
    have hNsq : Real.sqrt N * Real.sqrt N = (N:ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc 4 * Real.sqrt N * Real.log N
        = (4 * Real.log N * Real.exp ((c/2) * L)) * Real.sqrt N
          * Real.exp (-(c/2) * L) := by
          rw [show (4 * Real.log N * Real.exp ((c/2) * L)) * Real.sqrt N
              * Real.exp (-(c/2) * L)
              = 4 * Real.log N * Real.sqrt N
                * (Real.exp ((c/2) * L) * Real.exp (-(c/2) * L)) from by ring,
            ← Real.exp_add]
          simp
          ring
      _ ≤ Real.sqrt N * Real.sqrt N * Real.exp (-(c/2) * L) := by
          apply mul_le_mul_of_nonneg_right ?_ hE0.le
          apply mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (N:ℝ) * Real.exp (-(c/2) * L) := by rw [hNsq]
      _ ≤ (C + 6) * (N:ℝ) * Real.exp (-(c/2) * L) := by
          have h9 : (0:ℝ) ≤ (N:ℝ) * Real.exp (-(c/2) * L) := by positivity
          nlinarith
      _ = (C + 6) * (N:ℝ) * Real.exp (-(c/2) * Real.log N ^ ((1:ℝ)/10)) := by
          rw [hLdef]
  · -- TAIL: siegel_walfisz at X := t − 1
    have ht1 : 1 ≤ t := by
      by_contra hcon
      push_neg at hcon
      have h1 : t = 0 := by omega
      rw [h1] at htail
      simp only [Nat.cast_zero, zero_sub] at htail
      linarith [hsqrt1]
    have hXX₀ : X₀ ≤ (t:ℝ) - 1 := by
      have h1 := le_max_left X₀ (0:ℝ)
      linarith [hsqrtX₀, htail]
    have hlogt : Real.log N / 2 ≤ Real.log ((t:ℝ) - 1) := by
      rw [← hlogsqrt]
      apply Real.log_le_log (by linarith [hsqrt1]) htail
    have hqB2 : (q:ℝ) ≤ Real.log ((t:ℝ) - 1) ^ ((2*B : ℝ)) := by
      have h2 : (Real.log N / 2) ^ ((2*B : ℝ))
          = Real.log N ^ ((2*B:ℝ)) / 2 ^ ((2*B:ℝ)) :=
        Real.div_rpow (by linarith) (by norm_num) _
      have h1 : Real.log N ^ (B:ℝ) ≤ (Real.log N / 2) ^ ((2*B : ℝ)) := by
        rw [h2, le_div_iff₀ (by positivity)]
        have h3 : (2:ℝ) ^ ((2*B:ℝ)) ≤ Real.log N ^ (B:ℝ) := by
          have h31 : (2:ℝ) ^ ((2*B:ℝ)) = ((2:ℝ)^(2:ℕ)) ^ (B:ℝ) := by
            rw [← Real.rpow_natCast (2:ℝ) 2, ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h31, show ((2:ℝ)^(2:ℕ)) = (4:ℝ) from by norm_num]
          exact Real.rpow_le_rpow (by norm_num) hlogN4 (by linarith)
        have h4 : Real.log N ^ (B:ℝ) * Real.log N ^ (B:ℝ)
            = Real.log N ^ ((2*B:ℝ)) := by
          rw [← Real.rpow_add hlogN0]
          congr 1
          ring
        calc Real.log N ^ (B:ℝ) * 2 ^ ((2*B:ℝ))
            ≤ Real.log N ^ (B:ℝ) * Real.log N ^ (B:ℝ) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = Real.log N ^ ((2*B:ℝ)) := h4
      have h5 : (Real.log N / 2) ^ ((2*B : ℝ)) ≤ Real.log ((t:ℝ) - 1) ^ ((2*B : ℝ)) :=
        Real.rpow_le_rpow (by linarith) hlogt (by linarith)
      linarith [hqB]
    have hunit : IsUnit ((r : ZMod q)) := (ZMod.isUnit_iff_coprime r q).mpr hgcd
    have hSW' := hSW ((t:ℝ) - 1) hXX₀ q hqB2 ((r : ZMod q)) hunit
    have hXdef : ((t:ℝ) - 1) = (((t - 1 : ℕ)):ℝ) := by
      have h1 := Nat.cast_sub ht1 (R := ℝ)
      rw [h1]
      norm_num
    have hfloor : ⌊(t:ℝ) - 1⌋₊ + 1 = t := by
      rw [hXdef, Nat.floor_natCast]
      omega
    rw [hfloor] at hSW'
    have hbridge : (∑ n ∈ Finset.range t,
        if ((r : ZMod q)) = ((n : ZMod q)) then Λ n else 0)
        = ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      have h1 : (((r : ZMod q)) = ((n : ZMod q))) ↔ (n % q = r) := by
        rw [ZMod.natCast_eq_natCast_iff]
        constructor
        · intro h2
          have h3 : n % q = r % q := (Nat.ModEq.symm h2)
          rwa [Nat.mod_eq_of_lt hrq] at h3
        · intro h2
          have h3 : n % q = r % q := by rw [Nat.mod_eq_of_lt hrq]; exact h2
          exact Nat.ModEq.symm h3
      simp only [h1]
    rw [hbridge] at hSW'
    have hcast : ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
        - (t : ℂ) * (1 / (q.totient : ℂ))‖
        = |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - (t:ℝ) * (1 / (q.totient : ℝ))| := by
      rw [show (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
          - (t : ℂ) * (1 / (q.totient : ℂ))
          = ((((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - (t:ℝ) * (1 / (q.totient : ℝ)) : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hcast]
    have hφ1 : (1:ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hoffby : |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
        - (t:ℝ) * (1 / (q.totient : ℝ))|
        ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - ((t:ℝ) - 1) / (q.totient : ℝ)| + 1 := by
      have h1 : |((t:ℝ) - 1) / (q.totient : ℝ) - (t:ℝ) * (1 / (q.totient : ℝ))|
          ≤ 1 := by
        have hφ0 : (q.totient : ℝ) ≠ 0 := by linarith
        rw [show ((t:ℝ) - 1) / (q.totient : ℝ) - (t:ℝ) * (1 / (q.totient : ℝ))
            = -(1 / (q.totient : ℝ)) from by field_simp; ring,
          abs_neg, abs_of_pos (by positivity), div_le_one (by linarith)]
        exact hφ1
      calc |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
          - (t:ℝ) * (1 / (q.totient : ℝ))|
          = |((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - ((t:ℝ) - 1) / (q.totient : ℝ))
            + (((t:ℝ) - 1) / (q.totient : ℝ)
              - (t:ℝ) * (1 / (q.totient : ℝ)))| := by
            congr 1
            ring
        _ ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - ((t:ℝ) - 1) / (q.totient : ℝ)|
            + |((t:ℝ) - 1) / (q.totient : ℝ) - (t:ℝ) * (1 / (q.totient : ℝ))| :=
            abs_add_le _ _
        _ ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - ((t:ℝ) - 1) / (q.totient : ℝ)| + 1 := by linarith
    have hrate : Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10))
        ≤ Real.exp (-(c/2) * L) := by
      apply Real.exp_le_exp.mpr
      have h1 : (Real.log N / 2) ^ ((1:ℝ)/10) ≤ Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10) :=
        Real.rpow_le_rpow (by linarith) hlogt (by norm_num)
      have h3 : (Real.log N / 2) ^ ((1:ℝ)/10)
          = Real.log N ^ ((1:ℝ)/10) * ((1:ℝ)/2) ^ ((1:ℝ)/10) := by
        rw [show Real.log N / 2 = Real.log N * ((1:ℝ)/2) from by ring,
          Real.mul_rpow (by linarith) (by norm_num)]
      have h5 : ((1:ℝ)/2) ≤ ((1:ℝ)/2) ^ ((1:ℝ)/10) := by
        nth_rewrite 1 [show ((1:ℝ)/2) = ((1:ℝ)/2) ^ ((1:ℝ)) from
          (Real.rpow_one _).symm]
        apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        norm_num
      have h2 : ((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/10)
          ≤ (Real.log N / 2) ^ ((1:ℝ)/10) := by
        rw [h3]
        calc ((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/10)
            ≤ ((1:ℝ)/2) ^ ((1:ℝ)/10) * Real.log N ^ ((1:ℝ)/10) :=
              mul_le_mul_of_nonneg_right h5 (by positivity)
          _ = Real.log N ^ ((1:ℝ)/10) * ((1:ℝ)/2) ^ ((1:ℝ)/10) := by ring
      have h6 : c * (((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/10))
          ≤ c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10) := by
        apply mul_le_mul_of_nonneg_left ?_ hc0.le
        linarith
      rw [hLdef]
      nlinarith [h6]
    have hfin : C * ((t:ℝ) - 1) * Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10))
        ≤ C * (N:ℝ) * Real.exp (-(c/2) * L) := by
      have h1 : (t:ℝ) - 1 ≤ (N:ℝ) := by
        have h2 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
        linarith
      calc C * ((t:ℝ) - 1) * Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10))
          ≤ C * ((t:ℝ) - 1) * Real.exp (-(c/2) * L) := by
            apply mul_le_mul_of_nonneg_left hrate ?_
            have h4 : (0:ℝ) ≤ (t:ℝ) - 1 := by linarith [hsqrt1, htail]
            positivity
        _ ≤ C * (N:ℝ) * Real.exp (-(c/2) * L) := by
            apply mul_le_mul_of_nonneg_right ?_ hE0.le
            apply mul_le_mul_of_nonneg_left h1 hC0.le
    calc |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
        - (t:ℝ) * (1 / (q.totient : ℝ))|
        ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - ((t:ℝ) - 1) / (q.totient : ℝ)| + 1 := hoffby
      _ ≤ C * ((t:ℝ) - 1) * Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10)) + 1 := by
          linarith [hSW']
      _ ≤ C * (N:ℝ) * Real.exp (-(c/2) * L) + (N:ℝ) * Real.exp (-(c/2) * L) := by
          linarith [hfin, hEbig]
      _ ≤ (C + 6) * (N:ℝ) * Real.exp (-(c/2) * L) := by
          have h9 : (0:ℝ) ≤ (N:ℝ) * Real.exp (-(c/2) * L) := by positivity
          nlinarith
      _ = (C + 6) * (N:ℝ) * Real.exp (-(c/2) * Real.log N ^ ((1:ℝ)/10)) := by
          rw [hLdef]

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Rated progression bound, non-unit residues** (brick C1b): for `gcd(r,q) ≠ 1`
    the progression Λ-mass sits on prime powers `p^k` with `p ∣ q`; per prime it
    telescopes to `≤ log N`, so every initial segment is `≤ q·log N` — no
    Siegel–Walfisz needed. -/
theorem nonunit_progression_bound (q : ℕ) (hq0 : 0 < q) (r : ℕ)
    (hgcd : Nat.gcd r q ≠ 1) (N : ℕ) (hN : 3 ≤ N) (t : ℕ) (ht : t ≤ N) :
    ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
      ≤ (q:ℝ) * Real.log N := by
  classical
  have hN0 : (0:ℝ) < (N:ℝ) := by
    have h1 : 0 < N := by omega
    exact_mod_cast h1
  have hlogN0 : (0:ℝ) ≤ Real.log N := by
    apply Real.log_nonneg
    have h1 : 1 ≤ N := by omega
    exact_mod_cast h1
  -- restrict to prime powers
  have hstep : ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
      = ∑ n ∈ (Finset.range t).filter
          (fun n : ℕ => n % q = r ∧ IsPrimePow n), Λ n := by
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h1 : n % q = r
    · by_cases h2 : IsPrimePow n
      · simp [h1, h2]
      · have h3 : Λ n = 0 := by
          rw [ArithmeticFunction.vonMangoldt_apply, if_neg h2]
        simp [h1, h2, h3]
    · simp [h1]
  rw [hstep]
  -- membership facts
  have hEmem : ∀ n ∈ (Finset.range t).filter
      (fun n : ℕ => n % q = r ∧ IsPrimePow n),
      n.minFac ∈ q.primeFactors ∧ 1 ≤ n.factorization n.minFac ∧
      n.minFac ^ n.factorization n.minFac = n ∧
      n.factorization n.minFac ≤ N := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnt, hnr, hpp⟩ := hn
    have hrec := hpp.minFac_pow_factorization_eq
    have hn1 : n ≠ 1 := hpp.ne_one
    have hn0 : 0 < n := hpp.pos
    have hpmin : n.minFac.Prime := Nat.minFac_prime hn1
    -- the common prime of gcd(r,q) divides n, hence equals minFac n, hence ∣ q
    have hg0 : Nat.gcd r q ≠ 0 := by
      intro h
      exact hq0.ne' (Nat.eq_zero_of_gcd_eq_zero_right h)
    have hp₀ : (Nat.gcd r q).minFac.Prime := Nat.minFac_prime hgcd
    have hp₀r : (Nat.gcd r q).minFac ∣ r :=
      (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left r q)
    have hp₀q : (Nat.gcd r q).minFac ∣ q :=
      (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right r q)
    have hp₀n : (Nat.gcd r q).minFac ∣ n := by
      have h1 : n = q * (n / q) + r := by
        rw [← hnr]
        exact (Nat.div_add_mod n q).symm
      rw [h1]
      exact Nat.dvd_add (Dvd.dvd.mul_right hp₀q _) hp₀r
    have hrp : (Nat.gcd r q).minFac = n.minFac := by
      have h4 : (Nat.gcd r q).minFac ∣ n.minFac ^ n.factorization n.minFac := by
        rw [hrec]
        exact hp₀n
      have h5 : (Nat.gcd r q).minFac ∣ n.minFac := hp₀.dvd_of_dvd_pow h4
      exact (Nat.prime_dvd_prime_iff_eq hp₀ hpmin).mp h5
    have hpq : n.minFac ∣ q := hrp ▸ hp₀q
    have hk1 : 1 ≤ n.factorization n.minFac := by
      by_contra hcon
      push_neg at hcon
      have h0 : n.factorization n.minFac = 0 := by omega
      rw [h0, pow_zero] at hrec
      exact hn1 hrec.symm
    have hkN : n.factorization n.minFac ≤ N := by
      have h6 : n.factorization n.minFac ≤ n := by
        calc n.factorization n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
              (Nat.lt_pow_self hpmin.one_lt).le
          _ = n := hrec
      omega
    exact ⟨Nat.mem_primeFactors.mpr ⟨hpmin, hpq, hq0.ne'⟩, hk1, hrec, hkN⟩
  -- inject into (prime factor, exponent) pairs
  have hinj : Set.InjOn (fun n : ℕ => (n.minFac, n.factorization n.minFac))
      ((Finset.range t).filter (fun n : ℕ => n % q = r ∧ IsPrimePow n)) := by
    intro a ha b hb hab
    obtain ⟨-, -, hreca, -⟩ := hEmem a (Finset.mem_coe.mp ha)
    obtain ⟨-, -, hrecb, -⟩ := hEmem b (Finset.mem_coe.mp hb)
    simp only [Prod.mk.injEq] at hab
    calc a = a.minFac ^ a.factorization a.minFac := hreca.symm
      _ = b.minFac ^ b.factorization b.minFac := by rw [hab.2, hab.1]
      _ = b := hrecb
  have hval : ∀ n ∈ (Finset.range t).filter
      (fun n : ℕ => n % q = r ∧ IsPrimePow n),
      Λ n = Real.log n.minFac := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn.2.2]
  obtain ⟨IMG, hIMGdef⟩ : ∃ s : Finset (ℕ × ℕ),
      s = ((Finset.range t).filter
        (fun n : ℕ => n % q = r ∧ IsPrimePow n)).image
          (fun n => (n.minFac, n.factorization n.minFac)) := ⟨_, rfl⟩
  have hsub : IMG ⊆ (q.primeFactors ×ˢ Finset.Icc 1 N).filter
      (fun pk => (pk.1 : ℝ) ^ pk.2 ≤ (N:ℝ)) := by
    rw [hIMGdef]
    intro pk hpk
    rw [Finset.mem_image] at hpk
    obtain ⟨n, hn, hen⟩ := hpk
    obtain ⟨hp, hk1, hrec, hkN⟩ := hEmem n hn
    rw [Finset.mem_filter, Finset.mem_product, ← hen]
    have hnN : (n : ℝ) ≤ (N:ℝ) := by
      rw [Finset.mem_filter, Finset.mem_range] at hn
      have h7 : n ≤ N := by omega
      exact_mod_cast h7
    refine ⟨⟨hp, Finset.mem_Icc.mpr ⟨hk1, hkN⟩⟩, ?_⟩
    have h8 : ((n.minFac ^ n.factorization n.minFac : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hrec
    push_cast at h8
    rw [h8]
    exact hnN
  calc ∑ n ∈ (Finset.range t).filter
        (fun n : ℕ => n % q = r ∧ IsPrimePow n), Λ n
      = ∑ n ∈ (Finset.range t).filter
          (fun n : ℕ => n % q = r ∧ IsPrimePow n),
          Real.log n.minFac := Finset.sum_congr rfl hval
    _ = ∑ pk ∈ IMG, Real.log pk.1 := by
        rw [hIMGdef]
        exact (Finset.sum_image (f := fun pk => Real.log pk.1) hinj).symm
    _ ≤ ∑ pk ∈ (q.primeFactors ×ˢ Finset.Icc 1 N).filter
          (fun pk => (pk.1 : ℝ) ^ pk.2 ≤ (N:ℝ)), Real.log pk.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro pk hpk _
        rw [Finset.mem_filter, Finset.mem_product, Nat.mem_primeFactors] at hpk
        exact Real.log_nonneg (by exact_mod_cast hpk.1.1.1.one_lt.le)
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ (Finset.Icc 1 N).filter
          (fun k => (p : ℝ) ^ k ≤ (N:ℝ)), Real.log p := by
        rw [Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_filter]
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log N := by
        apply Finset.sum_le_sum
        intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hlogp0 : (0:ℝ) < Real.log p := by
          apply Real.log_pos
          exact_mod_cast hpprime.one_lt
        rw [Finset.sum_const, nsmul_eq_mul]
        obtain ⟨K, hKdef⟩ : ∃ m : ℕ, m = ⌊Real.log N / Real.log p⌋₊ := ⟨_, rfl⟩
        have hsubK : (Finset.Icc 1 N).filter (fun k => (p : ℝ) ^ k ≤ (N:ℝ))
            ⊆ Finset.Icc 1 K := by
          intro k hk
          rw [Finset.mem_filter, Finset.mem_Icc] at hk
          rw [Finset.mem_Icc]
          refine ⟨hk.1.1, ?_⟩
          rw [hKdef]
          apply Nat.le_floor
          rw [le_div_iff₀ hlogp0]
          calc (k : ℝ) * Real.log p = Real.log ((p : ℝ) ^ k) := by
                rw [Real.log_pow]
            _ ≤ Real.log N := Real.log_le_log
                (pow_pos (by exact_mod_cast hpprime.pos) k) hk.2
        have hcard2 : ((Finset.Icc 1 N).filter
            (fun k => (p : ℝ) ^ k ≤ (N:ℝ))).card ≤ K := by
          calc ((Finset.Icc 1 N).filter
              (fun k => (p : ℝ) ^ k ≤ (N:ℝ))).card ≤ (Finset.Icc 1 K).card :=
                Finset.card_le_card hsubK
            _ = K := by rw [Nat.card_Icc]; omega
        have hK : (K : ℝ) * Real.log p ≤ Real.log N := by
          rw [hKdef]
          have h9 : ((⌊Real.log N / Real.log p⌋₊ : ℝ)) ≤ Real.log N / Real.log p :=
            Nat.floor_le (by positivity)
          calc ((⌊Real.log N / Real.log p⌋₊ : ℝ)) * Real.log p
              ≤ (Real.log N / Real.log p) * Real.log p :=
                mul_le_mul_of_nonneg_right h9 hlogp0.le
            _ = Real.log N := by field_simp
        calc (((Finset.Icc 1 N).filter
            (fun k => (p : ℝ) ^ k ≤ (N:ℝ))).card : ℝ) * Real.log p
            ≤ (K : ℝ) * Real.log p := by
              apply mul_le_mul_of_nonneg_right ?_ hlogp0.le
              exact_mod_cast hcard2
          _ ≤ Real.log N := hK
    _ = (q.primeFactors.card : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) * Real.log N := by
        apply mul_le_mul_of_nonneg_right ?_ hlogN0
        have h10 : q.primeFactors ⊆ Finset.Icc 2 q := by
          intro p hp
          rw [Nat.mem_primeFactors] at hp
          rw [Finset.mem_Icc]
          exact ⟨hp.1.two_le, Nat.le_of_dvd hq0 hp.2.1⟩
        calc (q.primeFactors.card : ℝ) ≤ ((Finset.Icc 2 q).card : ℝ) := by
              exact_mod_cast Finset.card_le_card h10
          _ ≤ (q : ℝ) := by
              rw [Nat.card_Icc]
              have h11 : q + 1 - 2 ≤ q := by omega
              exact_mod_cast h11

-- duplicated from MinorArcExpSum.lean (deduped at the Phase-F concatenation)

open Finset in
set_option maxHeartbeats 4000000 in
/-- **The rated uniform window bound** (brick C1c = plan item C1, Phase C core):
    uniformly for `q ≤ (log N)^B`, every Farey-window evaluation of `∑Λ(n)e(nα)`
    against its `μ/φ`-model window carries an `exp(−c(log N)^{1/10})` rate:
    `‖∑_{n<N}Λ(n)e(n(a/q+β)) − S_q(a)·∑_{n<N}e(nβ)‖ ≤ C·q·N·exp(−c(log N)^{1/10})·(1+2πN|β|)`.
    This is the input Phase D feeds to the major-arc L² computation. -/
theorem rated_window_eval (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ a : ℤ, ∀ β : ℝ,
    ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
      - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
        * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
    ≤ C * q * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
      * (1 + 2 * Real.pi * N * |β|) := by
  obtain ⟨c, C, hc0, hC0, N₁, hC1a⟩ := rated_progression_bound B hB
  refine ⟨c, C + 1, hc0, by positivity, ?_⟩
  obtain ⟨Λ₃, hΛ₃def⟩ : ∃ x : ℝ, x = (30*B + c + 1)^(10:ℕ) + 4 := ⟨_, rfl⟩
  have hΛ₃0 : 0 < Λ₃ := by
    rw [hΛ₃def]
    positivity
  refine ⟨max N₁ (⌈Real.exp Λ₃⌉₊ + 3), ?_⟩
  intro N hN₀ q hq0 hqB a β
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN₀
  have hNe : ⌈Real.exp Λ₃⌉₊ + 3 ≤ N := le_trans (le_max_right _ _) hN₀
  have hN3 : 3 ≤ N := by omega
  have hN0 : (0:ℝ) < (N:ℝ) := by
    have h1 : 0 < N := by omega
    exact_mod_cast h1
  have hNR : Real.exp Λ₃ ≤ (N:ℝ) := by
    have h1 : (⌈Real.exp Λ₃⌉₊ : ℝ) ≤ (N:ℝ) := by
      have h2 : ⌈Real.exp Λ₃⌉₊ ≤ N := by omega
      exact_mod_cast h2
    linarith [Nat.le_ceil (Real.exp Λ₃)]
  have hlogN : Λ₃ ≤ Real.log N := by
    calc Λ₃ = Real.log (Real.exp Λ₃) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNR
  have hlogN4 : (4:ℝ) ≤ Real.log N := by
    rw [hΛ₃def] at hlogN
    have h1 : (0:ℝ) ≤ (30*B + c + 1)^(10:ℕ) := by positivity
    linarith
  have hlogN0 : (0:ℝ) < Real.log N := by linarith
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log N ^ ((1:ℝ)/10) := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    rw [hLdef]
    exact Real.rpow_pos_of_pos hlogN0 _
  have hLpow : L ^ (10:ℕ) = Real.log N := by
    rw [hLdef, ← Real.rpow_natCast (Real.log N ^ ((1:ℝ)/10)) 10,
      ← Real.rpow_mul hlogN0.le]
    norm_num
  have hL30B : 30*B + c + 1 ≤ L := by
    by_contra hcon
    push_neg at hcon
    have h1 : L ^ (10:ℕ) < (30*B + c + 1) ^ (10:ℕ) :=
      pow_lt_pow_left₀ hcon hL0.le (by norm_num)
    rw [hLpow] at h1
    rw [hΛ₃def] at hlogN
    linarith
  have hL1 : 1 ≤ L := by
    have h1 : (0:ℝ) ≤ 30*B + c := by positivity
    linarith
  -- the non-unit trivial bound is dominated by the rated error
  have hnonunit_dom : (q:ℝ) * Real.log N
      ≤ (N:ℝ) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    -- q·logN ≤ (logN)^{B+1} ≤ exp(L^{10} − cL) = N·e^{−cL}
    have h1 : (q:ℝ) * Real.log N ≤ Real.log N ^ ((B:ℝ)) * Real.log N := by
      apply mul_le_mul_of_nonneg_right hqB hlogN0.le
    have h2 : Real.log N ^ ((B:ℝ)) * Real.log N = Real.log N ^ ((B+1 : ℝ)) := by
      rw [Real.rpow_add hlogN0, Real.rpow_one]
    have h3 : Real.log N ^ ((B+1 : ℝ)) = Real.exp ((B+1) * Real.log (Real.log N)) := by
      rw [Real.rpow_def_of_pos hlogN0, mul_comm]
    have hloglog : Real.log (Real.log N) ≤ 10 * (L - 1) + 10 := by
      have h4 : Real.log (Real.log N) = 10 * Real.log L := by
        rw [← hLpow, Real.log_pow]
        push_cast
        ring
      have h5 : Real.log L ≤ L - 1 := by
        have h6 := Real.log_le_sub_one_of_pos hL0
        linarith
      linarith [h4.le, h4.ge]
    have hexp_arg : (B+1) * Real.log (Real.log N) + c * L ≤ L ^ (10:ℕ) := by
      have h7 : (B+1) * Real.log (Real.log N) ≤ (B+1) * (10 * L) := by
        apply mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith [hloglog]
      have h8 : (B+1) * (10 * L) + c * L = (10*B + 10 + c) * L := by ring
      have h9 : (10*B + 10 + c) * L ≤ L ^ (9:ℕ) * L := by
        apply mul_le_mul_of_nonneg_right ?_ hL0.le
        have h10 : L ≤ L ^ (9:ℕ) := le_self_pow₀ hL1 (by norm_num)
        linarith [hL30B]
      have h11 : L ^ (9:ℕ) * L = L ^ (10:ℕ) := by ring
      linarith
    calc (q:ℝ) * Real.log N ≤ Real.log N ^ ((B+1 : ℝ)) := by linarith [h2.le, h2.ge]
      _ = Real.exp ((B+1) * Real.log (Real.log N)) := h3
      _ ≤ Real.exp (L ^ (10:ℕ) - c * L) := by
          apply Real.exp_le_exp.mpr
          linarith [hexp_arg]
      _ = (N:ℝ) * Real.exp (-(c * L)) := by
          rw [show L ^ (10:ℕ) - c * L = L ^ (10:ℕ) + -(c * L) from by ring,
            Real.exp_add, hLpow, Real.exp_log hN0]
      _ = (N:ℝ) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
          rw [hLdef]
          congr 2
          ring
  -- per-residue input for ap_twisted_model, uniform over r < q
  have hper : ∀ r ∈ Finset.range q,
      ∀ t ≤ N, ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r),
        ((Λ n : ℝ) : ℂ)) - (t : ℂ) * lambdaModel q r‖
      ≤ (C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    intro r hr t ht
    rw [Finset.mem_range] at hr
    by_cases hgcd : Nat.gcd r q = 1
    · have h1 := hC1a N hNN₁ q hq0 hqB r hr hgcd t ht
      rw [show lambdaModel q r = 1 / (q.totient : ℂ) from by
        rw [lambdaModel, if_pos hgcd]]
      calc ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
          - (t : ℂ) * (1 / (q.totient : ℂ))‖
          ≤ C * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := h1
        _ ≤ (C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
            have h2 : (0:ℝ) ≤ (N:ℝ) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
              positivity
            nlinarith
    · have h1 := nonunit_progression_bound q hq0 r hgcd N hN3 t ht
      rw [show lambdaModel q r = 0 from by rw [lambdaModel, if_neg hgcd]]
      rw [mul_zero, sub_zero]
      have h2 : ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r),
          ((Λ n : ℝ) : ℂ))‖
          = |∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n| := by
        rw [show (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
            = (((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n : ℝ)) : ℂ)
            from by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [h2, abs_of_nonneg (Finset.sum_nonneg
        (fun n _ => ArithmeticFunction.vonMangoldt_nonneg))]
      calc ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
          ≤ (q:ℝ) * Real.log N := h1
        _ ≤ (N:ℝ) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := hnonunit_dom
        _ ≤ (C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
            have h3 : (0:ℝ) ≤ (N:ℝ) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
              positivity
            nlinarith
  -- assemble via the residue decomposition
  rw [major_arc_residue_decomp (fun n => ((Λ n : ℝ) : ℂ)) N a q hq0 β,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hterm : ∀ r ∈ Finset.range q,
      ‖e ((r : ℝ) * (a : ℝ) / (q : ℝ))
          * (∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
              ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * β))
        - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
        * (1 + 2 * Real.pi * N * |β|) := by
    intro r hr
    have h1 : e ((r : ℝ) * (a : ℝ) / (q : ℝ))
          * (∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
              ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * β))
        - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)
        = e ((r : ℝ) * (a : ℝ) / (q : ℝ))
          * ((∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
              ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * β))
            - lambdaModel q r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)) := by
      ring
    rw [h1, norm_mul, e_norm, one_mul]
    exact ap_twisted_model (fun n => ((Λ n : ℝ) : ℂ)) (lambdaModel q r) q r N β
      ((C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)))
      (hper r hr)
  calc ‖∑ r ∈ Finset.range q,
      (e ((r : ℝ) * (a : ℝ) / (q : ℝ))
          * (∑ n ∈ (Finset.range N).filter (fun n => n % q = r),
              ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * β))
        - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β))‖
      ≤ ∑ r ∈ Finset.range q,
        ((C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
          * (1 + 2 * Real.pi * N * |β|)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (q:ℝ) * ((C + 1) * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
          * (1 + 2 * Real.pi * N * |β|)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ = (C + 1) * q * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
        * (1 + 2 * Real.pi * N * |β|) := by ring

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Rated per-arc S² model** (brick D1): squaring the rated window bound —
    on the arc `α = a/q + β` with `q ≤ (log N)^B`,
    `‖S(α)² − (W(a,q)·T(β))²‖ ≤ C·q·N²·(log N + 1)·exp(−c(log N)^{1/10})·(1+2πN|β|)`
    where `S(α) = ∑_{n<N}Λ(n)e(nα)`, `W(a,q) = ∑_r e(ra/q)·lambdaModel q r`,
    `T(β) = ∑_{n<N}e(nβ)`. Via `A²−B² = (A−B)(A+B)`, `‖A‖ ≤ N·log N` and
    `‖W‖ ≤ 1` (the model window has total mass exactly 1). -/
theorem rated_arc_sq_model (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ a : ℤ, ∀ β : ℝ,
    ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) ^ 2
      - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)) ^ 2‖
    ≤ C * q * N ^ 2 * (Real.log N + 1) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
      * (1 + 2 * Real.pi * N * |β|) := by
  obtain ⟨c, C, hc0, hC0, N₀, hC1⟩ := rated_window_eval B hB
  refine ⟨c, 3 * C, hc0, by positivity, max N₀ 3, ?_⟩
  intro N hN₀ q hq0 hqB a β
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN₀
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN₀
  have hN0 : (0:ℝ) < (N:ℝ) := by
    have h1 : 0 < N := by omega
    exact_mod_cast h1
  have hlogN0 : (0:ℝ) ≤ Real.log N := by
    apply Real.log_nonneg
    have h1 : 1 ≤ N := by omega
    exact_mod_cast h1
  have hwindow := hC1 N hNN₀ q hq0 hqB a β
  -- crude bound on S(α)
  have hS : ‖∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
      * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))‖ ≤ (N:ℝ) * Real.log N := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.range N, ‖((Λ n : ℝ) : ℂ) * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))‖
        = ∑ n ∈ Finset.range N, Λ n := by
          apply Finset.sum_congr rfl
          intro n _
          rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ ∑ _n ∈ Finset.range N, Real.log N := by
          apply Finset.sum_le_sum
          intro n hn
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · rw [show Λ 0 = 0 from ArithmeticFunction.map_zero]
            linarith
          · calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
              _ ≤ Real.log N := by
                  apply Real.log_le_log (by exact_mod_cast hn0)
                  rw [Finset.mem_range] at hn
                  have h1 : n ≤ N := by omega
                  exact_mod_cast h1
      _ = (N:ℝ) * Real.log N := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  -- the model window has mass ≤ 1
  have hφ0 : (0:ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hW : ‖∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r‖
      ≤ 1 := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ r ∈ Finset.range q,
        ‖e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r‖
        = if Nat.gcd r q = 1 then 1 / (q.totient : ℝ) else 0 := by
      intro r _
      rw [norm_mul, e_norm, one_mul, lambdaModel]
      by_cases h : Nat.gcd r q = 1
      · rw [if_pos h, if_pos h,
          show (1 / (q.totient : ℂ)) = (((1 / (q.totient : ℝ)) : ℝ) : ℂ) from by
            push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      · rw [if_neg h, if_neg h, norm_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    have hcard : (((Finset.range q).filter (fun r => Nat.gcd r q = 1)).card : ℝ)
        = (q.totient : ℝ) := by
      have h1 : ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).card
          = q.totient := by
        rw [Nat.totient]
        congr 1
        apply Finset.filter_congr
        intro r _
        simp [Nat.Coprime, Nat.gcd_comm]
      exact_mod_cast h1
    rw [hcard, mul_one_div, div_self hφ0.ne']
  have hT : ‖∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖ ≤ (N:ℝ) := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    calc ∑ n ∈ Finset.range N, ‖e ((n : ℝ) * β)‖
        = ∑ _n ∈ Finset.range N, (1:ℝ) := by
          apply Finset.sum_congr rfl
          intro n _
          exact e_norm _
      _ = (N:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]
  have hB' : ‖(∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
      * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖ ≤ (N:ℝ) := by
    rw [norm_mul]
    calc ‖∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r‖
        * ‖∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
        ≤ 1 * (N:ℝ) := mul_le_mul hW hT (norm_nonneg _) (by norm_num)
      _ = (N:ℝ) := one_mul _
  -- A² − B² = (A−B)(A+B)
  rw [show (∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
        * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) ^ 2
      - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)) ^ 2
      = ((∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
            * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
          - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
            * ∑ n ∈ Finset.range N, e ((n : ℝ) * β))
        * ((∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
            * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
          + (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
            * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)) from by ring,
    norm_mul]
  have hsum : ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
        * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
      + (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
        * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (N:ℝ) * (Real.log N + 1) := by
    calc ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
          * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
        + (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
        ≤ ‖∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
            * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))‖
          + ‖(∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
              * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖ := norm_add_le _ _
      _ ≤ (N:ℝ) * Real.log N + (N:ℝ) := by linarith [hS, hB']
      _ = (N:ℝ) * (Real.log N + 1) := by ring
  have hEpos : (0:ℝ) ≤ Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
      * (1 + 2 * Real.pi * N * |β|) := by
    have h1 : (0:ℝ) ≤ 1 + 2 * Real.pi * N * |β| := by positivity
    positivity
  calc ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
        * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
      - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
        * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      * ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ)
          * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
        + (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (C * q * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
          * (1 + 2 * Real.pi * N * |β|))
        * ((N:ℝ) * (Real.log N + 1)) := by
        apply mul_le_mul hwindow hsum (norm_nonneg _) ?_
        have h1 : (0:ℝ) ≤ (q:ℝ) := by positivity
        have h2 : (0:ℝ) ≤ 1 + 2 * Real.pi * N * |β| := by positivity
        positivity
    _ = C * q * N ^ 2 * (Real.log N + 1) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
        * (1 + 2 * Real.pi * N * |β|) := by ring
    _ ≤ 3 * C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi * N * |β|) := by
        have h1 : (0:ℝ) ≤ (q:ℝ) * N ^ 2 * (Real.log N + 1)
            * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
            * (1 + 2 * Real.pi * N * |β|) := by
          have h2 : (0:ℝ) ≤ 1 + 2 * Real.pi * N * |β| := by positivity
          positivity
        have h3 : C * ((q:ℝ) * N ^ 2 * (Real.log N + 1)
            * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi * N * |β|))
            ≤ (3 * C) * ((q:ℝ) * N ^ 2 * (Real.log N + 1)
            * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi * N * |β|)) :=
          mul_le_mul_of_nonneg_right (by linarith) h1
        linarith [h3]

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Per-anchor integral error** (brick D2a): over one Farey window (radius
    `1/(q(N+1))`, so `N|β| ≤ 1` and the `(1+2πN|β|)` factor is `≤ 1+2π`), the
    integral of `(S² − model²)·e(−nα)` is bounded — uniformly in `n` and the
    anchor — by `C·N·(log N + 1)·exp(−c(log N)^{1/10})`; the window length
    `2/(q(N+1))` cancels the `q·N²` of the pointwise D1 bound. -/
theorem anchor_integral_error (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ a : ℤ, ∀ n : ℕ,
    ‖∫ α in Metric.closedBall ((a : ℝ) / q) (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * N * (Real.log N + 1) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, N₀, hD1⟩ := rated_arc_sq_model B hB
  refine ⟨c, 20 * C, hc0, by positivity, max N₀ 3, ?_⟩
  intro N hN₀ q hq0 hqB a n
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN₀
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN₀
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
  have hN0R : (0:ℝ) < (N:ℝ) := by
    have h1 : 0 < N := by omega
    exact_mod_cast h1
  have hr0 : (0:ℝ) ≤ 1 / (q * (N + 1)) := by positivity
  have hlogN0 : (0:ℝ) ≤ Real.log N := by
    apply Real.log_nonneg
    have h5 : 1 ≤ N := by omega
    exact_mod_cast h5
  have hK : (0:ℝ) ≤ C * q * N ^ 2 * (Real.log N + 1)
      * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi) := by
    have h1 : (0:ℝ) ≤ 1 + 2 * Real.pi := by nlinarith [Real.pi_pos]
    positivity
  -- pointwise bound on the window
  have hpt : ∀ α ∈ Metric.closedBall ((a : ℝ) / q) (1 / (q * (N + 1)))
      ∩ Set.Ioc (0:ℝ) 1,
      ‖((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
        - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
            * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi) := by
    intro α hα
    obtain ⟨hball, -⟩ := hα
    rw [Metric.mem_closedBall, Real.dist_eq] at hball
    rw [norm_mul, e_norm, mul_one]
    have hβ := hD1 N hNN₀ q hq0 hqB a (α - (a : ℝ) / (q : ℝ))
    have hαeq : (a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ)) = α := by ring
    rw [hαeq] at hβ
    refine hβ.trans ?_
    have hfac : 1 + 2 * Real.pi * N * |α - (a : ℝ) / (q : ℝ)| ≤ 1 + 2 * Real.pi := by
      have h3 : (N:ℝ) * (1 / (q * (N + 1))) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        nlinarith
      have h1 : (N:ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ 1 := by
        calc (N:ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ (N:ℝ) * (1 / (q * (N + 1))) := by
              apply mul_le_mul_of_nonneg_left hball (by positivity)
          _ ≤ 1 := h3
      nlinarith [Real.pi_pos]
    have hK2 : (0:ℝ) ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by positivity
    exact mul_le_mul_of_nonneg_left hfac hK2
  -- the window has small measure
  have hvol : (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
      (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal ≤ 2 / (q * (N + 1)) := by
    have h1 : MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
        (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1)
        ≤ ENNReal.ofReal (2 * (1 / (q * (N + 1)))) := by
      calc MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
          (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1)
          ≤ MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
            (1 / (q * (N + 1)))) :=
            MeasureTheory.measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (2 * (1 / (q * (N + 1)))) :=
            Real.volume_closedBall _ _
    calc (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
        (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal
        ≤ (ENNReal.ofReal (2 * (1 / (q * (N + 1))))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = 2 * (1 / (q * (N + 1))) := ENNReal.toReal_ofReal (by positivity)
      _ = 2 / (q * (N + 1)) := by ring
  have hfin : MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
      (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      MeasureTheory.measure_closedBall_lt_top
  have hint : ‖∫ α in Metric.closedBall ((a : ℝ) / q) (1 / (q * (N + 1)))
      ∩ Set.Ioc (0:ℝ) 1,
      ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
        - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
            * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi)
        * (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
            (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hpt
    simpa [MeasureTheory.measureReal_def] using h
  refine hint.trans ?_
  -- (K')·vol ≤ 20C·N·(log N+1)·e^{−cL}
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  calc C * q * N ^ 2 * (Real.log N + 1)
      * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi)
      * (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
          (1 / (q * (N + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal
      ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (1 + 2 * Real.pi)
        * (2 / (q * (N + 1))) := by
        apply mul_le_mul_of_nonneg_left hvol hK
    _ = (2 * (1 + 2 * Real.pi)) * (C * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) * ((N:ℝ) ^ 2 / (N + 1)) := by
        field_simp
    _ ≤ (2 * (1 + 2 * Real.pi)) * (C * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) * (N:ℝ) := by
        apply mul_le_mul_of_nonneg_left ?_ ?_
        · rw [div_le_iff₀ (by positivity)]
          nlinarith
        · have h1 : (0:ℝ) ≤ 1 + 2 * Real.pi := by nlinarith [Real.pi_pos]
          positivity
    _ ≤ 20 * C * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
        have h1 : 2 * (1 + 2 * Real.pi) ≤ 20 := by nlinarith
        have h2 : (0:ℝ) ≤ C * (Real.log N + 1)
            * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) * (N:ℝ) := by positivity
        nlinarith [h2, mul_nonneg (mul_nonneg hC0.le
          (by linarith : (0:ℝ) ≤ Real.log N + 1)) (Real.exp_pos
          (-c * Real.log N ^ ((1:ℝ)/10))).le]

-- duplicated from MinorArcExpSum.lean (deduped at the Phase-F concatenation)

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Anchor-sum error** (brick D2b): summing the per-anchor integral errors over
    all reduced Farey anchors of level `P ≤ (log N)^B`:
    `‖∑_pq ∫_window (S² − model_pq²)e(−nα)‖ ≤ C·P²·N·(log N+1)·exp(−c(log N)^{1/10})`,
    uniform in `n` — `#anchors ≤ P(3P+1) ≤ 4P²`. -/
theorem anchor_sum_error (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ P : ℕ, 0 < P → (P : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ n : ℕ,
    ‖∑ pq ∈ anchors P,
        ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
          ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * P ^ 2 * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, N₀, hD2a⟩ := anchor_integral_error B hB
  refine ⟨c, 4 * C, hc0, by positivity, N₀, ?_⟩
  intro N hN₀ P hP0 hPB n
  have hP0R : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP0
  have hterm : ∀ pq ∈ anchors P,
      ‖∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
          ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * N * (Real.log N + 1) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    intro pq hpq
    rw [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
    obtain ⟨⟨⟨hq1, hqP⟩, -⟩, -⟩ := hpq
    have hq0 : 0 < pq.1 := hq1
    have hqB : (pq.1 : ℝ) ≤ Real.log N ^ (B : ℝ) := by
      have h1 : (pq.1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hqP
      linarith
    exact hD2a N hN₀ pq.1 hq0 hqB pq.2 n
  have hcard : ((anchors P).card : ℝ) ≤ 4 * P ^ 2 := by
    have h1 : (anchors P).card ≤ P * (3 * P + 1) := by
      calc (anchors P).card
          ≤ (Finset.Icc 1 P ×ˢ Finset.Icc (-(P : ℤ)) (2 * P)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = (Finset.Icc 1 P).card * (Finset.Icc (-(P : ℤ)) (2 * P)).card :=
            Finset.card_product _ _
        _ = P * (3 * P + 1) := by
            rw [Nat.card_Icc, Int.card_Icc]
            congr 1
            omega
    have h3 : P * (3 * P + 1) ≤ 4 * P ^ 2 := by nlinarith
    calc ((anchors P).card : ℝ) ≤ ((P * (3 * P + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ((4 * P ^ 2 : ℕ) : ℝ) := by exact_mod_cast h3
      _ = 4 * (P:ℝ) ^ 2 := by push_cast; ring
  have hK0 : (0:ℝ) ≤ C * N * (Real.log N + 1)
      * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hlogN0 : (0:ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN1
      · simp
      · apply Real.log_nonneg
        exact_mod_cast hN1
    positivity
  calc ‖∑ pq ∈ anchors P,
      ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
          ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ ∑ pq ∈ anchors P, (C * N * (Real.log N + 1)
          * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = ((anchors P).card : ℝ) * (C * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * (P:ℝ) ^ 2) * (C * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) :=
        mul_le_mul_of_nonneg_right hcard hK0
    _ = 4 * C * P ^ 2 * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by ring

section CrossFileInputsD


end CrossFileInputsD

lemma e_continuous : Continuous e := by
  unfold e
  fun_prop

lemma cont_S_sq_e (N n : ℕ) : Continuous (fun α : ℝ =>
    (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
      * e (-((n : ℝ) * α))) := by
  unfold e
  fun_prop

lemma cont_model_sq_e (q : ℕ) (a : ℤ) (N n : ℕ) (W : ℂ) : Continuous (fun α : ℝ =>
    (W * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2
      * e (-((n : ℝ) * α))) := by
  unfold e
  fun_prop

lemma integrableOn_window {f : ℝ → ℂ} (hf : Continuous f) (x r : ℝ) :
    MeasureTheory.IntegrableOn f
      (Metric.closedBall x r ∩ Set.Ioc (0:ℝ) 1) := by
  apply MeasureTheory.IntegrableOn.mono_set (t := Metric.closedBall x r)
    ?_ Set.inter_subset_left
  rw [Real.closedBall_eq_Icc]
  exact hf.integrableOn_Icc

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Major-arc Bessel error** (brick D3): with the model coefficient
    `c n := ∑_pq ∫_window model_pq²·e(−nα)`, the summed squared errors of the
    major-arc Fourier coefficients satisfy
    `∑_{n<2N} ‖∫_MW S²e(−nα) − c n‖² ≤ C·P⁴·N³·(log N+1)²·exp(−2c(log N)^{1/10})`.
    The window union decomposes exactly (farey_disjoint at `Q = N`), each window
    difference telescopes to the D2b sum, and there are `2N` terms. -/
theorem major_bessel_error (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ P : ℕ, 0 < P → (P : ℝ) ≤ Real.log N ^ (B : ℝ) → 2 * P ^ 2 < N + 1 →
    ∑ n ∈ Finset.range (2 * N),
      ‖(∫ α in ⋃ pq ∈ anchors P,
            (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
              ∩ Set.Ioc (0:ℝ) 1),
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∑ pq ∈ anchors P,
            ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
              ∩ Set.Ioc (0:ℝ) 1,
            ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))‖ ^ 2
      ≤ C * P ^ 4 * N ^ 3 * (Real.log N + 1) ^ 2
        * Real.exp (-(2 * c) * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, N₀, hD2b⟩ := anchor_sum_error B hB
  refine ⟨c, 2 * C ^ 2, hc0, by positivity, N₀, ?_⟩
  intro N hN₀ P hP0 hPB hPQ
  have hmeas : ∀ pq ∈ anchors P, MeasurableSet
      (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
        ∩ Set.Ioc (0:ℝ) 1) := by
    intro pq _
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hdis : ((anchors P : Finset (ℕ × ℤ)) : Set (ℕ × ℤ)).Pairwise
      (Function.onFun Disjoint (fun pq =>
        Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
          ∩ Set.Ioc (0:ℝ) 1)) := by
    intro pq hpq pq' hpq' hne
    rw [Finset.mem_coe, anchors, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hpq hpq'
    obtain ⟨⟨⟨hq1, hqP⟩, -⟩, hg⟩ := hpq
    obtain ⟨⟨⟨hq1', hqP'⟩, -⟩, hg'⟩ := hpq'
    have hd := farey_disjoint P N hPQ pq.2 pq'.2 pq.1 pq'.1 hq1 hq1' hqP hqP' hg hg'
      (by
        intro hcon
        apply hne
        exact Prod.ext hcon.2 hcon.1)
    exact Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left hd
  -- per-n error bound
  have hkey : ∀ n : ℕ,
      ‖(∫ α in ⋃ pq ∈ anchors P,
            (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
              ∩ Set.Ioc (0:ℝ) 1),
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∑ pq ∈ anchors P,
            ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
              ∩ Set.Ioc (0:ℝ) 1,
            ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))‖
      ≤ C * P ^ 2 * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    intro n
    have hint1 : ∀ pq ∈ anchors P, MeasureTheory.IntegrableOn (fun α : ℝ =>
        (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          * e (-((n : ℝ) * α)))
        (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
          ∩ Set.Ioc (0:ℝ) 1) := by
      intro pq _
      exact integrableOn_window (cont_S_sq_e N n) _ _
    rw [MeasureTheory.integral_biUnion_finset (anchors P) hmeas hdis hint1,
      ← Finset.sum_sub_distrib]
    have hsub : ∀ pq ∈ anchors P,
        (∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          ((∑ r ∈ Finset.range pq.1,
              e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
            * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))
        = ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
            * e (-((n : ℝ) * α)) := by
      intro pq hpq
      rw [← MeasureTheory.integral_sub (hint1 pq hpq)
        (integrableOn_window (cont_model_sq_e pq.1 pq.2 N n _) _ _)]
      apply MeasureTheory.setIntegral_congr_fun (hmeas pq hpq)
      intro α _
      ring
    rw [Finset.sum_congr rfl hsub]
    exact hD2b N hN₀ P hP0 hPB n
  -- sum the squares
  have hK0 : (0:ℝ) ≤ C * P ^ 2 * N * (Real.log N + 1)
      * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    have hlogN0 : (0:ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN1
      · simp
      · apply Real.log_nonneg
        exact_mod_cast hN1
    positivity
  calc ∑ n ∈ Finset.range (2 * N),
      ‖(∫ α in ⋃ pq ∈ anchors P,
            (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
              ∩ Set.Ioc (0:ℝ) 1),
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∑ pq ∈ anchors P,
            ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (N + 1)))
              ∩ Set.Ioc (0:ℝ) 1,
            ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))‖ ^ 2
      ≤ ∑ _n ∈ Finset.range (2 * N), (C * P ^ 2 * N * (Real.log N + 1)
          * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        exact pow_le_pow_left₀ (norm_nonneg _) (hkey n) 2
    _ = (2 * N : ℕ) * ((C * P ^ 2 * N * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ = 2 * C ^ 2 * P ^ 4 * N ^ 3 * (Real.log N + 1) ^ 2
        * Real.exp (-(2 * c) * Real.log N ^ ((1:ℝ)/10)) := by
        have hexp : (Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2
            = Real.exp (-(2 * c) * Real.log N ^ ((1:ℝ)/10)) := by
          rw [show ((Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2 : ℝ)
              = Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
                * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) from sq _,
            ← Real.exp_add]
          congr 1
          ring
        push_cast
        rw [← hexp]
        ring

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Per-anchor integral error, general window level** (brick D2a-Q): over one
    Farey window of radius `1/(q(Q+1))`, uniformly in `n` and the anchor:
    `‖∫_window (S² − model²)e(−nα)‖ ≤ C·(N²/(Q+1))·(log N+1)·(1+N/(Q+1))·exp(−c(log N)^{1/10})`.
    (`Q` free; at `Q ~ N/(log N)^{2B}` the extra factors are polylog.) -/
theorem anchor_integral_error_q (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ Q : ℕ, ∀ a : ℤ, ∀ n : ℕ,
    ‖∫ α in Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1) * (1 + (N:ℝ) / (Q + 1))
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, N₀, hD1⟩ := rated_arc_sq_model B hB
  refine ⟨c, 20 * C, hc0, by positivity, max N₀ 3, ?_⟩
  intro N hN₀ q hq0 hqB Q a n
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN₀
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN₀
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
  have hQ0R : (0:ℝ) < (Q:ℝ) + 1 := by positivity
  have hN0R : (0:ℝ) < (N:ℝ) := by
    have h1 : 0 < N := by omega
    exact_mod_cast h1
  have hlogN0 : (0:ℝ) ≤ Real.log N := by
    apply Real.log_nonneg
    have h5 : 1 ≤ N := by omega
    exact_mod_cast h5
  have hwfac0 : (0:ℝ) ≤ 1 + 2 * Real.pi * ((N:ℝ) / (Q + 1)) := by
    have h1 : (0:ℝ) ≤ (N:ℝ) / (Q + 1) := by positivity
    nlinarith [Real.pi_pos]
  have hK : (0:ℝ) ≤ C * q * N ^ 2 * (Real.log N + 1)
      * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
      * (1 + 2 * Real.pi * ((N:ℝ) / (Q + 1))) := by positivity
  -- pointwise bound on the window
  have hpt : ∀ α ∈ Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1)))
      ∩ Set.Ioc (0:ℝ) 1,
      ‖((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
        - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
            * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
        * (1 + 2 * Real.pi * ((N:ℝ) / (Q + 1))) := by
    intro α hα
    obtain ⟨hball, -⟩ := hα
    rw [Metric.mem_closedBall, Real.dist_eq] at hball
    rw [norm_mul, e_norm, mul_one]
    have hβ := hD1 N hNN₀ q hq0 hqB a (α - (a : ℝ) / (q : ℝ))
    have hαeq : (a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ)) = α := by ring
    rw [hαeq] at hβ
    refine hβ.trans ?_
    have hfac : 1 + 2 * Real.pi * N * |α - (a : ℝ) / (q : ℝ)|
        ≤ 1 + 2 * Real.pi * ((N:ℝ) / (Q + 1)) := by
      have h1 : (N:ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ (N:ℝ) / (Q + 1) := by
        have h3 : (N:ℝ) * (1 / (q * (Q + 1))) ≤ (N:ℝ) / (Q + 1) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) hQ0R]
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hq1R) hN0R.le) hQ0R.le]
        calc (N:ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ (N:ℝ) * (1 / (q * (Q + 1))) := by
              apply mul_le_mul_of_nonneg_left hball (by positivity)
          _ ≤ (N:ℝ) / (Q + 1) := h3
      nlinarith [Real.pi_pos]
    have hK2 : (0:ℝ) ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by positivity
    exact mul_le_mul_of_nonneg_left hfac hK2
  -- window measure
  have hvol : (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
      (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal ≤ 2 / (q * (Q + 1)) := by
    have h1 : MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
        (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1)
        ≤ ENNReal.ofReal (2 * (1 / (q * (Q + 1)))) := by
      calc MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
          (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1)
          ≤ MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
            (1 / (q * (Q + 1)))) :=
            MeasureTheory.measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (2 * (1 / (q * (Q + 1)))) :=
            Real.volume_closedBall _ _
    calc (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
        (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal
        ≤ (ENNReal.ofReal (2 * (1 / (q * (Q + 1))))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = 2 * (1 / (q * (Q + 1))) := ENNReal.toReal_ofReal (by positivity)
      _ = 2 / (q * (Q + 1)) := by ring
  have hfin : MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
      (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      MeasureTheory.measure_closedBall_lt_top
  have hint : ‖∫ α in Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1)))
      ∩ Set.Ioc (0:ℝ) 1,
      ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
        - ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
            * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
        * (1 + 2 * Real.pi * ((N:ℝ) / (Q + 1)))
        * (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
            (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hpt
    simpa [MeasureTheory.measureReal_def] using h
  refine hint.trans ?_
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  calc C * q * N ^ 2 * (Real.log N + 1)
      * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
      * (1 + 2 * Real.pi * ((N:ℝ) / (Q + 1)))
      * (MeasureTheory.volume (Metric.closedBall ((a : ℝ) / q)
          (1 / (q * (Q + 1))) ∩ Set.Ioc (0:ℝ) 1)).toReal
      ≤ C * q * N ^ 2 * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
        * (1 + 2 * Real.pi * ((N:ℝ) / (Q + 1)))
        * (2 / (q * (Q + 1))) := by
        apply mul_le_mul_of_nonneg_left hvol hK
    _ = (2 * (C * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))))
        * ((N:ℝ) ^ 2 / (Q + 1)) * (1 + 2 * Real.pi * ((N:ℝ) / (Q + 1))) := by
        field_simp
    _ ≤ (2 * (C * (Real.log N + 1)
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))))
        * ((N:ℝ) ^ 2 / (Q + 1)) * (10 * (1 + (N:ℝ) / (Q + 1))) := by
        apply mul_le_mul_of_nonneg_left ?_ ?_
        · have h1 : (0:ℝ) ≤ (N:ℝ) / (Q + 1) := by positivity
          nlinarith
        · positivity
    _ = 20 * C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1) * (1 + (N:ℝ) / (Q + 1))
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by ring

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Anchor-sum error, general window level** (brick D2b-Q). -/
theorem anchor_sum_error_q (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ P : ℕ, 0 < P → (P : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ Q : ℕ, ∀ n : ℕ,
    ‖∑ pq ∈ anchors P,
        ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
          ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * P ^ 2 * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1) * (1 + (N:ℝ) / (Q + 1))
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, N₀, hD2a⟩ := anchor_integral_error_q B hB
  refine ⟨c, 4 * C, hc0, by positivity, N₀, ?_⟩
  intro N hN₀ P hP0 hPB Q n
  have hP0R : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP0
  have hterm : ∀ pq ∈ anchors P,
      ‖∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
          ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1) * (1 + (N:ℝ) / (Q + 1))
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    intro pq hpq
    rw [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
    obtain ⟨⟨⟨hq1, hqP⟩, -⟩, -⟩ := hpq
    have hqB : (pq.1 : ℝ) ≤ Real.log N ^ (B : ℝ) := by
      have h1 : (pq.1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hqP
      linarith
    exact hD2a N hN₀ pq.1 hq1 hqB Q pq.2 n
  have hcard : ((anchors P).card : ℝ) ≤ 4 * P ^ 2 := by
    have h1 : (anchors P).card ≤ P * (3 * P + 1) := by
      calc (anchors P).card
          ≤ (Finset.Icc 1 P ×ˢ Finset.Icc (-(P : ℤ)) (2 * P)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = (Finset.Icc 1 P).card * (Finset.Icc (-(P : ℤ)) (2 * P)).card :=
            Finset.card_product _ _
        _ = P * (3 * P + 1) := by
            rw [Nat.card_Icc, Int.card_Icc]
            congr 1
            omega
    have h3 : P * (3 * P + 1) ≤ 4 * P ^ 2 := by nlinarith
    calc ((anchors P).card : ℝ) ≤ ((P * (3 * P + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ((4 * P ^ 2 : ℕ) : ℝ) := by exact_mod_cast h3
      _ = 4 * (P:ℝ) ^ 2 := by push_cast; ring
  have hK0 : (0:ℝ) ≤ C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
      * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    have hlogN0 : (0:ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN1
      · simp
      · apply Real.log_nonneg
        exact_mod_cast hN1
    positivity
  calc ‖∑ pq ∈ anchors P,
      ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
          ∩ Set.Ioc (0:ℝ) 1,
        ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α))‖
      ≤ ∑ _pq ∈ anchors P, (C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
          * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = ((anchors P).card : ℝ) * (C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
        * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * (P:ℝ) ^ 2) * (C * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
        * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) :=
        mul_le_mul_of_nonneg_right hcard hK0
    _ = 4 * C * P ^ 2 * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
        * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by ring

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Major-arc Bessel error, general window level** (brick D3-Q): the form D4
    consumes, with `P ~ (log N)^B` and `Q ~ N/(log N)^{2B}` making every extra
    factor polylog against the exponential saving. -/
theorem major_bessel_error_q (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ P : ℕ, 0 < P → (P : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ Q : ℕ, 2 * P ^ 2 < Q + 1 →
    ∑ n ∈ Finset.range (2 * N),
      ‖(∫ α in ⋃ pq ∈ anchors P,
            (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
              ∩ Set.Ioc (0:ℝ) 1),
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∑ pq ∈ anchors P,
            ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
              ∩ Set.Ioc (0:ℝ) 1,
            ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))‖ ^ 2
      ≤ C * P ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / (Q + 1)) ^ 2 * (Real.log N + 1) ^ 2
        * (1 + (N:ℝ) / (Q + 1)) ^ 2
        * Real.exp (-(2 * c) * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, N₀, hD2b⟩ := anchor_sum_error_q B hB
  refine ⟨c, C ^ 2, hc0, by positivity, N₀, ?_⟩
  intro N hN₀ P hP0 hPB Q hPQ
  have hmeas : ∀ pq ∈ anchors P, MeasurableSet
      (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
        ∩ Set.Ioc (0:ℝ) 1) := by
    intro pq _
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hdis : ((anchors P : Finset (ℕ × ℤ)) : Set (ℕ × ℤ)).Pairwise
      (Function.onFun Disjoint (fun pq =>
        Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
          ∩ Set.Ioc (0:ℝ) 1)) := by
    intro pq hpq pq' hpq' hne
    rw [Finset.mem_coe, anchors, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hpq hpq'
    obtain ⟨⟨⟨hq1, hqP⟩, -⟩, hg⟩ := hpq
    obtain ⟨⟨⟨hq1', hqP'⟩, -⟩, hg'⟩ := hpq'
    have hd := farey_disjoint P Q hPQ pq.2 pq'.2 pq.1 pq'.1 hq1 hq1' hqP hqP' hg hg'
      (by
        intro hcon
        apply hne
        exact Prod.ext hcon.2 hcon.1)
    exact Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left hd
  have hkey : ∀ n : ℕ,
      ‖(∫ α in ⋃ pq ∈ anchors P,
            (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
              ∩ Set.Ioc (0:ℝ) 1),
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∑ pq ∈ anchors P,
            ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
              ∩ Set.Ioc (0:ℝ) 1,
            ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))‖
      ≤ C * P ^ 2 * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
        * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    intro n
    have hint1 : ∀ pq ∈ anchors P, MeasureTheory.IntegrableOn (fun α : ℝ =>
        (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
          * e (-((n : ℝ) * α)))
        (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
          ∩ Set.Ioc (0:ℝ) 1) := by
      intro pq _
      exact integrableOn_window (cont_S_sq_e N n) _ _
    rw [MeasureTheory.integral_biUnion_finset (anchors P) hmeas hdis hint1,
      ← Finset.sum_sub_distrib]
    have hsub : ∀ pq ∈ anchors P,
        (∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          ((∑ r ∈ Finset.range pq.1,
              e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
            * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))
        = ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          ((∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            - ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2)
            * e (-((n : ℝ) * α)) := by
      intro pq hpq
      rw [← MeasureTheory.integral_sub (hint1 pq hpq)
        (integrableOn_window (cont_model_sq_e pq.1 pq.2 N n _) _ _)]
      apply MeasureTheory.setIntegral_congr_fun (hmeas pq hpq)
      intro α _
      ring
    rw [Finset.sum_congr rfl hsub]
    exact hD2b N hN₀ P hP0 hPB Q n
  have hK0 : (0:ℝ) ≤ C * P ^ 2 * ((N:ℝ) ^ 2 / (Q + 1)) * (Real.log N + 1)
      * (1 + (N:ℝ) / (Q + 1)) * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
    have hlogN0 : (0:ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN1
      · simp
      · apply Real.log_nonneg
        exact_mod_cast hN1
    positivity
  calc ∑ n ∈ Finset.range (2 * N),
      ‖(∫ α in ⋃ pq ∈ anchors P,
            (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
              ∩ Set.Ioc (0:ℝ) 1),
          (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
            * e (-((n : ℝ) * α)))
        - (∑ pq ∈ anchors P,
            ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
              ∩ Set.Ioc (0:ℝ) 1,
            ((∑ r ∈ Finset.range pq.1,
                e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
              * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)))‖ ^ 2
      ≤ ∑ _n ∈ Finset.range (2 * N), (C * P ^ 2 * ((N:ℝ) ^ 2 / (Q + 1))
          * (Real.log N + 1) * (1 + (N:ℝ) / (Q + 1))
          * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        exact pow_le_pow_left₀ (norm_nonneg _) (hkey n) 2
    _ = (2 * N : ℕ) * ((C * P ^ 2 * ((N:ℝ) ^ 2 / (Q + 1))
        * (Real.log N + 1) * (1 + (N:ℝ) / (Q + 1))
        * Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ = C ^ 2 * P ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / (Q + 1)) ^ 2
        * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / (Q + 1)) ^ 2
        * Real.exp (-(2 * c) * Real.log N ^ ((1:ℝ)/10)) := by
        have hexp : (Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2
            = Real.exp (-(2 * c) * Real.log N ^ ((1:ℝ)/10)) := by
          rw [show ((Real.exp (-c * Real.log N ^ ((1:ℝ)/10))) ^ 2 : ℝ)
              = Real.exp (-c * Real.log N ^ ((1:ℝ)/10))
                * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) from sq _,
            ← Real.exp_add]
          congr 1
          ring
        push_cast
        rw [← hexp]
        ring

-- duplicated from MinorArcExpSum.lean (deduped at the Phase-F concatenation)

section CrossFileInputsE







end CrossFileInputsE


/-- The truncated singular-series / anchor-window model coefficient (the `c(n)` fed to
    `variance_le_bessel`; matches `major_bessel_error_q`'s model sum). -/
noncomputable def coeffModel (N P Q : ℕ) : ℕ → ℂ := fun n =>
  ∑ pq ∈ anchors P,
    ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
      ∩ Set.Ioc (0:ℝ) 1,
    ((∑ r ∈ Finset.range pq.1, e ((r : ℝ) * (pq.2 : ℝ) / (pq.1 : ℝ)) * lambdaModel pq.1 r)
      * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
    * e (-((n : ℝ) * α))

/-- **Phase D brick (c): the circle-method variance bound (X-dependent form).**
    With `P = ⌊(log N)^9⌋₊`, `Q = N/P`, the weighted Goldbach count `R(n)` is close in
    ℓ² to the truncated singular-series model: `∑_{n<2N} ‖R(n) − c(n)‖² ≤ ε N³` eventually. -/
theorem core_variance (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ))
          - coeffModel N (Nat.floor ((Real.log N) ^ 9)) (N / Nat.floor ((Real.log N) ^ 9)) n‖ ^ 2
      ≤ ε * (N : ℝ) ^ 3 := by
  obtain ⟨cM, CM, hcM, hCM, Nmaj, hmaj⟩ := major_bessel_error_q 9 (by norm_num)
  obtain ⟨Nmin, hmin⟩ := minor_limit (ε / 2) (by linarith)
  obtain ⟨Nexp, hexp⟩ := exp_dominates_polylog (2 * cM) (by linarith) 74 (ε / (128 * CM)) (by positivity)
  obtain ⟨Npoly, hpoly⟩ := polylog_le_self 27 2 (by norm_num)
  refine ⟨max 8 (max Nmaj (max Nmin (max Nexp Npoly))), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hNmaj : Nmaj ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNmin : Nmin ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNexp : Nexp ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hNpoly : Npoly ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  -- scale facts
  have hN1 : 1 ≤ N := by omega
  have hNR : (8:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN8
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogN2 : (2:ℝ) ≤ Real.log N := by
    calc (2:ℝ) ≤ Real.log 8 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
          have := Real.log_two_gt_d9; push_cast; linarith
      _ ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlogNpos : (0:ℝ) < Real.log N := by linarith
  set P : ℕ := Nat.floor ((Real.log N) ^ 9) with hPdef
  set Q : ℕ := N / P with hQdef
  -- bookkeeping
  have hL9nn : (0:ℝ) ≤ (Real.log N) ^ 9 := by positivity
  have hPleL9 : (P:ℝ) ≤ (Real.log N) ^ 9 := by rw [hPdef]; exact Nat.floor_le hL9nn
  have hP2 : 2 ≤ P := by
    rw [hPdef]; apply Nat.le_floor
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hlogN2 9
    calc ((2:ℕ):ℝ) = 2 := by norm_num
      _ ≤ (2:ℝ)^9 := by norm_num
      _ ≤ (Real.log N)^9 := h
  have hP0 : 0 < P := by omega
  have hP1 : 1 ≤ P := by omega
  have hPR1 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP1
  have h2poly : (2:ℝ) * (Real.log N)^27 ≤ (N:ℝ) := hpoly N hNpoly
  have hL27nn : (0:ℝ) ≤ (Real.log N)^27 := by positivity
  -- P^3 ≤ N
  have hP3R : (P:ℝ)^3 ≤ (Real.log N)^27 := by
    calc (P:ℝ)^3 ≤ ((Real.log N)^9)^3 := by apply pow_le_pow_left₀ (by positivity) hPleL9
      _ = (Real.log N)^27 := by ring
  have hP3 : P ^ 3 ≤ N := by
    have : (P:ℝ)^3 ≤ (N:ℝ) := by nlinarith [hP3R, h2poly, hL27nn]
    have h2 : ((P^3 : ℕ):ℝ) ≤ ((N:ℕ):ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hP2le : P ^ 2 ≤ N := le_trans (Nat.pow_le_pow_right hP1 (by norm_num)) hP3
  have hPN : P ≤ N := le_trans (Nat.le_self_pow (by norm_num) P) hP3
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.one_le_div_iff hP0 |>.mpr hPN
  have hPQcut : P ≤ Q := by
    rw [hQdef]; exact Nat.le_div_iff_mul_le hP0 |>.mpr (by rw [← pow_two]; exact hP2le)
  have hPmulQ : P * Q ≤ N := by rw [hQdef]; exact Nat.mul_div_le N P
  have h2P3 : 2 * P ^ 3 ≤ N := by
    have : ((2 * P^3 : ℕ):ℝ) ≤ ((N:ℕ):ℝ) := by push_cast; nlinarith [hP3R, h2poly, hL27nn]
    exact_mod_cast this
  have h2P2Q : 2 * P ^ 2 < Q + 1 := by
    have h2P2 : 2 * P ^ 2 ≤ Q := by
      rw [hQdef]; apply Nat.le_div_iff_mul_le hP0 |>.mpr
      calc 2 * P ^ 2 * P = 2 * P ^ 3 := by ring
        _ ≤ N := h2P3
    omega
  have hPB : (P:ℝ) ≤ Real.log N ^ (9:ℝ) := by
    have hbridge : Real.log N ^ (9:ℝ) = (Real.log N) ^ (9:ℕ) := by
      rw [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hbridge]; exact hPleL9
  -- apply variance_le_bessel
  have hbessel := variance_le_bessel (fun k => ((Λ k : ℝ) : ℂ)) N
    (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset
    (coeffModel N P Q)
  -- set equality for the major integral domain
  have hset : Set.Ioc (0:ℝ) 1 \ (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q)
      = ⋃ pq ∈ anchors P,
          (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1) := by
    rw [Set.diff_diff_right, Set.diff_self, Set.empty_union, Set.inter_comm,
        majorArcs_inter_eq_anchors P Q hP0, Set.iUnion₂_inter]
  -- term1 ≤ ε/2 N³  and  term2 ≤ ε/2 N³
  have hterm1 : 2 * (∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
        ‖∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)‖ ^ 4) ≤ ε / 2 * (N:ℝ)^3 := by
    have hms : MeasurableSet (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q) :=
      measurableSet_Ioc.diff (measurableSet_majorArcs P Q)
    have heq : (∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
          ‖∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)‖ ^ 4)
        = ∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
          ‖(∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2‖ ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun hms
      intro α _
      dsimp only
      rw [norm_pow]; ring
    rw [heq]
    have hL4 := minor_L4_le_explicit N P Q hP2 hP3 hPQcut hPmulQ hN1 hQ1
    have hml := hmin N hNmin
    rw [← hPdef] at hml
    linarith [hL4, hml]
  have hterm2 : 2 * ∑ n ∈ Finset.range (2 * N),
        ‖(∫ α in Set.Ioc (0:ℝ) 1 \ (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
            (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α)))
          - coeffModel N P Q n‖ ^ 2 ≤ ε / 2 * (N:ℝ)^3 := by
    have hsum := hmaj N hNmaj P hP0 hPB Q h2P2Q
    simp only [coeffModel]
    simp_rw [hset]
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num)) ?_
    -- goal: 2 * majorRHS ≤ ε/2 * N³
    have hQ1pos : (0:ℝ) < (Q:ℝ) + 1 := by positivity
    have hNltR : (N:ℝ) < ((Q:ℝ) + 1) * P := by
      have hmod : N % P < P := Nat.mod_lt N hP0
      have hdm : P * (N / P) + N % P = N := Nat.div_add_mod N P
      have hnat : N < (Q + 1) * P := by
        have heq : (Q + 1) * P = P * (N / P) + P := by rw [hQdef]; ring
        omega
      exact_mod_cast hnat
    have hNQ : (N:ℝ) / ((Q:ℝ) + 1) ≤ (P:ℝ) := by
      rw [div_le_iff₀ hQ1pos]; nlinarith [hNltR]
    have hA : (N:ℝ) ^ 2 / ((Q:ℝ) + 1) ≤ (N:ℝ) * P := by
      rw [div_le_iff₀ hQ1pos]; nlinarith [mul_lt_mul_of_pos_left hNltR hNpos]
    have hG : (1:ℝ) + (N:ℝ) / ((Q:ℝ) + 1) ≤ 2 * P := by linarith [hNQ, hPR1]
    have hB : Real.log N + 1 ≤ 2 * Real.log N := by linarith [hlogN2]
    have hP8_72 : (P:ℝ) ^ 8 ≤ (Real.log N) ^ 72 := by
      calc (P:ℝ) ^ 8 ≤ ((Real.log N) ^ 9) ^ 8 := by apply pow_le_pow_left₀ (by positivity) hPleL9
        _ = (Real.log N) ^ 72 := by ring
    have hEnn : (0:ℝ) ≤ Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := (Real.exp_pos _).le
    have hAnn : (0:ℝ) ≤ (N:ℝ) ^ 2 / ((Q:ℝ) + 1) := by positivity
    have hGnn : (0:ℝ) ≤ (1:ℝ) + (N:ℝ) / ((Q:ℝ) + 1) := by positivity
    have hBnn : (0:ℝ) ≤ Real.log N + 1 := by linarith [hlogNpos]
    have hmaj_ub : CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / ((Q:ℝ) + 1)) ^ 2
          * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / ((Q:ℝ) + 1)) ^ 2
          * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))
        ≤ 32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
          * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by
      calc CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / ((Q:ℝ) + 1)) ^ 2
            * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / ((Q:ℝ) + 1)) ^ 2
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))
          ≤ CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) * P) ^ 2
            * (2 * Real.log N) ^ 2 * (2 * (P:ℝ)) ^ 2
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by
            gcongr
        _ = 32 * CM * (N:ℝ) ^ 3 * ((P:ℝ) ^ 8 * (Real.log N) ^ 2)
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by ring
        _ ≤ 32 * CM * (N:ℝ) ^ 3 * ((Real.log N) ^ 72 * (Real.log N) ^ 2)
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by
            apply mul_le_mul_of_nonneg_right _ hEnn
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hP8_72 (by positivity)
        _ = 32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by ring
    have hexp' := hexp N hNexp
    have hCMne : CM ≠ 0 := ne_of_gt hCM
    calc 2 * (CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / ((Q:ℝ) + 1)) ^ 2
            * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / ((Q:ℝ) + 1)) ^ 2
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)))
        ≤ 2 * (32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))) :=
          mul_le_mul_of_nonneg_left hmaj_ub (by norm_num)
      _ = 64 * CM * (N:ℝ) ^ 3
            * ((Real.log N) ^ 74 * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))) := by ring
      _ ≤ 64 * CM * (N:ℝ) ^ 3 * (ε / (128 * CM)) :=
          mul_le_mul_of_nonneg_left hexp' (by positivity)
      _ = ε / 2 * (N:ℝ) ^ 3 := by field_simp; ring
  calc ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - coeffModel N P Q n‖ ^ 2
      ≤ 2 * (∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
            ‖∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)‖ ^ 4)
          + 2 * ∑ n ∈ Finset.range (2 * N),
              ‖(∫ α in Set.Ioc (0:ℝ) 1 \ (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
                  (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α)))
                - coeffModel N P Q n‖ ^ 2 := hbessel
    _ ≤ ε / 2 * (N:ℝ)^3 + ε / 2 * (N:ℝ)^3 := by linarith [hterm1, hterm2]
    _ = ε * (N:ℝ)^3 := by ring


end GoldbachChain
