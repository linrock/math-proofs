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


end GoldbachChain
