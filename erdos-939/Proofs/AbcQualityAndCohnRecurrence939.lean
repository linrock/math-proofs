module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

public import PowerfulSumsAndNitaj939

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Nat

namespace Erdos939

/-!
# ABC Quality Bound $q(a, b, a+b) \ge 4/3$, Conditional ABC Finiteness of `Erdos939Sums 4`, and Cohn's Non-Cube $3$-Powerful Recurrence on $32 X^3 + 49 Y^3 = 81 Z^3$ (Erdős #939)

This module establishes:
1. **Part 1 (Radical Arithmetic and the ABC Quality Bound $q(a, b, a+b) > 4/3$ for `Erdos939Sums 4`):**
   - Defines the radical $\mathrm{rad}(n) = \prod_{p \in n.\mathrm{primeFactors}} p$ and proves positivity,
     squarefreeness, coprime multiplicativity $\mathrm{rad}(ab(a+b)) = \mathrm{rad}(a)\mathrm{rad}(b)\mathrm{rad}(a+b)$,
     and universal $r$-powerful radical divisibility $\mathrm{rad}(n)^r \mid n$ and $\mathrm{rad}(n)^r \le n$.
   - Proves the universal $r$-powerful coprime triple radical inequality
     $\mathrm{rad}(ab(a+b))^r \le ab(a+b) < (a+b)^3$ and $4\,\mathrm{rad}(ab(a+b))^r < (a+b)^3$ for $r \ge 2$,
     specializing at $r = 4$ (`{a, b} ∈ Erdos939Sums 4`) to
     $$\mathrm{rad}(ab(a+b))^4 \le ab(a+b) < (a+b)^3, \qquad \frac{4}{3}\log\mathrm{rad}(ab(a+b)) < \log(a+b).$$
2. **Part 2 (Conditional ABC Height Bounds and Finiteness of `Erdos939Sums 4`):**
   - Proves that any effective $abc$ quality threshold at $4/3$ ($(x+y)^3 \le \mathrm{rad}(xy(x+y))^4$ for
     coprime $x, y$ with $x + y > B$) bounds $a + b \le B$ and implies `(Erdos939Sums 4).Finite`.
   - Proves that an explicit $abc$ bound at exponent $7/6$ ($(x+y)^6 \le K\,\mathrm{rad}(xy(x+y))^7$)
     forces $(a+b)^3 < K^4$ and `(Erdos939Sums 4).Finite`, while the strong $K=1$ threshold forces
     `Erdos939Sums 4 = ∅` and refutes `∀ r ≥ 4, (Erdos939Sums r).Nonempty`.
3. **Part 3 (Cohn's 1998 Non-Cube $3$-Powerful Recurrence on $32 X^3 + 49 Y^3 = 81 Z^3$):**
   - Formalizes Cohn's signed and unsigned tangent recurrences on $32 X^3 + 49 Y^3 = 81 Z^3$,
     proves that $32 X^3, 49 Y^3$ ($7 \mid Y$), and $81 Z^3$ are $3$-powerful non-cubes via mod-$3$
     prime factorization invariants ($v_2 \equiv 2$, $v_7 \equiv 2$, $v_3 \equiv 1 \pmod{3}$), and
     iterates from Cohn's seed $(X_0, Y_0, Z_0)$ to prove the infinitude of coprime non-cube
     $3$-powerful triples (`cohn_noncube_triples_infinite`) and $2$-element non-cube sets in
     `Erdos939GeneralSums 3 2` (`cohn_noncube_generalSums_three_two_infinite`).
-/

/-! ## Part 1: Radical Arithmetic and the ABC Quality Bound for `Erdos939Sums 4` -/

/-- The radical $\mathrm{rad}(n) = \prod_{p \in n.\mathrm{primeFactors}} p$ of a natural number $n$. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem rad_zero_and_one : rad 0 = 1 ∧ rad 1 = 1 := by
  simp [rad]

theorem rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  refine Finset.prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos

theorem rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  exact squarefree_finset_prod_of_prime n.primeFactors fun p hp => (Nat.mem_primeFactors.mp hp).1

theorem rad_mul_of_coprime {a b : ℕ} (hcop : Nat.Coprime a b) :
    rad (a * b) = rad a * rad b := by
  unfold rad
  rw [Nat.Coprime.primeFactors_mul hcop,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]

theorem rad_mul_add_of_coprime {a b : ℕ} (hcop : Nat.Coprime a b) :
    rad (a * b * (a + b)) = rad a * rad b * rad (a + b) := by
  have hab := coprime_add_self_left_and_right a b hcop
  have hprod : Nat.Coprime (a * b) (a + b) := hab.1.mul_left hab.2
  rw [rad_mul_of_coprime hprod, rad_mul_of_coprime hcop]

/-- For every positive $r$-powerful integer $n$, $\mathrm{rad}(n)^r \mid n$. -/
theorem rad_pow_dvd_of_full {r n : ℕ} (hn : 0 < n) (hfull : r.Full n) :
    rad n ^ r ∣ n := by
  unfold rad
  rw [← Finset.prod_pow]
  have hprod : (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n :=
    Nat.factorization_prod_pow_eq_self (by omega)
  conv_rhs => rw [← hprod]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hdvd : p ^ r ∣ n := hfull p hp
  have hle : r ≤ n.factorization p := (hpp.pow_dvd_iff_le_factorization (by omega)).mp hdvd
  exact Nat.pow_dvd_pow p hle

/-- For every positive $r$-powerful integer $n$, $\mathrm{rad}(n)^r \le n$. -/
theorem rad_pow_le_of_full {r n : ℕ} (hn : 0 < n) (hfull : r.Full n) :
    rad n ^ r ≤ n :=
  Nat.le_of_dvd hn (rad_pow_dvd_of_full hn hfull)

theorem rad_dvd_and_le_self {n : ℕ} (hn : 0 < n) :
    rad n ∣ n ∧ rad n ≤ n := by
  have h1 : (1).Full n := by
    intro p hp
    rw [pow_one]
    exact (Nat.mem_primeFactors.mp hp).2.1
  have hdvd : rad n ∣ n := by simpa using rad_pow_dvd_of_full hn h1
  exact ⟨hdvd, Nat.le_of_dvd hn hdvd⟩

/-- Sharpened AM-GM cubic inequality $4ab(a+b) \le (a+b)^3$, strict whenever $a \ne b$. -/
theorem four_mul_ab_add_le_cube_and_lt_of_ne {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    4 * (a * b * (a + b)) ≤ (a + b) ^ 3 ∧
      (a ≠ b → 4 * (a * b * (a + b)) < (a + b) ^ 3) := by
  rcases le_total a b with hab | hba
  · have hid : (a + b) ^ 3 = 4 * (a * b * (a + b)) + (a + b) * (b - a) ^ 2 := by
      zify [hab]; ring
    refine ⟨by omega, fun hne => ?_⟩
    have hpos : 0 < (a + b) * (b - a) ^ 2 :=
      Nat.mul_pos (by omega) (pow_pos (by omega) 2)
    omega
  · have hid : (a + b) ^ 3 = 4 * (a * b * (a + b)) + (a + b) * (a - b) ^ 2 := by
      zify [hba]; ring
    refine ⟨by omega, fun hne => ?_⟩
    have hpos : 0 < (a + b) * (a - b) ^ 2 :=
      Nat.mul_pos (by omega) (pow_pos (by omega) 2)
    omega

/-- **Universal $r$-Powerful Radical Inequality:** For any positive coprime $r$-powerful pair $(a, b)$
with $r$-powerful sum ($r \ge 2$), $\mathrm{rad}(ab(a+b))^r \le ab(a+b) < (a+b)^3$ and
$4\,\mathrm{rad}(ab(a+b))^r < (a+b)^3$. -/
theorem rad_pow_r_le_and_four_mul_lt_cube_of_coprime_full_triple {r a b : ℕ}
    (hr : 2 ≤ r) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hfa : r.Full a) (hfb : r.Full b) (hfs : r.Full (a + b)) :
    rad (a * b * (a + b)) ^ r ∣ a * b * (a + b) ∧
      rad (a * b * (a + b)) ^ r ≤ a * b * (a + b) ∧
      a * b * (a + b) < (a + b) ^ 3 ∧
      4 * rad (a * b * (a + b)) ^ r < (a + b) ^ 3 := by
  have hfull_prod : r.Full (a * b * (a + b)) :=
    full_mul_of_full r (a * b) (a + b) (full_mul_of_full r a b hfa hfb) hfs
  have hpos_prod : 0 < a * b * (a + b) :=
    Nat.mul_pos (Nat.mul_pos ha hb) (by omega)
  have hdvd : rad (a * b * (a + b)) ^ r ∣ a * b * (a + b) :=
    rad_pow_dvd_of_full hpos_prod hfull_prod
  have hle : rad (a * b * (a + b)) ^ r ≤ a * b * (a + b) :=
    Nat.le_of_dvd hpos_prod hdvd
  have hne : a ≠ b := ne_of_coprime_of_full_add r a b hr ha hcop hfs
  have h4lt : 4 * (a * b * (a + b)) < (a + b) ^ 3 :=
    (four_mul_ab_add_le_cube_and_lt_of_ne ha hb).2 hne
  have h4rad : 4 * rad (a * b * (a + b)) ^ r ≤ 4 * (a * b * (a + b)) :=
    Nat.mul_le_mul_left 4 hle
  exact ⟨hdvd, hle, by omega, lt_of_le_of_lt h4rad h4lt⟩

/-- **ABC Quality Bound for `Erdos939Sums 4` ($\mathbb{N}$ Form):** Every `{a, b} ∈ Erdos939Sums 4`
satisfies $\mathrm{rad}(ab(a+b))^4 \le ab(a+b) < (a+b)^3$ and $4\,\mathrm{rad}(ab(a+b))^4 < (a+b)^3$. -/
theorem rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four {a b : ℕ}
    (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    rad (a * b * (a + b)) ^ 4 ∣ a * b * (a + b) ∧
      rad (a * b * (a + b)) ^ 4 ≤ a * b * (a + b) ∧
      a * b * (a + b) < (a + b) ^ 3 ∧
      4 * rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3 ∧
      rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3 := by
  rcases (pair_mem_erdos939Sums_four_iff a b).mp hmem with ⟨ha, hb, hcop, hfa, hfb, hfs⟩
  have h := rad_pow_r_le_and_four_mul_lt_cube_of_coprime_full_triple (by omega) ha hb hcop hfa hfb hfs
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, lt_of_le_of_lt h.2.1 h.2.2.1⟩

/-- **ABC Quality Bound $q(a, b, a+b) > 4/3$ for `Erdos939Sums 4` ($\mathbb{R}$ Form):**
Every `{a, b} ∈ Erdos939Sums 4` satisfies $\frac{4}{3}\log\mathrm{rad}(ab(a+b)) < \log(a+b)$. -/
theorem abc_quality_four_thirds_real_bound_of_mem_erdos939Sums_four {a b : ℕ}
    (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    (rad (a * b * (a + b)) : ℝ) ^ 4 ≤ (a * b * (a + b) : ℝ) ∧
      (a * b * (a + b) : ℝ) < (a + b : ℝ) ^ 3 ∧
      4 * (rad (a * b * (a + b)) : ℝ) ^ 4 < (a + b : ℝ) ^ 3 ∧
      (4 : ℝ) / 3 * Real.log (rad (a * b * (a + b)) : ℝ) < Real.log (a + b : ℝ) := by
  have h := rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four hmem
  have hle_real : (rad (a * b * (a + b)) : ℝ) ^ 4 ≤ (a * b * (a + b) : ℝ) := by
    exact_mod_cast h.2.1
  have hlt_real : (a * b * (a + b) : ℝ) < (a + b : ℝ) ^ 3 := by
    exact_mod_cast h.2.2.1
  have h4_real : 4 * (rad (a * b * (a + b)) : ℝ) ^ 4 < (a + b : ℝ) ^ 3 := by
    exact_mod_cast h.2.2.2.1
  have hrad_lt_cube : (rad (a * b * (a + b)) : ℝ) ^ 4 < (a + b : ℝ) ^ 3 :=
    lt_of_le_of_lt hle_real hlt_real
  have hrad_pos : (0 : ℝ) < (rad (a * b * (a + b)) : ℝ) := by
    exact_mod_cast rad_pos (a * b * (a + b))
  have hlog : Real.log ((rad (a * b * (a + b)) : ℝ) ^ 4) < Real.log ((a + b : ℝ) ^ 3) :=
    Real.log_lt_log (pow_pos hrad_pos 4) hrad_lt_cube
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  refine ⟨hle_real, hlt_real, h4_real, by linarith⟩

/-! ## Part 2: Conditional ABC Height Bounds and Finiteness of `Erdos939Sums 4` -/

/-- If every coprime pair $(x, y)$ with $x + y > B$ has $abc$ quality $\le 4/3$
($(x+y)^3 \le \mathrm{rad}(xy(x+y))^4$), then every `{a, b} ∈ Erdos939Sums 4` satisfies $a + b \le B$. -/
theorem sum_le_of_abc_four_thirds_threshold {B a b : ℕ}
    (habc : ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y → B < x + y →
      (x + y) ^ 3 ≤ rad (x * y * (x + y)) ^ 4)
    (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    a + b ≤ B := by
  rcases (pair_mem_erdos939Sums_four_iff a b).mp hmem with ⟨ha, hb, hcop, _, _, _⟩
  have hlt := (rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four hmem).2.2.2.2
  by_contra hnot
  have hgt : B < a + b := by omega
  have hge := habc a b ha hb hcop hgt
  omega

/-- **Conditional ABC Finiteness of `Erdos939Sums 4` (Quality $4/3$ Threshold Form):**
If at most finitely many coprime triples have $abc$ quality $> 4/3$, then `Erdos939Sums 4` is finite. -/
theorem erdos939Sums_four_finite_of_pair_abc_four_thirds_threshold {B : ℕ}
    (habc : ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y → B < x + y →
      (x + y) ^ 3 ≤ rad (x * y * (x + y)) ^ 4) :
    (Erdos939Sums 4).Finite :=
  erdos939Sums_four_finite_of_sum_bound fun _ _ hmem =>
    sum_le_of_abc_four_thirds_threshold habc hmem

/-- Under the explicit $abc$ bound $(x+y)^6 \le K\,\mathrm{rad}(xy(x+y))^7$ at exponent $1 + \varepsilon = 7/6$,
every `{a, b} ∈ Erdos939Sums 4` satisfies $(a + b)^3 < K^4$ and $a + b \le K^4$. -/
theorem sum_cube_lt_and_sum_le_of_abc_seven_sixths_bound {K a b : ℕ}
    (habc : ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y →
      (x + y) ^ 6 ≤ K * rad (x * y * (x + y)) ^ 7)
    (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    (a + b) ^ 3 < K ^ 4 ∧ a + b ≤ K ^ 4 := by
  rcases (pair_mem_erdos939Sums_four_iff a b).mp hmem with ⟨ha, hb, hcop, _, _, _⟩
  have hlt : rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3 :=
    (rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four hmem).2.2.2.2
  have h6 : (a + b) ^ 6 ≤ K * rad (a * b * (a + b)) ^ 7 := habc a b ha hb hcop
  have h24 : ((a + b) ^ 6) ^ 4 ≤ (K * rad (a * b * (a + b)) ^ 7) ^ 4 :=
    Nat.pow_le_pow_left h6 4
  have h28 : (rad (a * b * (a + b)) ^ 4) ^ 7 < ((a + b) ^ 3) ^ 7 :=
    Nat.pow_lt_pow_left hlt (by omega)
  have hK_pos : 0 < K := by
    by_contra hK0
    have hK : K = 0 := by omega
    subst hK
    have h0 : (a + b) ^ 6 ≤ 0 := by simpa using h6
    have hpos6 : 0 < (a + b) ^ 6 := pow_pos (by omega) 6
    omega
  have hK4_pos : 0 < K ^ 4 := pow_pos hK_pos 4
  have hlt_mul : K ^ 4 * (rad (a * b * (a + b)) ^ 4) ^ 7 < K ^ 4 * ((a + b) ^ 3) ^ 7 :=
    Nat.mul_lt_mul_of_pos_left h28 hK4_pos
  have lhs_eq : ((a + b) ^ 6) ^ 4 = (a + b) ^ 3 * ((a + b) ^ 3) ^ 7 := by ring
  have mid_eq : (K * rad (a * b * (a + b)) ^ 7) ^ 4 = K ^ 4 * (rad (a * b * (a + b)) ^ 4) ^ 7 := by ring
  rw [lhs_eq, mid_eq] at h24
  have hcomb : (a + b) ^ 3 * ((a + b) ^ 3) ^ 7 < K ^ 4 * ((a + b) ^ 3) ^ 7 :=
    lt_of_le_of_lt h24 hlt_mul
  have hcube_lt : (a + b) ^ 3 < K ^ 4 := Nat.lt_of_mul_lt_mul_right hcomb
  have hself : a + b ≤ (a + b) ^ 3 := Nat.le_self_pow (by omega) (a + b)
  exact ⟨hcube_lt, by omega⟩

/-- **Conditional ABC Finiteness of `Erdos939Sums 4` (Explicit Constant Form):**
If $(x+y)^6 \le K\,\mathrm{rad}(xy(x+y))^7$ for all coprime positive $x, y$, then `Erdos939Sums 4` is finite. -/
theorem erdos939Sums_four_finite_of_abc_seven_sixths_bound {K : ℕ}
    (habc : ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y →
      (x + y) ^ 6 ≤ K * rad (x * y * (x + y)) ^ 7) :
    (Erdos939Sums 4).Finite :=
  erdos939Sums_four_finite_of_sum_bound fun _ _ hmem =>
    (sum_cube_lt_and_sum_le_of_abc_seven_sixths_bound habc hmem).2

/-- If no coprime positive pair has $abc$ quality $> 4/3$, then `Erdos939Sums 4 = ∅` and
`¬ (∀ r ≥ 4, (Erdos939Sums r).Nonempty)`. -/
theorem erdos939Sums_four_eq_empty_and_not_forall_of_strong_abc
    (habc : ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y →
      (x + y) ^ 3 ≤ rad (x * y * (x + y)) ^ 4) :
    Erdos939Sums 4 = ∅ ∧ ¬ (∀ r ≥ 4, (Erdos939Sums r).Nonempty) := by
  have hempty : Erdos939Sums 4 = ∅ := by
    ext S
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hS
    have hcard : S.card = 2 := hS.1
    rcases Finset.card_eq_two.mp hcard with ⟨a, b, _, rfl⟩
    have hle : a + b ≤ 0 :=
      sum_le_of_abc_four_thirds_threshold (B := 0) (fun x y hx hy hcop _ => habc x y hx hy hcop) hS
    rcases (pair_mem_erdos939Sums_four_iff a b).mp hS with ⟨ha, hb, _, _, _, _⟩
    omega
  refine ⟨hempty, ?_⟩
  intro hall
  have hne : (Erdos939Sums 4).Nonempty := hall 4 (by omega)
  rw [hempty] at hne
  exact Set.not_nonempty_empty hne

/-! ## Part 3: Cohn's (1998) Non-Cube $3$-Powerful Recurrence on $32 X^3 + 49 Y^3 = 81 Z^3$ -/

/-- **Cohn's Signed Cubic Tangent Identity ($\mathbb{Z}$ Form):** If $32 X^3 + 49 Y^3 = 81 Z^3$, then
$X' = X(49 Y^3 + 81 Z^3)$, $Y' = -Y(32 X^3 + 81 Z^3)$, $Z' = Z(32 X^3 - 49 Y^3)$ satisfy
$32 X'^3 + 49 Y'^3 = 81 Z'^3$ and preserve $7 \mid Y$. -/
theorem cohn_cubic_signed_tangent_identity (X Y Z : ℤ)
    (h : 32 * X ^ 3 + 49 * Y ^ 3 = 81 * Z ^ 3) :
    32 * (X * (49 * Y ^ 3 + 81 * Z ^ 3)) ^ 3 +
      49 * (- Y * (32 * X ^ 3 + 81 * Z ^ 3)) ^ 3 =
        81 * (Z * (32 * X ^ 3 - 49 * Y ^ 3)) ^ 3 ∧
      ((7 : ℤ) ∣ Y → (7 : ℤ) ∣ (- Y * (32 * X ^ 3 + 81 * Z ^ 3))) := by
  refine ⟨?_, ?_⟩
  · calc
      32 * (X * (49 * Y ^ 3 + 81 * Z ^ 3)) ^ 3 + 49 * (- Y * (32 * X ^ 3 + 81 * Z ^ 3)) ^ 3
        = (32 * X ^ 3) * (49 * Y ^ 3 + 81 * Z ^ 3) ^ 3 -
            (49 * Y ^ 3) * (32 * X ^ 3 + 81 * Z ^ 3) ^ 3 := by ring
      _ = (32 * X ^ 3) * (49 * Y ^ 3 + (32 * X ^ 3 + 49 * Y ^ 3)) ^ 3 -
            (49 * Y ^ 3) * (32 * X ^ 3 + (32 * X ^ 3 + 49 * Y ^ 3)) ^ 3 := by rw [← h]
      _ = (32 * X ^ 3 + 49 * Y ^ 3) * (32 * X ^ 3 - 49 * Y ^ 3) ^ 3 := by ring
      _ = (81 * Z ^ 3) * (32 * X ^ 3 - 49 * Y ^ 3) ^ 3 := by rw [h]
      _ = 81 * (Z * (32 * X ^ 3 - 49 * Y ^ 3)) ^ 3 := by ring
  · intro h7
    exact dvd_mul_of_dvd_left (dvd_neg.mpr h7) _

/-- **Cohn's Unsigned Tangent Step ($\mathbb{N}$ Form):** For $32 X^3 \le 49 Y^3$ with
$32 X^3 + 49 Y^3 = 81 Z^3$, $7 \mid Y$, and $\gcd(32 X^3, 49 Y^3) = 1$, the tangent step
$(X_1, Z_1, Y_1)$ satisfies $32 X_1^3 + 81 Z_1^3 = 49 Y_1^3$, $7 \mid Y_1$, and
$\gcd(32 X_1^3, 81 Z_1^3) = 1$. -/
theorem cohn_curve_nat_step_identity_and_coprime {X Y Z : ℕ}
    (huv : 32 * X ^ 3 ≤ 49 * Y ^ 3)
    (heq : 32 * X ^ 3 + 49 * Y ^ 3 = 81 * Z ^ 3)
    (h7 : 7 ∣ Y) (hcop : Nat.Coprime (32 * X ^ 3) (49 * Y ^ 3)) :
    let X₁ := X * (49 * Y ^ 3 + 81 * Z ^ 3)
    let Z₁ := Z * (49 * Y ^ 3 - 32 * X ^ 3)
    let Y₁ := Y * (32 * X ^ 3 + 81 * Z ^ 3)
    32 * X₁ ^ 3 + 81 * Z₁ ^ 3 = 49 * Y₁ ^ 3 ∧
      7 ∣ Y₁ ∧
      Nat.Coprime (32 * X₁ ^ 3) (81 * Z₁ ^ 3) := by
  intro X₁ Z₁ Y₁
  have h3dvd : 3 ∣ 32 * X ^ 3 ∨ 3 ∣ 49 * Y ^ 3 ∨ 3 ∣ 81 * Z ^ 3 :=
    Or.inr (Or.inr ⟨27 * Z ^ 3, by ring⟩)
  have hev := euler_viete_cubic_tangent_identity huv heq
  have hcop_ev := coprime_euler_viete_summands huv heq hcop h3dvd
  have hX1 : 32 * X₁ ^ 3 = (32 * X ^ 3) * (49 * Y ^ 3 + 81 * Z ^ 3) ^ 3 := by
    dsimp [X₁]; ring
  have hZ1 : 81 * Z₁ ^ 3 = (81 * Z ^ 3) * (49 * Y ^ 3 - 32 * X ^ 3) ^ 3 := by
    dsimp [Z₁]; ring
  have hY1 : 49 * Y₁ ^ 3 = (49 * Y ^ 3) * (32 * X ^ 3 + 81 * Z ^ 3) ^ 3 := by
    dsimp [Y₁]; ring
  refine ⟨?_, dvd_mul_of_dvd_left h7 _, ?_⟩
  · rw [hX1, hZ1, hY1]
    exact hev
  · rw [hX1, hZ1]
    exact hcop_ev

/-- Any integer $n$ whose prime factorization exponent at $p$ is not divisible by $3$ is not a cube. -/
theorem not_cube_of_factorization_mod_three_ne_zero (n p : ℕ)
    (hmod : n.factorization p % 3 ≠ 0) : ∀ k : ℕ, k ^ 3 ≠ n := by
  intro k hk
  have hfac : (k ^ 3).factorization p = n.factorization p := by rw [hk]
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
  omega

/-- Multiplying a positive integer $n$ by a positive cube $m^3$ preserves $v_p(n) \bmod 3$. -/
theorem factorization_mul_cube_mod_three {n m : ℕ} (p : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (n * m ^ 3).factorization p % 3 = n.factorization p % 3 := by
  have hm3 : m ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  rw [Nat.factorization_mul (by omega) hm3, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  omega

/-- For every $X > 0$, $32 X^3$ is $3$-powerful and never a perfect cube ($v_2(32 X^3) \equiv 2 \pmod{3}$). -/
theorem full_and_noncube_thirty_two_mul_cube {X : ℕ} (hX : 0 < X) :
    (3).Full (32 * X ^ 3) ∧
      (32 * X ^ 3).factorization 2 % 3 = 2 ∧
      ∀ k : ℕ, k ^ 3 ≠ 32 * X ^ 3 := by
  have hfull : (3).Full (32 * X ^ 3) := by
    have h32 : 32 = 2 ^ 5 := by norm_num
    rw [h32]
    exact full_mul_of_full 3 (2 ^ 5) (X ^ 3)
      ((prime_pow_full_iff 3 2 5 Nat.prime_two (by omega)).mpr (by omega))
      (full_of_pow_r_add_offset 3 0 X)
  have hfac : (32 * X ^ 3).factorization 2 % 3 = 2 := by
    rw [factorization_mul_cube_mod_three 2 (by omega) hX]
    have h32 : 32 = 2 ^ 5 := by norm_num
    rw [h32, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  refine ⟨hfull, hfac, not_cube_of_factorization_mod_three_ne_zero _ 2 (by omega)⟩

/-- For every $Y > 0$ with $7 \mid Y$, $49 Y^3$ is $3$-powerful and never a perfect cube ($v_7(49 Y^3) \equiv 2 \pmod{3}$). -/
theorem full_and_noncube_forty_nine_mul_cube {Y : ℕ} (hY : 0 < Y) (h7 : 7 ∣ Y) :
    (3).Full (49 * Y ^ 3) ∧
      (49 * Y ^ 3).factorization 7 % 3 = 2 ∧
      ∀ k : ℕ, k ^ 3 ≠ 49 * Y ^ 3 := by
  have hprime7 : Nat.Prime 7 := by decide
  rcases h7 with ⟨m, rfl⟩
  have hfull : (3).Full (49 * (7 * m) ^ 3) := by
    have heq : 49 * (7 * m) ^ 3 = 7 ^ 5 * m ^ 3 := by ring
    rw [heq]
    exact full_mul_of_full 3 (7 ^ 5) (m ^ 3)
      ((prime_pow_full_iff 3 7 5 hprime7 (by omega)).mpr (by omega))
      (full_of_pow_r_add_offset 3 0 m)
  have hfac : (49 * (7 * m) ^ 3).factorization 7 % 3 = 2 := by
    rw [factorization_mul_cube_mod_three 7 (by omega) hY]
    have h49 : 49 = 7 ^ 2 := by norm_num
    rw [h49, Nat.Prime.factorization_pow hprime7, Finsupp.single_eq_same]
  refine ⟨hfull, hfac, not_cube_of_factorization_mod_three_ne_zero _ 7 (by omega)⟩

/-- For every $Z > 0$, $81 Z^3$ is $3$-powerful and never a perfect cube ($v_3(81 Z^3) \equiv 1 \pmod{3}$). -/
theorem full_and_noncube_eighty_one_mul_cube {Z : ℕ} (hZ : 0 < Z) :
    (3).Full (81 * Z ^ 3) ∧
      (81 * Z ^ 3).factorization 3 % 3 = 1 ∧
      ∀ k : ℕ, k ^ 3 ≠ 81 * Z ^ 3 := by
  have hfull : (3).Full (81 * Z ^ 3) := by
    have h81 : 81 = 3 ^ 4 := by norm_num
    rw [h81]
    exact full_mul_of_full 3 (3 ^ 4) (Z ^ 3)
      ((prime_pow_full_iff 3 3 4 Nat.prime_three (by omega)).mpr (by omega))
      (full_of_pow_r_add_offset 3 0 Z)
  have hfac : (81 * Z ^ 3).factorization 3 % 3 = 1 := by
    rw [factorization_mul_cube_mod_three 3 (by omega) hZ]
    have h81 : 81 = 3 ^ 4 := by norm_num
    rw [h81, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  refine ⟨hfull, hfac, not_cube_of_factorization_mod_three_ne_zero _ 3 (by omega)⟩

/-- Invariant structure for Cohn's non-cube $3$-powerful triples: a Nitaj triple whose three terms
each have a prime factorization exponent not divisible by $3$. -/
structure IsCohnNonCubeTriple (u v w : ℕ) : Prop extends IsNitajTriple u v w where
  noncube_u : ∃ p : ℕ, u.factorization p % 3 ≠ 0
  noncube_v : ∃ p : ℕ, v.factorization p % 3 ≠ 0
  noncube_w : ∃ p : ℕ, w.factorization p % 3 ≠ 0

theorem isCohnNonCubeTriple_not_cubes {u v w : ℕ} (h : IsCohnNonCubeTriple u v w) :
    (∀ k : ℕ, k ^ 3 ≠ u) ∧ (∀ k : ℕ, k ^ 3 ≠ v) ∧ (∀ k : ℕ, k ^ 3 ≠ w) := by
  rcases h.noncube_u with ⟨pu, hpu⟩
  rcases h.noncube_v with ⟨pv, hpv⟩
  rcases h.noncube_w with ⟨pw, hpw⟩
  exact ⟨not_cube_of_factorization_mod_three_ne_zero u pu hpu,
    not_cube_of_factorization_mod_three_ne_zero v pv hpv,
    not_cube_of_factorization_mod_three_ne_zero w pw hpw⟩

theorem isCohnNonCubeTriple_symm {u v w : ℕ} (h : IsCohnNonCubeTriple u v w) :
    IsCohnNonCubeTriple v u w :=
  ⟨isNitajTriple_symm h.toIsNitajTriple, h.noncube_v, h.noncube_u, h.noncube_w⟩

theorem isCohnNonCubeTriple_ordered_step {u v w : ℕ}
    (h : IsCohnNonCubeTriple u v w) (huv : u ≤ v) :
    IsCohnNonCubeTriple (u * (v + w) ^ 3) (w * (v - u) ^ 3) (v * (u + w) ^ 3) ∧
      w < v * (u + w) ^ 3 := by
  have hstep := isNitajTriple_ordered_step h.toIsNitajTriple huv
  have hu : 0 < u := h.u_pos
  have hv : 0 < v := h.v_pos
  have hw_eq : u + v = w := h.sum_eq
  have hw_pos : 0 < w := by omega
  have huv_lt : u < v := by
    rcases eq_or_lt_of_le huv with rfl | hlt
    · have hu1 : u = 1 := h.coprime_uv.eq_one_of_dvd dvd_rfl
      rcases h.noncube_u with ⟨p, hp⟩
      rw [hu1, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply] at hp
      omega
    · exact hlt
  rcases h.noncube_u with ⟨pu, hpu⟩
  rcases h.noncube_v with ⟨pv, hpv⟩
  rcases h.noncube_w with ⟨pw, hpw⟩
  refine ⟨⟨hstep.1, ⟨pu, ?_⟩, ⟨pw, ?_⟩, ⟨pv, ?_⟩⟩, hstep.2⟩
  · rw [factorization_mul_cube_mod_three pu hu (by omega)]
    exact hpu
  · rw [factorization_mul_cube_mod_three pw hw_pos (by omega)]
    exact hpw
  · rw [factorization_mul_cube_mod_three pv hv (by omega)]
    exact hpv

theorem isCohnNonCubeTriple_nitajStep {t : ℕ × ℕ × ℕ}
    (h : IsCohnNonCubeTriple t.1 t.2.1 t.2.2) :
    IsCohnNonCubeTriple (nitajStep t).1 (nitajStep t).2.1 (nitajStep t).2.2 ∧
      t.2.2 < (nitajStep t).2.2 := by
  dsimp [nitajStep]
  rcases le_total t.1 t.2.1 with hle | hge
  · rw [min_eq_left hle, max_eq_right hle]
    exact isCohnNonCubeTriple_ordered_step h hle
  · rw [min_eq_right hge, max_eq_left hge]
    exact isCohnNonCubeTriple_ordered_step (isCohnNonCubeTriple_symm h) hge

/-- Every positive integer point $(X, Y, Z)$ on $32 X^3 + 49 Y^3 = 81 Z^3$ with $7 \mid Y$ and
$\gcd(32 X^3, 49 Y^3) = 1$ yields a valid `IsCohnNonCubeTriple`. -/
theorem isCohnNonCubeTriple_of_cohn_curve_point {X Y Z : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (heq : 32 * X ^ 3 + 49 * Y ^ 3 = 81 * Z ^ 3)
    (h7 : 7 ∣ Y) (hcop : Nat.Coprime (32 * X ^ 3) (49 * Y ^ 3)) :
    IsCohnNonCubeTriple (32 * X ^ 3) (49 * Y ^ 3) (81 * Z ^ 3) := by
  have h32 := full_and_noncube_thirty_two_mul_cube hX
  have h49 := full_and_noncube_forty_nine_mul_cube hY h7
  have h81 := full_and_noncube_eighty_one_mul_cube hZ
  have h3dvd : 3 ∣ 81 * Z ^ 3 := ⟨27 * Z ^ 3, by ring⟩
  refine ⟨⟨by positivity, by positivity, heq, hcop, Or.inr (Or.inr h3dvd),
    h32.1, h49.1, h81.1⟩, ⟨2, by omega⟩, ⟨7, by omega⟩, ⟨3, by omega⟩⟩

/-- Cohn's (1998) fundamental solution on $32 X^3 + 49 Y^3 = 81 Z^3$. -/
def cohnX0 : ℕ := 9712247684771506604963490444281
def cohnY0 : ℕ := 32295800804958334401937923416351
def cohnZ0 : ℕ := 27474621855216870941749052236511

def cohnSeed : ℕ × ℕ × ℕ :=
  (32 * cohnX0 ^ 3, 49 * cohnY0 ^ 3, 81 * cohnZ0 ^ 3)

theorem isCohnNonCubeTriple_cohnSeed :
    IsCohnNonCubeTriple cohnSeed.1 cohnSeed.2.1 cohnSeed.2.2 := by
  dsimp [cohnSeed]
  refine isCohnNonCubeTriple_of_cohn_curve_point
    (by norm_num [cohnX0]) (by norm_num [cohnY0]) (by norm_num [cohnZ0])
    (by norm_num [cohnX0, cohnY0, cohnZ0])
    (by norm_num [cohnY0])
    (by decide)

def cohnSeq (n : ℕ) : ℕ × ℕ × ℕ :=
  nitajStep^[n] cohnSeed

theorem isCohnNonCubeTriple_cohnSeq (n : ℕ) :
    IsCohnNonCubeTriple (cohnSeq n).1 (cohnSeq n).2.1 (cohnSeq n).2.2 := by
  induction n with
  | zero => exact isCohnNonCubeTriple_cohnSeed
  | succ n ih =>
    unfold cohnSeq
    rw [Function.iterate_succ_apply']
    exact (isCohnNonCubeTriple_nitajStep ih).1

theorem strictMono_cohnSeq_third :
    StrictMono (fun n : ℕ => (cohnSeq n).2.2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold cohnSeq
  rw [Function.iterate_succ_apply']
  exact (isCohnNonCubeTriple_nitajStep (isCohnNonCubeTriple_cohnSeq n)).2

theorem cohnSeq_mem_noncube_triples_set (n : ℕ) :
    cohnSeq n ∈ {(a, b, c) : ℕ × ℕ × ℕ |
      ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      (∀ k : ℕ, k ^ 3 ≠ a) ∧ (∀ k : ℕ, k ^ 3 ≠ b) ∧ (∀ k : ℕ, k ^ 3 ≠ c) ∧
      a + b = c} := by
  have h := isCohnNonCubeTriple_cohnSeq n
  have hnc := isCohnNonCubeTriple_not_cubes h
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, h.u_pos, h.v_pos, h.full_u, h.full_v, h.full_w, hnc.1, hnc.2.1, hnc.2.2, h.sum_eq⟩
  exact coprime_insert_of_coprime_pair {(cohnSeq n).1, (cohnSeq n).2.1, (cohnSeq n).2.2}
    (by simp) (by simp) h.coprime_uv

/-- **Cohn's (1998) Theorem on Non-Cube $3$-Powerful Triples:**
There are infinitely many triples $(a, b, c)$ of coprime positive $3$-powerful integers with
$a + b = c$ such that none of $a, b, c$ is a perfect cube. -/
theorem cohn_noncube_triples_infinite :
    {(a, b, c) : ℕ × ℕ × ℕ |
      ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      (∀ k : ℕ, k ^ 3 ≠ a) ∧ (∀ k : ℕ, k ^ 3 ≠ b) ∧ (∀ k : ℕ, k ^ 3 ≠ c) ∧
      a + b = c}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := cohnSeq)
  · intro m n hmn
    have h3 : (cohnSeq m).2.2 = (cohnSeq n).2.2 := by rw [hmn]
    exact strictMono_cohnSeq_third.injective h3
  · exact cohnSeq_mem_noncube_triples_set

theorem cohnSeq_pair_mem_noncube_generalSums (n : ℕ) :
    ({(cohnSeq n).1, (cohnSeq n).2.1} : Finset ℕ) ∈
      {S : Finset ℕ | S ∈ Erdos939GeneralSums 3 2 ∧
        (∀ k : ℕ, k ^ 3 ≠ ∑ s ∈ S, s) ∧
        ∀ s ∈ S, ∀ k : ℕ, k ^ 3 ≠ s} ∧
      ∑ s ∈ ({(cohnSeq n).1, (cohnSeq n).2.1} : Finset ℕ), s = (cohnSeq n).2.2 := by
  have h := isCohnNonCubeTriple_cohnSeq n
  have hnc := isCohnNonCubeTriple_not_cubes h
  have hmem : ({(cohnSeq n).1, (cohnSeq n).2.1} : Finset ℕ) ∈ Erdos939GeneralSums 3 2 := by
    rw [pair_mem_erdos939GeneralSums_two_iff 3 (cohnSeq n).1 (cohnSeq n).2.1 (by omega)]
    exact ⟨h.u_pos, h.v_pos, h.coprime_uv, h.full_u, h.full_v, h.sum_eq.symm ▸ h.full_w⟩
  have hne : (cohnSeq n).1 ≠ (cohnSeq n).2.1 :=
    ne_of_coprime_of_full_add 3 (cohnSeq n).1 (cohnSeq n).2.1 (by omega)
      h.u_pos h.coprime_uv (h.sum_eq.symm ▸ h.full_w)
  have hsum : ∑ s ∈ ({(cohnSeq n).1, (cohnSeq n).2.1} : Finset ℕ), s = (cohnSeq n).2.2 := by
    rw [Finset.sum_pair hne, h.sum_eq]
  refine ⟨⟨hmem, ?_, ?_⟩, hsum⟩
  · rw [hsum]
    exact hnc.2.2
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hnc.1
    · exact hnc.2.1

/-- **Infinitude of Non-Cube $2$-Element Sets in `Erdos939GeneralSums 3 2`:**
There are infinitely many $2$-element coprime $3$-powerful sets in `Erdos939GeneralSums 3 2`
whose elements and sum are all non-cubes. -/
theorem cohn_noncube_generalSums_three_two_infinite :
    {S : Finset ℕ | S ∈ Erdos939GeneralSums 3 2 ∧
      (∀ k : ℕ, k ^ 3 ≠ ∑ s ∈ S, s) ∧
      ∀ s ∈ S, ∀ k : ℕ, k ^ 3 ≠ s}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ({(cohnSeq n).1, (cohnSeq n).2.1} : Finset ℕ))
  · intro m n hmn
    have hm := (cohnSeq_pair_mem_noncube_generalSums m).2
    have hn := (cohnSeq_pair_mem_noncube_generalSums n).2
    change ({(cohnSeq m).1, (cohnSeq m).2.1} : Finset ℕ) =
      {(cohnSeq n).1, (cohnSeq n).2.1} at hmn
    have hsum : (cohnSeq m).2.2 = (cohnSeq n).2.2 := by
      rw [← hm, ← hn, hmn]
    exact strictMono_cohnSeq_third.injective hsum
  · intro n
    exact (cohnSeq_pair_mem_noncube_generalSums n).1


end Erdos939
