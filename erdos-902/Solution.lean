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

public import SolutionUpstream902

@[expose] public section

noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics

namespace Erdos902.Core

def Dominates {V : Type*} (G : Digraph V) (v : V) (S : Finset V) : Prop :=
  ∀ u ∈ S, G.Adj v u

def outNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj v u)

def inNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj u v)

def commonOutNeigh {N : ℕ} (G : Digraph (Fin N)) (u v : Fin N) : Finset (Fin N) :=
  outNeigh G u ∩ outNeigh G v

def IsParadoxicalTournament {V : Type*} [Fintype V] (n : ℕ) (G : Digraph V) : Prop :=
  IsTournament G ∧ n ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card = n → ∃ v : V, Dominates G v S

def HasParadoxicalTournament (n N : ℕ) : Prop :=
  ∃ G : Digraph (Fin N), IsParadoxicalTournament n G

noncomputable def f (n : ℕ) : ℕ :=
  sInf {N : ℕ | HasParadoxicalTournament n N}

def ErdosProbabilisticCriterion (n N : ℕ) : Prop :=
  N.choose n * (2 ^ n - 1) ^ (N - n) < (2 ^ n) ^ (N - n)

def paley3Digraph : Digraph (Fin 3) where
  Adj u v := (v.val + 3 - u.val) % 3 = 1

def paley7Digraph : Digraph (Fin 7) where
  Adj u v :=
    let d := (v.val + 7 - u.val) % 7
    d = 1 ∨ d = 2 ∨ d = 4

def isQR19 (d : ℕ) : Bool :=
  d == 1 || d == 4 || d == 5 || d == 6 || d == 7 || d == 9 || d == 11 || d == 16 || d == 17

def paley19Digraph : Digraph (Fin 19) where
  Adj u v := isQR19 ((v.val + 19 - u.val) % 19) = true

def isQR67 (d : ℕ) : Bool :=
  if d < 29 then
    if d < 16 then
      if d < 9 then
        if d < 4 then (d == 1) else if d == 4 then true else (d == 6)
      else if d == 9 then true else
        if d < 14 then (d == 10) else if d == 14 then true else (d == 15)
    else if d == 16 then true else
      if d < 22 then
        if d < 19 then (d == 17) else if d == 19 then true else (d == 21)
      else if d == 22 then true else
        if d < 24 then (d == 23) else if d == 24 then true else
          if d < 26 then (d == 25) else (d == 26)
  else if d == 29 then true else
    if d < 47 then
      if d < 37 then
        if d < 35 then (d == 33) else if d == 35 then true else (d == 36)
      else if d == 37 then true else
        if d < 40 then (d == 39) else (d == 40)
    else if d == 47 then true else
      if d < 59 then
        if d < 55 then
          if d < 54 then (d == 49) else (d == 54)
        else if d == 55 then true else (d == 56)
      else if d == 59 then true else
        if d < 64 then
          if d < 62 then (d == 60) else (d == 62)
        else if d == 64 then true else (d == 65)

def paley67Digraph : Digraph (Fin 67) where
  Adj u v := isQR67 ((v.val + 67 - u.val) % 67) = true

def paleyFinDigraph (p : ℕ) : Digraph (Fin p) where
  Adj u v := (u.val : ZMod p) ≠ (v.val : ZMod p) ∧ IsSquare ((v.val : ZMod p) - (u.val : ZMod p))

theorem hasParadoxicalTournament_zero_iff_and_f_zero (N : ℕ) :
    (HasParadoxicalTournament 0 N ↔ 1 ≤ N) ∧ f 0 = 1 :=
  Erdos902.hasParadoxicalTournament_zero_iff_and_f_zero N

theorem hasParadoxicalTournament_one_iff_and_f_one (N : ℕ) :
    IsParadoxicalTournament 1 paley3Digraph ∧
      (HasParadoxicalTournament 1 N ↔ 3 ≤ N) ∧ f 1 = 3 :=
  ⟨Erdos902.isParadoxicalTournament_paley3Digraph,
    Erdos902.hasParadoxicalTournament_one_iff_and_f_one N⟩

theorem paley7Digraph_dom2_and_f_two (N : ℕ) :
    IsParadoxicalTournament 2 paley7Digraph ∧
      (HasParadoxicalTournament 2 N ↔ 7 ≤ N) ∧ f 2 = 7 := by
  have h2 := Erdos902.paley7Digraph_dom2_and_f_two N
  have hpaley : IsParadoxicalTournament 2 paley7Digraph := by
    refine ⟨⟨by dsimp [paley7Digraph]; decide, by dsimp [paley7Digraph]; decide⟩, by decide, ?_⟩
    intro S hScard
    rcases Finset.card_eq_two.mp hScard with ⟨a, b, _, rfl⟩
    have hdom : ∀ x y : Fin 7, ∃ v : Fin 7, paley7Digraph.Adj v x ∧ paley7Digraph.Adj v y := by
      dsimp [paley7Digraph]
      decide
    obtain ⟨v, hva, hvb⟩ := hdom a b
    refine ⟨v, fun u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu2
    · exact hva
    · rw [Finset.mem_singleton.mp hu2]
      exact hvb
  exact ⟨hpaley, h2⟩

theorem hasParadoxicalTournament_three_iff_and_f_three (N : ℕ) :
    IsParadoxicalTournament 3 paley19Digraph ∧
      (HasParadoxicalTournament 3 N ↔ 19 ≤ N) ∧
      14 ≤ f 3 ∧ f 3 ≤ 19 ∧ f 3 = 19 := by
  have h3 := Erdos902.hasParadoxicalTournament_three_iff_and_f_three N
  have hpaley : IsParadoxicalTournament 3 paley19Digraph := by
    refine ⟨⟨by dsimp [paley19Digraph]; decide, by dsimp [paley19Digraph]; decide⟩, by decide, ?_⟩
    intro S hScard
    rcases Finset.card_eq_three.mp hScard with ⟨a, b, c, _, _, _, rfl⟩
    obtain ⟨v, hva, hvb, hvc⟩ := Erdos902.paley19Digraph_dom3_all a b c
    refine ⟨v, fun u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu2
    · exact hva
    · rcases Finset.mem_insert.mp hu2 with rfl | hu3
      · exact hvb
      · rw [Finset.mem_singleton.mp hu3]
        exact hvc
  have hf3 : f 3 = 19 := h3.2
  exact ⟨hpaley, h3.1, by omega, by omega, hf3⟩

theorem hasParadoxicalTournament_four_67_and_f_four_bounds :
    IsParadoxicalTournament 4 paley67Digraph ∧
      HasParadoxicalTournament 4 67 ∧ 47 ≤ f 4 ∧ f 4 ≤ 67 :=
  ⟨Erdos902.isParadoxicalTournament_paley67Digraph,
    Erdos902.hasParadoxicalTournament_four_67_and_f_four_bounds⟩

theorem erdos_and_szekeres_lower_bounds (k N : ℕ) :
    (HasParadoxicalTournament k N → 2 ^ (k + 1) - 1 ≤ N ∧ 2 ^ k ≤ N) ∧
      (1 ≤ k → 2 ^ (k + 1) - 1 ≤ f k ∧ (k + 2) * 2 ^ (k - 1) - 1 ≤ f k) ∧
      (1 ≤ k → HasParadoxicalTournament k N →
        (k + 2) * 2 ^ (k - 1) - 1 ≤ N ∧ k * 2 ^ (k - 1) < N) := by
  refine ⟨fun h => Erdos902.erdos_lower_bound_of_hasParadoxicalTournament k N h,
    fun hk => ?_, fun hk h => ?_⟩
  · have hsand := Erdos902.erdos_szekeres_f_sandwich k hk
    exact ⟨hsand.1, hsand.2.1⟩
  · have hsz := Erdos902.szekeres_lower_bound_of_hasParadoxicalTournament k N hk h
    exact ⟨hsz.1, hsz.2.1⟩

theorem hasParadoxicalTournament_of_erdosProbabilisticCriterion {n N : ℕ}
    (hnN : n ≤ N) (hcrit : ErdosProbabilisticCriterion n N) :
    HasParadoxicalTournament n N :=
  (Erdos902.hasParadoxicalTournament_of_erdosProbabilisticCriterion hnN hcrit).2

theorem erdos_szekeres_f_sandwich (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 1) - 1 ≤ f n ∧
      (n + 2) * 2 ^ (n - 1) - 1 ≤ f n ∧
      f n ≤ n + 2 * n * (n + 1) * 2 ^ n ∧
      f n ≤ 5 * n ^ 2 * 2 ^ n :=
  Erdos902.erdos_szekeres_f_sandwich n hn

theorem unit_leading_and_quintic_upper_bounds :
    (∀ n : ℕ, 1 ≤ n →
      HasParadoxicalTournament n (n * (n + 1) * 2 ^ n) ∧
        f n ≤ n * (n + 1) * 2 ^ n ∧
        f n ≤ n + (n ^ 2 + 5) * 2 ^ n) ∧
      (∀ n : ℕ, 11 ≤ n →
        HasParadoxicalTournament n (n ^ 2 * 2 ^ n) ∧ f n ≤ n ^ 2 * 2 ^ n) ∧
      f 5 ≤ 965 ∧ f 6 ≤ 2630 ∧ f 7 ≤ 6919 ∧ f 8 ≤ 17416 ∧ f 9 ≤ 43017 ∧ f 10 ≤ 103434 := by
  have hmid := Erdos902.mid_range_quintic_upper_bounds_and_global_add_five
  refine ⟨fun n hn => ?_, fun n hn11 => ?_,
    hmid.1, hmid.2.1, hmid.2.2.1, hmid.2.2.2.1, hmid.2.2.2.2.1, hmid.2.2.2.2.2.1⟩
  · have hu := Erdos902.hasParadoxicalTournament_and_f_le_mul_add_one_two_pow n hn
    exact ⟨hu.1, hu.2.1, hmid.2.2.2.2.2.2 n hn⟩
  · have h11 := Erdos902.hasParadoxicalTournament_and_f_le_sq_mul_two_pow_of_eleven_le hn11
    exact ⟨h11.1, h11.2.1⟩

theorem isTournament_and_regular_paleyFinDigraph {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    IsTournament (paleyFinDigraph p) ∧
      ∀ u : Fin p,
        (outNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 ∧
          (inNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 := by
  have h := Erdos902.isTournament_and_regular_paleyFinDigraph hp
  exact ⟨h.1, h.2.1⟩

theorem isParadoxicalTournament_of_second_moment_commonOutNeigh {k N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (hkN : k ≤ N)
    (hsm : (N.choose k - 1) * (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) <
      (∑ v : Fin N, (outNeigh G v).card.choose k) ^ 2) :
    IsParadoxicalTournament k G :=
  Erdos902.isParadoxicalTournament_of_second_moment_commonOutNeigh hG hkN hsm

theorem twenty_nine_seventy_nine_lower_bound_and_not_criterion_ten :
    (∀ n : ℕ, 8 ≤ n → 29 * (2 ^ n) ^ (2 ^ n) ≤ 79 * (2 ^ n - 1) ^ (2 ^ n)) ∧
      ¬ ErdosProbabilisticCriterion 10 (10 ^ 2 * 2 ^ 10) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ 10 → ¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)) :=
  Erdos902.twenty_nine_seventy_nine_lower_bound_and_not_criterion_ten

end Erdos902.Core

namespace Erdos902

/-- Upstream `erdos_902.variants.f_two`. -/
theorem erdos_902.variants.f_two : f 2 = 7 :=
  (Erdos902.paley7Digraph_dom2_and_upstream_f_two 7).2.2

/-- Upstream `erdos_902.variants.erdos_lower`. -/
theorem erdos_902.variants.erdos_lower (n : ℕ) : 2 ^ (n + 1) - 1 ≤ f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(Erdos902.hasParadoxicalTournament_zero_iff_and_upstream_f_zero 1).2]
    norm_num
  · exact (Erdos902.erdos_szekeres_upstream_f_sandwich n hn).1

/-- Upstream `erdos_902.variants.szekeres_f_three`. -/
theorem erdos_902.variants.szekeres_f_three : f 3 = 19 :=
  (Erdos902.hasParadoxicalTournament_three_iff_and_upstream_f_three 19).2.2.2.2

/-- Upstream `erdos_902.variants.szekeres_lower`. -/
theorem erdos_902.variants.szekeres_lower :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * n * 2 ^ n ≤ (f n : ℝ) := by
  refine ⟨(1 : ℝ) / 4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hsz : (n + 2) * 2 ^ (n - 1) - 1 ≤ f n :=
    (Erdos902.erdos_szekeres_upstream_f_sandwich n hn).2.1
  have hszR : ((n : ℝ) + 2) * (2 : ℝ) ^ (n - 1) - 1 ≤ (f n : ℝ) := by
    have hpos : 1 ≤ (n + 2) * 2 ^ (n - 1) := by
      have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ 2 (by decide)
      nlinarith
    have hsz' : (n + 2) * 2 ^ (n - 1) ≤ f n + 1 := by omega
    have hcast : (((n : ℕ) + 2) * 2 ^ (n - 1) : ℝ) ≤ (f n : ℝ) + 1 := by
      exact_mod_cast hsz'
    linarith
  have hpowR : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  rw [hpowR]
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

end Erdos902
end
