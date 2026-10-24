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

public import Mathlib

@[expose] public section

noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics

namespace Erdos902.Core

/-- A **tournament** is a directed graph in which every pair of distinct vertices is connected
by exactly one directed edge (`FormalConjecturesForMathlib.Combinatorics.Digraph.Tournament`). -/
def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

/-- A vertex `v` dominates a finset `S` in a digraph `G` if `G.Adj v u` holds for every `u ∈ S`. -/
def Dominates {V : Type*} (G : Digraph V) (v : V) (S : Finset V) : Prop :=
  ∀ u ∈ S, G.Adj v u

/-- The strict out-neighborhood of `v` in `G : Digraph (Fin N)`. -/
def outNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj v u)

/-- The strict in-neighborhood of `v` in `G : Digraph (Fin N)`. -/
def inNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj u v)

/-- Common out-neighborhood `outNeigh G u ∩ outNeigh G v` of two vertices `u, v : Fin N`. -/
def commonOutNeigh {N : ℕ} (G : Digraph (Fin N)) (u v : Fin N) : Finset (Fin N) :=
  outNeigh G u ∩ outNeigh G v

/-- A digraph `G` on a finite vertex type `V` is an `n`-paradoxical tournament (Schütte's
property) if `G` is a tournament, `V` has at least `n` vertices, and every `n`-element subset of
`V` is dominated by at least one vertex. -/
def IsParadoxicalTournament {V : Type*} [Fintype V] (n : ℕ) (G : Digraph V) : Prop :=
  IsTournament G ∧ n ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card = n → ∃ v : V, Dominates G v S

/-- There exists an `n`-paradoxical tournament on `Fin N`. -/
def HasParadoxicalTournament (n N : ℕ) : Prop :=
  ∃ G : Digraph (Fin N), IsParadoxicalTournament n G

/-- `f n` is the minimum number of vertices `N` such that there exists an `n`-paradoxical
tournament on `Fin N` (Erdős Problem #902). -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {N : ℕ | HasParadoxicalTournament n N}

/-- Exact integer form of Erdős's (1963) random-tournament union-bound criterion:
`\binom{N}{n} (2^n - 1)^{N - n} < (2^n)^{N - n}`. -/
def ErdosProbabilisticCriterion (n N : ℕ) : Prop :=
  N.choose n * (2 ^ n - 1) ^ (N - n) < (2 ^ n) ^ (N - n)

/-- The directed 3-cycle Paley tournament `0 → 1 → 2 → 0` on `Fin 3`. -/
def paley3Digraph : Digraph (Fin 3) where
  Adj u v := (v.val + 3 - u.val) % 3 = 1

/-- The 7-vertex Paley tournament `QR_7` on `Fin 7` (quadratic residues `{1, 2, 4} mod 7`). -/
def paley7Digraph : Digraph (Fin 7) where
  Adj u v :=
    let d := (v.val + 7 - u.val) % 7
    d = 1 ∨ d = 2 ∨ d = 4

/-- Boolean test for the 9 nonzero quadratic residues `{1, 4, 5, 6, 7, 9, 11, 16, 17} mod 19`. -/
def isQR19 (d : ℕ) : Bool :=
  d == 1 || d == 4 || d == 5 || d == 6 || d == 7 || d == 9 || d == 11 || d == 16 || d == 17

/-- The 19-vertex Paley tournament `QR_19` on `Fin 19`. -/
def paley19Digraph : Digraph (Fin 19) where
  Adj u v := isQR19 ((v.val + 19 - u.val) % 19) = true

/-- Boolean test for the 33 nonzero quadratic residues modulo 67. -/
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

/-- The 67-vertex Paley tournament `QR_67` on `Fin 67`. -/
def paley67Digraph : Digraph (Fin 67) where
  Adj u v := isQR67 ((v.val + 67 - u.val) % 67) = true

/-- The general Paley (quadratic-residue) digraph on `Fin p`: there is a directed edge `u → v`
iff `(u.val : ZMod p) ≠ (v.val : ZMod p)` and `(v.val : ZMod p) - (u.val : ZMod p)` is a square
in `ZMod p`. -/
def paleyFinDigraph (p : ℕ) : Digraph (Fin p) where
  Adj u v := (u.val : ZMod p) ≠ (v.val : ZMod p) ∧ IsSquare ((v.val : ZMod p) - (u.val : ZMod p))

/-- Exact evaluation `f(0) = 1` and threshold `HasParadoxicalTournament 0 N ↔ 1 ≤ N`. -/
theorem hasParadoxicalTournament_zero_iff_and_f_zero (N : ℕ) :
    (HasParadoxicalTournament 0 N ↔ 1 ≤ N) ∧ f 0 = 1 := by
  sorry

/-- Exact evaluation `f(1) = 3` and threshold `HasParadoxicalTournament 1 N ↔ 3 ≤ N` via
`paley3Digraph`. -/
theorem hasParadoxicalTournament_one_iff_and_f_one (N : ℕ) :
    IsParadoxicalTournament 1 paley3Digraph ∧
      (HasParadoxicalTournament 1 N ↔ 3 ≤ N) ∧ f 1 = 3 := by
  sorry

/-- Exact evaluation `f(2) = 7` and threshold `HasParadoxicalTournament 2 N ↔ 7 ≤ N` via the
7-vertex Paley tournament `QR_7` (`paley7Digraph`). -/
theorem paley7Digraph_dom2_and_f_two (N : ℕ) :
    IsParadoxicalTournament 2 paley7Digraph ∧
      (HasParadoxicalTournament 2 N ↔ 7 ≤ N) ∧ f 2 = 7 := by
  sorry

/-- Bounds `14 ≤ f(3) ≤ 19` and exact Szekeres–Szekeres evaluation `f(3) = 19` with threshold
`HasParadoxicalTournament 3 N ↔ 19 ≤ N` via the 19-vertex Paley tournament `QR_19`
(`paley19Digraph`). -/
theorem hasParadoxicalTournament_three_iff_and_f_three (N : ℕ) :
    IsParadoxicalTournament 3 paley19Digraph ∧
      (HasParadoxicalTournament 3 N ↔ 19 ≤ N) ∧
      14 ≤ f 3 ∧ f 3 ≤ 19 ∧ f 3 = 19 := by
  sorry

/-- Constructive 4-paradoxicality of the 67-vertex Paley tournament `QR_67` (`paley67Digraph`)
and two-sided interval `47 ≤ f(4) ≤ 67`. -/
theorem hasParadoxicalTournament_four_67_and_f_four_bounds :
    IsParadoxicalTournament 4 paley67Digraph ∧
      HasParadoxicalTournament 4 67 ∧ 47 ≤ f 4 ∧ f 4 ≤ 67 := by
  sorry

/-- Unconditional Erdős (1963) lower bound `f(k) ≥ 2^(k+1) - 1` and Szekeres–Szekeres (1965)
lower bound `f(k) ≥ (k + 2) * 2^(k - 1) - 1` for all `k` and all `k`-paradoxical tournaments. -/
theorem erdos_and_szekeres_lower_bounds (k N : ℕ) :
    (HasParadoxicalTournament k N → 2 ^ (k + 1) - 1 ≤ N ∧ 2 ^ k ≤ N) ∧
      (1 ≤ k → 2 ^ (k + 1) - 1 ≤ f k ∧ (k + 2) * 2 ^ (k - 1) - 1 ≤ f k) ∧
      (1 ≤ k → HasParadoxicalTournament k N →
        (k + 2) * 2 ^ (k - 1) - 1 ≤ N ∧ k * 2 ^ (k - 1) < N) := by
  sorry

/-- Erdős's (1963) finite tournament orientation-space union-bound bridge: for all `n ≤ N`, if
`ErdosProbabilisticCriterion n N` holds, then `HasParadoxicalTournament n N` holds. -/
theorem hasParadoxicalTournament_of_erdosProbabilisticCriterion {n N : ℕ}
    (hnN : n ≤ N) (hcrit : ErdosProbabilisticCriterion n N) :
    HasParadoxicalTournament n N := by
  sorry

/-- Unconditional two-sided Erdős–Szekeres–Szekeres sandwich for `f(n)` (`1 ≤ n`):
`2^(n+1) - 1 ≤ f(n)`, `(n + 2) * 2^(n - 1) - 1 ≤ f(n)`, `f(n) ≤ n + 2 * n * (n + 1) * 2^n`,
and `f(n) ≤ 5 * n^2 * 2^n`. -/
theorem erdos_szekeres_f_sandwich (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 1) - 1 ≤ f n ∧
      (n + 2) * 2 ^ (n - 1) - 1 ≤ f n ∧
      f n ≤ n + 2 * n * (n + 1) * 2 ^ n ∧
      f n ≤ 5 * n ^ 2 * 2 ^ n := by
  sorry

/-- Probabilistic upper bounds: the unit-leading-coefficient bounds
`f(n) ≤ n * (n + 1) * 2^n` and `f(n) ≤ n + (n^2 + 5) * 2^n` for all `1 ≤ n`,
`f(n) ≤ n^2 * 2^n` for all `11 ≤ n`, and explicit mid-range bounds for `5 ≤ n ≤ 10`. -/
theorem unit_leading_and_quintic_upper_bounds :
    (∀ n : ℕ, 1 ≤ n →
      HasParadoxicalTournament n (n * (n + 1) * 2 ^ n) ∧
        f n ≤ n * (n + 1) * 2 ^ n ∧
        f n ≤ n + (n ^ 2 + 5) * 2 ^ n) ∧
      (∀ n : ℕ, 11 ≤ n →
        HasParadoxicalTournament n (n ^ 2 * 2 ^ n) ∧ f n ≤ n ^ 2 * 2 ^ n) ∧
      f 5 ≤ 965 ∧ f 6 ≤ 2630 ∧ f 7 ≤ 6919 ∧ f 8 ≤ 17416 ∧ f 9 ≤ 43017 ∧ f 10 ≤ 103434 := by
  sorry

/-- General Paley tournament construction on `Fin p` for every prime `p ≡ 3 [MOD 4]`:
`paleyFinDigraph p` is a regular tournament of out-degree and in-degree `(p - 1) / 2`. -/
theorem isTournament_and_regular_paleyFinDigraph {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    IsTournament (paleyFinDigraph p) ∧
      ∀ u : Fin p,
        (outNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 ∧
          (inNeigh (paleyFinDigraph p) u).card = (p - 1) / 2 := by
  sorry

/-- Deterministic second-moment pairwise out-neighborhood intersection paradoxicality criterion:
if `G` is a tournament on `Fin N` (`k ≤ N`) and
`(N.choose k - 1) * ∑ u, ∑ v, (commonOutNeigh G u v).card.choose k < (∑ v, (outNeigh G v).card.choose k)^2`,
then `G` is `k`-paradoxical. -/
theorem isParadoxicalTournament_of_second_moment_commonOutNeigh {k N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (hkN : k ≤ N)
    (hsm : (N.choose k - 1) * (∑ u : Fin N, ∑ v : Fin N, (commonOutNeigh G u v).card.choose k) <
      (∑ v : Fin N, (outNeigh G v).card.choose k) ^ 2) :
    IsParadoxicalTournament k G := by
  sorry

/-- Dyadic `(29, 79)` lower bound for `n ≥ 8` and complete falsification of the first-moment
union-bound criterion `ErdosProbabilisticCriterion n (n^2 * 2^n)` for all `1 ≤ n ≤ 10`. -/
theorem twenty_nine_seventy_nine_lower_bound_and_not_criterion_ten :
    (∀ n : ℕ, 8 ≤ n → 29 * (2 ^ n) ^ (2 ^ n) ≤ 79 * (2 ^ n - 1) ^ (2 ^ n)) ∧
      ¬ ErdosProbabilisticCriterion 10 (10 ^ 2 * 2 ^ 10) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ 10 → ¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)) := by
  sorry

end Erdos902.Core

namespace Erdos902

/-- `HasPropertyS G n` is Schütte's property $S_n$: every set `E` of `n` vertices is dominated by
a vertex outside it. -/
def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

/-- `f n` is the least number of vertices of a tournament with property `S_n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), Erdos902.Core.IsTournament G ∧ HasPropertyS G n}

/--
It is easy to check that $f(1)=3$ and $f(2)=7$.

This is the statement for $f(2)$.
-/
theorem erdos_902.variants.f_two : f 2 = 7 := by
  sorry

/--
Erdős [Er63c] proved
$$2^{n+1}-1 \leq f(n) \ll n^22^n.$$

This is the lower bound.
-/
theorem erdos_902.variants.erdos_lower (n : ℕ) : 2 ^ (n + 1) - 1 ≤ f n := by
  sorry

/--
Szekeres and Szekeres [SzSz65] proved that $f(3)=19$ and
$$n2^n \ll f(n).$$

This is the statement for $f(3)$.
-/
theorem erdos_902.variants.szekeres_f_three : f 3 = 19 := by
  sorry

/--
Szekeres and Szekeres [SzSz65] proved that $f(3)=19$ and
$$n2^n \ll f(n).$$

This is the lower bound.
-/
theorem erdos_902.variants.szekeres_lower :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * n * 2 ^ n ≤ (f n : ℝ) := by
  sorry

end Erdos902
end
