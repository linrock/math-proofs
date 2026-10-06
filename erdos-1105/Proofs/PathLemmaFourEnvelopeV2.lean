module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic

@[expose] public section

/-! No graph theorem or supplied envelope is imported. -/

namespace ErdosProblems.PathLemmaFourEnvelope

/-- The polynomial expression for a binomial coefficient of order two. -/
noncomputable def q (x : ℝ) : ℝ := x * (x - 1) / 2

/-- Transparent natural-number version of the published h expression. -/
def h (v p j : ℕ) : ℕ :=
  (p - j).choose 2 + j * (v - p + j)

/-- Clique cap below the forbidden path order; maximum-h cap above it. -/
def scalarCap (p v : ℕ) : ℕ :=
  if v ≤ p then v.choose 2 else max (h v p 1) (h v p ((p - 1) / 2))

/-- Exactly the natural choose/div/parity maximum in FC1105 part ii. -/
def pathFormula (n k : ℕ) : ℕ :=
  let ℓ := (k - 1) / 2
  let ε := if Odd k then 1 else 2
  max ((k - 2).choose 2 + 1)
    ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)

noncomputable def capR (P V B : ℝ) : ℝ :=
  if V ≤ P then q V
  else max (q (P - 1) + (V - P + 1))
    (q (P - B) + B * (V - P + B))

theorem cast_sub_eq (x y : ℕ) (hy : y ≤ x) :
    ((x - y : ℕ) : ℝ) = (x : ℝ) - (y : ℝ) := by
  have hn : (x - y) + y = x := by omega
  have hr : ((x - y : ℕ) : ℝ) + (y : ℝ) = (x : ℝ) := by
    exact_mod_cast hn
  linarith

theorem choose_cast (n : ℕ) :
    (n.choose 2 : ℝ) = q (n : ℝ) := by
  exact Nat.cast_choose_two ℝ n

theorem nonneg_of_pos_mul (x y : ℝ) (hx : 0 < x) (hxy : 0 ≤ x * y) :
    0 ≤ y := by
  by_contra hn
  have hy : y < 0 := lt_of_not_ge hn
  have hbad : x * y < 0 := mul_neg_of_pos_of_neg hx hy
  exact (not_lt_of_ge hxy) hbad

theorem h_cast (v p j : ℕ) (hj : j ≤ p) (hv : p ≤ v) :
    (h v p j : ℝ) =
      q ((p : ℝ) - (j : ℝ)) +
        (j : ℝ) * ((v : ℝ) - (p : ℝ) + (j : ℝ)) := by
  simp only [h, Nat.cast_add, Nat.cast_mul, choose_cast]
  rw [cast_sub_eq p j hj, cast_sub_eq v p hv]

theorem cap_cast (p v : ℕ) (hp : 2 ≤ p) (hv : p ≤ v) :
    (scalarCap p v : ℝ) =
      capR (p : ℝ) (v : ℝ) (((p - 1) / 2 : ℕ) : ℝ) := by
  have hb : (p - 1) / 2 ≤ p := by omega
  by_cases hle : v ≤ p
  · have hleR : (v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    simp only [scalarCap, capR, ite_eq_left hle, ite_eq_left hleR, choose_cast]
  · have hleR : ¬(v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    simp only [scalarCap, capR, ite_eq_right hle, ite_eq_right hleR, Nat.cast_max]
    rw [h_cast v p 1 (by omega) hv, h_cast v p ((p - 1) / 2) hb hv]
    simp only [Nat.cast_one, one_mul]

theorem formula_cast (p d N : ℕ) (hpd : d ≤ p) (hd : 2 ≤ d)
    (hN : p + d + 1 ≤ N) :
    (pathFormula N (p + d + 1) : ℝ) =
      max (q ((p : ℝ) + (d : ℝ) - 1) + 1)
        (((((p + d - 2) / 2 : ℕ) : ℝ)) * (N : ℝ) -
          q (((((p + d - 2) / 2 : ℕ) : ℝ)) + 1) +
          (1 + (((p + d - 2) % 2 : ℕ) : ℝ))) := by
  let a : ℕ := (p + d - 2) / 2
  let δ : ℕ := (p + d - 2) % 2
  have hk : p + d + 1 - 2 = p + d - 1 := by omega
  have he : (p + d + 1 - 1) / 2 - 1 = a := by dsimp [a]; omega
  have hn : N - (p + d + 1 - 1) / 2 + 1 = N - a := by
    dsimp [a]
    omega
  have haN : a ≤ N := by dsimp [a]; omega
  have hε : (if Odd (p + d + 1) then (1 : ℕ) else 2) = 1 + δ := by
    split_ifs with ho
    · have hm := Nat.odd_iff.mp ho
      dsimp [δ]
      omega
    · have hm := Nat.not_odd_iff.mp ho
      dsimp [δ]
      omega
  have hnat : pathFormula N (p + d + 1) =
      max ((p + d - 1).choose 2 + 1)
        (a.choose 2 + a * (N - a) + (1 + δ)) := by
    dsimp only [pathFormula]
    rw [hk, he, hn, hε]
  rw [hnat, Nat.cast_max]
  congr 1
  · rw [Nat.cast_add, choose_cast, Nat.cast_one,
      cast_sub_eq (p + d) 1 (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, choose_cast]
    rw [cast_sub_eq N a haN]
    change q (a : ℝ) + (a : ℝ) * ((N : ℝ) - (a : ℝ)) +
      (1 + (δ : ℝ)) =
      (a : ℝ) * (N : ℝ) - q ((a : ℝ) + 1) + (1 + (δ : ℝ))
    dsimp [q]
    ring

/-- Uniform affine domination for arbitrary nonnegative real tail size. -/
theorem scalar_affine_real (P D V U a b δ η : ℝ)
    (hpd : D ≤ P) (hd : 2 ≤ D) (hv : P ≤ V) (hU : 0 ≤ U)
    (hN : P + D + 1 ≤ V + U)
    (ha : 0 < a) (hda : D - 1 ≤ a) (hba : b ≤ a) (hb : 0 ≤ b)
    (hz : P + D = 2 * a + 2 + δ) (hp : P = 2 * b + 1 + η)
    (hδ : δ = 0 ∨ δ = 1) (hη : η = 0 ∨ η = 1) :
    capR P V b + ((D - 1) / 2 + 1 / D) * U ≤
      max (q (P + D - 1) + 1)
        (a * (V + U) - q (a + 1) + (1 + δ)) := by
  let N := V + U
  let c := (D - 1) / 2 + 1 / D
  let first := q (P + D - 1) + 1
  let lin := fun x : ℝ => a * x - q (a + 1) + (1 + δ)
  let q0 := fun x : ℝ => q P + c * (x - P)
  let qb := fun x : ℝ => b * x - q (b + 1) + η
  let nc := (5 * a + 3 + 4 * δ) / 2
  let T := (5 * (P + D) - 1) / 4
  have hdpos : 0 < D := by linarith
  have hdne : D ≠ 0 := ne_of_gt hdpos
  have hδ0 : 0 ≤ δ := by rcases hδ with h0 | h1 <;> linarith
  have hδ1 : δ ≤ 1 := by rcases hδ with h0 | h1 <;> linarith
  have hη0 : 0 ≤ η := by rcases hη with h0 | h1 <;> linarith
  have hη1 : η ≤ 1 := by rcases hη with h0 | h1 <;> linarith
  have hc1id : 2 * D * (c - 1) = (D - 1) * (D - 2) := by
    dsimp [c]
    field_simp [hdne]
    ring
  have hc1 : 1 ≤ c := by
    have hm : 0 ≤ (D - 1) * (D - 2) := mul_nonneg (by linarith) (by linarith)
    have hprod : 0 ≤ 2 * D * (c - 1) := by rw [hc1id]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) (c - 1) (by positivity) hprod
    linarith only [hsub]
  have hcdid : 2 * D * ((D - 1) - c) = (D - 2) * (D + 1) := by
    dsimp [c]
    field_simp [hdne]
    ring
  have hcd : c ≤ D - 1 := by
    have hm : 0 ≤ (D - 2) * (D + 1) := mul_nonneg (by linarith) (by linarith)
    have hprod : 0 ≤ 2 * D * ((D - 1) - c) := by rw [hcdid]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) ((D - 1) - c) (by positivity) hprod
    linarith only [hsub]
  have hca : c ≤ a := hcd.trans hda
  have hc0 : 0 ≤ c := by linarith
  have hintersection : first = lin nc := by
    dsimp [first, lin, nc]
    rw [hz]
    rcases hδ with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
  have hncT : nc ≤ T := by dsimp [nc, T]; linarith only [hz, hδ1]
  have hfactor :
      8 * D * (first - q0 T) =
        (P - D) * (7 * D * (D - 1) - 2) +
          (D - 2) * (6 * D ^ 2 - D + 1) + 4 := by
    dsimp [first, q0, T, c, q]
    field_simp [hdne]
    ring
  have hfpos : 0 < first - q0 T := by
    have hcoef : 0 ≤ 7 * D * (D - 1) - 2 := by
      nlinarith only [hd,
        mul_nonneg (by linarith : 0 ≤ D - 2) (by linarith : 0 ≤ D - 1)]
    have hpoly : 0 ≤ 6 * D ^ 2 - D + 1 := by
      nlinarith only [hd, sq_nonneg (D - 2)]
    have hright : 0 <
        (P - D) * (7 * D * (D - 1) - 2) +
          (D - 2) * (6 * D ^ 2 - D + 1) + 4 := by
      have hm1 := mul_nonneg (sub_nonneg.mpr hpd) hcoef
      have hm2 := mul_nonneg (by linarith : 0 ≤ D - 2) hpoly
      linarith
    have hprod : 0 < 8 * D * (first - q0 T) := by rw [hfactor]; exact hright
    by_contra hnot
    have hm : first - q0 T ≤ 0 := le_of_not_gt hnot
    have hbad := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 8 * D) hm
    linarith
  have hmid : q0 nc < first := by
    have hq : q0 nc ≤ q0 T := by
      dsimp [q0]
      nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hncT)]
    linarith only [hq, hfpos]
  have hq0 : q0 N ≤ max first (lin N) := by
    by_cases hsmall : N ≤ nc
    · have hq : q0 N ≤ q0 nc := by
        dsimp [q0]
        nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hsmall)]
      exact (hq.trans hmid.le).trans (le_max_left _ _)
    · have hmul : 0 ≤ (a - c) * (N - nc) :=
        mul_nonneg (sub_nonneg.mpr hca) (by linarith)
      have hi : lin N - q0 N =
          (lin nc - q0 nc) + (a - c) * (N - nc) := by
        dsimp [lin, q0]
        ring
      have hbase : 0 ≤ lin nc - q0 nc := by rw [← hintersection]; linarith
      have hq : q0 N ≤ lin N := by linarith only [hi, hmul, hbase]
      exact hq.trans (le_max_right _ _)
  have hqb : qb N ≤ max first (lin N) := by
    have hi : lin N - qb N =
        (a - b) * (N - (a + b + 1) / 2) + (1 + δ) - η := by
      dsimp [lin, qb, q]
      ring
    have hbracket : 0 ≤ N - (a + b + 1) / 2 := by
      dsimp [N]
      linarith only [hN, hz, hba, ha, hδ0]
    have hmul := mul_nonneg (sub_nonneg.mpr hba) hbracket
    have hq : qb N ≤ lin N := by linarith only [hi, hmul, hδ0, hη1]
    exact hq.trans (le_max_right _ _)
  have hbform (x : ℝ) :
      q (P - b) + b * (x - P + b) = b * x - q (b + 1) + η := by
    rw [hp]
    rcases hη with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
  have hbbase : q (P - b) + b * (P - P + b) ≤ q P := by
    have hi : q P - (q (P - b) + b * (P - P + b)) =
        b * (b + 1 + 2 * η) / 2 := by
      rw [hp]
      rcases hη with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
    have hm : 0 ≤ b * (b + 1 + 2 * η) := mul_nonneg hb (by linarith)
    nlinarith only [hi, hm]
  have hclique : q P + c * U ≤ max first (lin N) := by
    calc
      q P + c * U ≤ q0 N := by
        dsimp [q0, N]
        nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hv)]
      _ ≤ max first (lin N) := hq0
  have hfirst : q (P - 1) + (V - P + 1) + c * U ≤ max first (lin N) := by
    have hcore : q (P - 1) + (V - P + 1) ≤ q P + c * (V - P) := by
      have hm := mul_nonneg (by linarith : 0 ≤ c - 1) (sub_nonneg.mpr hv)
      dsimp [q]
      nlinarith only [hm, hd, hpd]
    calc
      q (P - 1) + (V - P + 1) + c * U ≤ q P + c * (V - P) + c * U :=
        add_le_add_left hcore _
      _ = q0 N := by dsimp [q0, N]; ring
      _ ≤ max first (lin N) := hq0
  have hsecond : q (P - b) + b * (V - P + b) + c * U ≤ max first (lin N) := by
    by_cases hbc : b ≤ c
    · have hcore : q (P - b) + b * (V - P + b) ≤ q P + c * (V - P) := by
        have hm := mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hv)
        nlinarith only [hbbase, hm]
      calc
        q (P - b) + b * (V - P + b) + c * U ≤ q P + c * (V - P) + c * U :=
          add_le_add_left hcore _
        _ = q0 N := by dsimp [q0, N]; ring
        _ ≤ max first (lin N) := hq0
    · have hcb : c * U ≤ b * U :=
        mul_le_mul_of_nonneg_right (lt_of_not_ge hbc).le hU
      calc
        q (P - b) + b * (V - P + b) + c * U ≤
            q (P - b) + b * (V - P + b) + b * U := add_le_add_right hcb _
        _ = qb N := by rw [hbform]; dsimp [qb, N]; ring
        _ ≤ max first (lin N) := hqb
  change capR P V b + c * U ≤ max first (lin N)
  by_cases hle : V ≤ P
  · have heq : V = P := le_antisymm hle hv
    simpa only [capR, heq, ite_eq_left (le_refl P)] using hclique
  · simp only [capR, ite_eq_right hle]
    rcases le_total (q (P - 1) + (V - P + 1))
        (q (P - b) + b * (V - P + b)) with hm | hm
    · rw [max_eq_right hm]
      exact hsecond
    · rw [max_eq_left hm]
      exact hfirst

/-- Direct uniform affine envelope for every natural tail size u.
The exact natural choose/div/parity formula is retained. No specific tail
decomposition, remainder premise, graph theorem or supplied envelope occurs. -/
theorem scalar_affine_envelope (p d v u : ℕ)
    (hpd : d ≤ p) (hd : 2 ≤ d) (hv : p ≤ v)
    (hN : p + d + 1 ≤ v + u) :
    (scalarCap p v : ℝ) +
      (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (u : ℝ) ≤
        (pathFormula (v + u) (p + d + 1) : ℝ) := by
  let a : ℕ := (p + d - 2) / 2
  let b : ℕ := (p - 1) / 2
  let δ : ℕ := (p + d - 2) % 2
  let η : ℕ := (p - 1) % 2
  have hz : p + d = 2 * a + 2 + δ := by dsimp [a, δ]; omega
  have hp : p = 2 * b + 1 + η := by dsimp [b, η]; omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hda : d - 1 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [b, a]; omega
  have hδ : δ = 0 ∨ δ = 1 := by dsimp [δ]; omega
  have hη : η = 0 ∨ η = 1 := by dsimp [η]; omega
  have hzR : (p : ℝ) + (d : ℝ) = 2 * (a : ℝ) + 2 + (δ : ℝ) := by
    exact_mod_cast hz
  have hpR : (p : ℝ) = 2 * (b : ℝ) + 1 + (η : ℝ) := by exact_mod_cast hp
  have hδR : (δ : ℝ) = 0 ∨ (δ : ℝ) = 1 := by
    rcases hδ with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hηR : (η : ℝ) = 0 ∨ (η : ℝ) = 1 := by
    rcases hη with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hdaR : (d : ℝ) - 1 ≤ (a : ℝ) := by
    have ht : d ≤ a + 1 := by
      calc
        d = (d - 1) + 1 := by omega
        _ ≤ a + 1 := Nat.add_le_add_right hda 1
    have htR : (d : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast ht
    linarith
  have hx := scalar_affine_real (p : ℝ) (d : ℝ) (v : ℝ) (u : ℝ)
    (a : ℝ) (b : ℝ) (δ : ℝ) (η : ℝ)
    (by exact_mod_cast hpd) (by exact_mod_cast hd) (by exact_mod_cast hv)
    (Nat.cast_nonneg u) (by exact_mod_cast hN)
    (by
      have ht : 0 < a := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) ha
      exact_mod_cast ht) hdaR
    (by exact_mod_cast hba) (Nat.cast_nonneg b) hzR hpR hδR hηR
  have hcap := cap_cast p v (by omega) hv
  have hform := formula_cast p d (v + u) hpd hd hN
  simpa only [Nat.cast_add, hcap, hform] using hx

end ErdosProblems.PathLemmaFourEnvelope

