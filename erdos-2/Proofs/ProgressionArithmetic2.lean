module

public import Mathlib


@[expose] public section

/-!
# Divisor decomposition and Chinese Remainder Theorem rectangle splitting

Decomposes divisors of $Q p^\gamma$ (with $p \nmid Q$) as $m p^j$ with $m \mid Q$
and $j \le \gamma$, and identifies residue classes modulo $m p^j$ in
$\mathbb{Z}/(Q p^\gamma)\mathbb{Z}$ with product rectangles in
$\mathbb{Z}/Q\mathbb{Z} \times \mathbb{Z}/p^\gamma\mathbb{Z}$.
-/

namespace Erdos2.ProgressionArithmetic


theorem divisor_decomposition {Q p γ d : ℕ} (hp : p.Prime)
    (hpQ : ¬p ∣ Q) (hd : d ∣ Q*p^γ) :
    ∃ m j : ℕ, m ∣ Q ∧ j ≤ γ ∧ d = m*p^j ∧ ¬p ∣ m := by
  have hc : Q.Coprime (p^γ) := (hp.coprime_iff_not_dvd.mpr hpQ).symm.pow_right γ
  have hg : d.gcd Q * d.gcd (p^γ) = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hc).mpr hd
  obtain ⟨j, hj, heq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right d (p^γ))
  refine ⟨d.gcd Q, j, Nat.gcd_dvd_right d Q, hj, ?_, ?_⟩
  · simpa [heq] using hg.symm
  · intro h
    exact hpQ (h.trans (Nat.gcd_dvd_right d Q))

theorem primeFactors_card_mul_prime_pow {m p j : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hpm : ¬p ∣ m) (hj : 0 < j) :
    (m*p^j).primeFactors.card = m.primeFactors.card + 1 := by
  rw [Nat.primeFactors_mul hm (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow (ne_of_gt hj) hp]
  have hn : p ∉ m.primeFactors := fun h => hpm (Nat.dvd_of_mem_primeFactors h)
  rw [Finset.union_singleton, Finset.card_insert_of_notMem hn]

theorem crt_reduction_pair {Q P m n : ℕ} (hcQ : Q.Coprime P)
    (hcm : m.Coprime n) (hm : m ∣ Q) (hn : n ∣ P)
    (a : ℤ) (z : ZMod (Q*P)) :
    ZMod.castHom (Nat.mul_dvd_mul hm hn) (ZMod (m*n)) z = (a : ZMod (m*n)) ↔
      ZMod.castHom hm (ZMod m) (ZMod.chineseRemainder hcQ z).1 = (a : ZMod m) ∧
      ZMod.castHom hn (ZMod n) (ZMod.chineseRemainder hcQ z).2 = (a : ZMod n) := by
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective z
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]
  change (t : ZMod (m*n)) = (a : ZMod (m*n)) ↔
    (t : ZMod m) = (a : ZMod m) ∧ (t : ZMod n) = (a : ZMod n)
  have hi := Int.modEq_and_modEq_iff_modEq_lcm
    (a := t) (b := a) (m := (m : ℤ)) (n := (n : ℤ))
  simpa only [ZMod.intCast_eq_intCast_iff, Int.lcm_def,
    Int.natAbs_natCast, hcm.lcm_eq_mul] using hi.symm

theorem crt_residue_mass_eq_rectangle {Q P m n : ℕ} [NeZero Q] [NeZero P]
    (hcQ : Q.Coprime P) (hcm : m.Coprime n) (hm : m ∣ Q) (hn : n ∣ P)
    (a : ℤ) (f : ZMod Q × ZMod P → ℝ) :
    (∑ z ∈ Finset.univ.filter (fun z : ZMod (Q*P) =>
      ZMod.castHom (Nat.mul_dvd_mul hm hn) (ZMod (m*n)) z = (a : ZMod (m*n))),
        f (ZMod.chineseRemainder hcQ z)) =
    ∑ x ∈ Finset.univ.filter (fun x : ZMod Q =>
      ZMod.castHom hm (ZMod m) x = (a : ZMod m)),
      ∑ y ∈ Finset.univ.filter (fun y : ZMod P =>
        ZMod.castHom hn (ZMod n) y = (a : ZMod n)), f (x,y) := by
  classical
  calc
    _ = ∑ xy ∈ Finset.product (Finset.univ.filter (fun x : ZMod Q =>
          ZMod.castHom hm (ZMod m) x = (a : ZMod m)))
        (Finset.univ.filter (fun y : ZMod P =>
          ZMod.castHom hn (ZMod n) y = (a : ZMod n))), f xy := by
      apply Finset.sum_equiv (ZMod.chineseRemainder hcQ).toEquiv
      · intro z
        simp only [Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact crt_reduction_pair hcQ hcm hm hn a z
      · intro z hz
        rfl
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]

theorem primeFactor_bound_ratio {m p j : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hpm : ¬p ∣ m) (hj : 0 < j) :
    (2 : ℝ) ^ (m*p^j).primeFactors.card / (m*p^j : ℕ) =
      (2 / (p^j : ℕ)) * ((2 : ℝ) ^ m.primeFactors.card / m) := by
  rw [primeFactors_card_mul_prime_pow hp hm hpm hj]
  push_cast
  simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

end Erdos2.ProgressionArithmetic
