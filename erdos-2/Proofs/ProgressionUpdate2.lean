module

public import ProgressionArithmetic2
public import ProductUpdate2
public import CongruenceGeometry2
public import Mathlib


@[expose] public section

/-!
# Preservation of progression-mass bounds across one prime step

Defines the invariant `HasProgressionBounds N w` requiring that every residue
class modulo any divisor $d \mid N$ has `w`-mass at most $2^{\omega(d)} / d$,
and proves that `crtUpdate` preserves this invariant when passing from $Q$ to
$Q p^\gamma$.
-/

namespace Erdos2.ProgressionUpdate

noncomputable def residueClass {N d : ℕ} [NeZero N]
    (hd : d ∣ N) (a : ℤ) : Finset (ZMod N) :=
  Finset.univ.filter (fun x => ZMod.castHom hd (ZMod d) x = (a : ZMod d))

noncomputable def residueMass {N d : ℕ} [NeZero N]
    (hd : d ∣ N) (a : ℤ) (w : ZMod N → ℝ) : ℝ :=
  ∑ x ∈ residueClass hd a, w x

def HasProgressionBounds (N : ℕ) [NeZero N] (w : ZMod N → ℝ) : Prop :=
  ∀ d : ℕ, ∀ hd : d ∣ N, ∀ a : ℤ,
    residueMass hd a w ≤ (2 : ℝ) ^ d.primeFactors.card / d

theorem residueClass_one {N : ℕ} [NeZero N] (a : ℤ) :
    residueClass (one_dvd N) a = Finset.univ := by
  classical
  ext x
  simp only [residueClass, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact Subsingleton.elim _ _

theorem bound_for_residue {N : ℕ} [NeZero N] (w : ZMod N → ℝ)
    (hw : HasProgressionBounds N w) (d : ℕ) (hd : d ∣ N) (a : ZMod d) :
    (∑ x ∈ Finset.univ.filter (fun x : ZMod N =>
      ZMod.castHom hd (ZMod d) x = a), w x) ≤
        (2 : ℝ)^d.primeFactors.card/d := by
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective a
  exact hw d hd t

noncomputable def crtUpdate {Q P : ℕ} [NeZero Q] [NeZero P]
    (hc : Q.Coprime P) (w : ProductProbability.ProbabilityWeight (ZMod Q))
    (B : ZMod Q → Finset (ZMod P)) :
    ProductProbability.ProbabilityWeight (ZMod (Q*P)) where
  value z := (ProductProbability.update w B).value (ZMod.chineseRemainder hc z)
  nonneg z := (ProductProbability.update w B).nonneg (ZMod.chineseRemainder hc z)
  normalized := by
    exact ((ZMod.chineseRemainder hc).toEquiv.sum_comp
      (ProductProbability.update w B).value).trans
        (ProductProbability.update w B).normalized

theorem crtUpdate_preserves_progressionBounds {Q p γ : ℕ} [NeZero Q] [NeZero p]
    (hp : p.Prime) (hpQ : ¬p ∣ Q)
    (w : ProductProbability.ProbabilityWeight (ZMod Q))
    (B : ZMod Q → Finset (ZMod (p^γ)))
    (hw : HasProgressionBounds Q w.value) :
    HasProgressionBounds (Q*p^γ)
      (crtUpdate ((hp.coprime_iff_not_dvd.mpr hpQ).symm.pow_right γ) w B).value := by
  intro d hd a
  obtain ⟨m, j, hm, hj, rfl, hpm⟩ :=
    ProgressionArithmetic.divisor_decomposition hp hpQ hd
  have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne Q) hm
  have hpow : p^j ∣ p^γ := Nat.pow_dvd_pow p hj
  have hc : Q.Coprime (p^γ) := (hp.coprime_iff_not_dvd.mpr hpQ).symm.pow_right γ
  have hcm : m.Coprime (p^j) := (hp.coprime_iff_not_dvd.mpr hpm).symm.pow_right j
  change (∑ z ∈ Finset.univ.filter (fun z : ZMod (Q*p^γ) =>
      ZMod.castHom hd (ZMod (m*p^j)) z = (a : ZMod (m*p^j))),
      (ProductProbability.update w B).value (ZMod.chineseRemainder hc z)) ≤
    (2 : ℝ)^(m*p^j).primeFactors.card/(m*p^j : ℕ)
  rw [ProgressionArithmetic.crt_residue_mass_eq_rectangle hc hcm hm hpow]
  change (∑ x ∈ residueClass hm a, ∑ y ∈ residueClass hpow a,
      (ProductProbability.update w B).value (x,y)) ≤
    (2 : ℝ)^(m*p^j).primeFactors.card/(m*p^j : ℕ)
  by_cases hj0 : j = 0
  · subst j
    simp only [pow_zero, mul_one] at *
    rw [residueClass_one, ProductProbability.update_preserves_cylinder]
    exact hw m hm a
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    let S : Finset (ZMod Q) := residueClass hm a
    let T : Finset (ZMod (p^γ)) := residueClass hpow a
    have hfrac : (T.card : ℝ)/Fintype.card (ZMod (p^γ)) = 1/(p^j : ℕ) := by
      simpa only [T, residueClass, ZMod.card] using
        CongruenceGeometry.reduction_uniform_fraction hpow (a : ZMod (p^j))
    have hcoef : 2*(T.card : ℝ)/Fintype.card (ZMod (p^γ)) = 2/(p^j : ℕ) := by
      calc
        _ = 2*((T.card : ℝ)/Fintype.card (ZMod (p^γ))) := by ring
        _ = 2*(1/(p^j : ℕ)) := by rw [hfrac]
        _ = _ := by ring
    calc
      _ ≤ (2*(T.card : ℝ)/Fintype.card (ZMod (p^γ))) *
          (∑ x ∈ S, w.value x) :=
        ProductProbability.update_rectangle_mass_le w B S T
      _ ≤ (2/(p^j : ℕ))*((2 : ℝ)^m.primeFactors.card/m) := by
        rw [hcoef]
        exact mul_le_mul_of_nonneg_left (hw m hm a) (by positivity)
      _ = _ := (ProgressionArithmetic.primeFactor_bound_ratio hp hm0 hpm hjpos).symm

end Erdos2.ProgressionUpdate
