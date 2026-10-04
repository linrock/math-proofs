module

public import CoveringModel2
public import ProgressionUpdate2
public import RectangleMoment2
public import RectangleCoefficient2
public import DivisorEulerBound2


@[expose] public section

/-!
# Late-stage second-moment bound for one prime step

Combines the progression-intersection invariant `HasProgressionBounds Q`, the
rectangle second-moment expansion, the geometric sum over prime powers $p^{j}$,
and the divisor-pair Euler product to bound the fiber second moment at prime $p$
by $C (\log p)^6 / (p - 1)^2$.
-/

open scoped BigOperators
namespace Erdos2.LateMoment

open CoveringModel

theorem newClass_fraction {Q p γ : ℕ} [NeZero Q] [NeZero p]
    (r : ℕ → ℤ) (i : LateIndex Q γ) :
    Rectangles.fraction (newClass Q p γ r i) =
      1 / (p : ℝ) ^ (i.2.val + 1) := by
  simpa only [Rectangles.fraction, newClass, ZMod.card, Nat.cast_pow] using
    CongruenceGeometry.reduction_uniform_fraction
      (Nat.pow_dvd_pow p (Nat.succ_le_of_lt i.2.isLt))
      (r (i.1.val * p ^ (i.2.val + 1)) : ZMod (p ^ (i.2.val + 1)))

theorem late_secondMoment_le_divisor_sum {Q p γ : ℕ}
    [NeZero Q] [NeZero p] (hp : p.Prime)
    (w : ProductProbability.ProbabilityWeight (ZMod Q))
    (hw : ProgressionUpdate.HasProgressionBounds Q w.value) (r : ℕ → ℤ) :
    (∑ x : ZMod Q, w.value x * (Fiber.fraction (lateFiber Q p γ r x)) ^ 2) ≤
      (∑ m ∈ Q.divisors, ∑ n ∈ Q.divisors,
        (2 : ℝ) ^ (Nat.lcm m n).primeFactors.card / (Nat.lcm m n : ℝ)) /
          ((p : ℝ) - 1) ^ 2 := by
  classical
  let H : Q.divisors → Q.divisors → ℝ := fun m n =>
    (2 : ℝ) ^ (Nat.lcm m.val n.val).primeFactors.card /
      (Nat.lcm m.val n.val : ℝ)
  let S := oldClass Q p γ r
  let T := newClass Q p γ r
  have hHnonneg : ∀ m n, 0 ≤ H m n := by
    intro m n
    dsimp [H]
    positivity
  have hH : ∀ i j : LateIndex Q γ,
      (∑ x ∈ S i ∩ S j, w.value x) ≤ H i.1 j.1 := by
    intro i j
    have hset : S i ∩ S j = Finset.univ.filter (fun x : ZMod Q =>
        ZMod.castHom (Nat.dvd_of_mem_divisors i.1.property) (ZMod i.1.val) x =
          (r (i.1.val * p ^ (i.2.val + 1)) : ZMod i.1.val) ∧
        ZMod.castHom (Nat.dvd_of_mem_divisors j.1.property) (ZMod j.1.val) x =
          (r (j.1.val * p ^ (j.2.val + 1)) : ZMod j.1.val)) := by
      ext x
      simp only [S, oldClass, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and]
    rw [hset]
    exact CongruenceGeometry.weighted_residue_intersection_le
      (Nat.dvd_of_mem_divisors i.1.property) (Nat.dvd_of_mem_divisors j.1.property)
      _ _ w.value (H i.1 j.1) (hHnonneg _ _)
      (fun a => ProgressionUpdate.bound_for_residue w.value hw _
        (Nat.lcm_dvd (Nat.dvd_of_mem_divisors i.1.property)
          (Nat.dvd_of_mem_divisors j.1.property)) a)
  have hrect := Rectangles.rectangle_second_moment_le w.value S T
    (fun i j => H i.1 j.1) w.nonneg hH
  have hfrac : ∀ i : LateIndex Q γ,
      Rectangles.fraction (T i) = 1 / (p : ℝ) ^ (i.2.val + 1) :=
    newClass_fraction r
  have hsum : (∑ m : Q.divisors, ∑ n : Q.divisors, H m n) ≤
      ∑ m ∈ Q.divisors, ∑ n ∈ Q.divisors,
        (2 : ℝ) ^ (Nat.lcm m n).primeFactors.card / (Nat.lcm m n : ℝ) := by
    apply le_of_eq
    change (∑ m : Q.divisors, ∑ n : Q.divisors,
        (2 : ℝ) ^ (Nat.lcm m.val n.val).primeFactors.card /
          (Nat.lcm m.val n.val : ℝ)) = _
    calc
      _ = ∑ m ∈ Q.divisors, ∑ n : Q.divisors,
          (2 : ℝ) ^ (Nat.lcm m n.val).primeFactors.card /
            (Nat.lcm m n.val : ℝ) :=
        Finset.sum_coe_sort Q.divisors (fun m : ℕ => ∑ n : Q.divisors,
          (2 : ℝ) ^ (Nat.lcm m n.val).primeFactors.card /
            (Nat.lcm m n.val : ℝ))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        exact Finset.sum_coe_sort Q.divisors (fun n : ℕ =>
          (2 : ℝ) ^ (Nat.lcm m n).primeFactors.card / (Nat.lcm m n : ℝ))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ ∑ i : LateIndex Q γ, ∑ j : LateIndex Q γ,
        Rectangles.fraction (T i) * Rectangles.fraction (T j) * H i.1 j.1 := by
      simpa only [S, T, lateFiber, Rectangles.badFiber,
        Fiber.fraction, Rectangles.fraction] using hrect
    _ = ∑ i : Q.divisors × Fin γ, ∑ j : Q.divisors × Fin γ,
        (1 / (p : ℝ) ^ (i.2.val + 1)) *
          (1 / (p : ℝ) ^ (j.2.val + 1)) * H i.1 j.1 := by simp_rw [hfrac]
    _ ≤ _ := Rectangles.geometric_pair_sum_le hp2 γ H hHnonneg hsum

theorem late_secondMoment_le_primeProduct {Q p γ : ℕ}
    [NeZero Q] [NeZero p] (hp : p.Prime)
    (w : ProductProbability.ProbabilityWeight (ZMod Q))
    (hw : ProgressionUpdate.HasProgressionBounds Q w.value) (r : ℕ → ℤ) :
    (∑ x : ZMod Q, w.value x * (Fiber.fraction (lateFiber Q p γ r x)) ^ 2) ≤
      (∏ q ∈ Q.primeFactors, EulerMoment.factorBound (q : ℝ)) /
        ((p : ℝ) - 1) ^ 2 := by
  exact (late_secondMoment_le_divisor_sum hp w hw r).trans
    (div_le_div_of_nonneg_right (DivisorEuler.divisor_pair_sum_le_product Q (NeZero.ne Q))
      (sq_nonneg _))

theorem late_secondMoment_le_uniformCost {Q p γ : ℕ}
    [NeZero Q] [NeZero p] (hp : p.Prime)
    (w : ProductProbability.ProbabilityWeight (ZMod Q))
    (hw : ProgressionUpdate.HasProgressionBounds Q w.value) (r : ℕ → ℤ) (C : ℝ)
    (hprod : (∏ q ∈ Q.primeFactors, EulerMoment.factorBound (q : ℝ)) ≤
      C * Real.log (p : ℝ) ^ 6) :
    (∑ x : ZMod Q, w.value x * (Fiber.fraction (lateFiber Q p γ r x)) ^ 2) ≤
      C * Real.log (p : ℝ) ^ 6 / ((p : ℝ) - 1) ^ 2 := by
  exact (late_secondMoment_le_primeProduct hp w hw r).trans
    (div_le_div_of_nonneg_right hprod (sq_nonneg _))

end Erdos2.LateMoment
