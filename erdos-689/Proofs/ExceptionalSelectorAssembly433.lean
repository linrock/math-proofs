module

public import AffineProgressionSieve433

@[expose] public section


/-!
# Actual selector-preserving normalization at the exceptional prime three

Excluding the determinant-collision prime from a two-prime sieve enlarges
the excluded modulus and appears to introduce a spurious factor `9/4`.
The genuine affine product has exactly one forbidden residue modulo three,
so the actual selected parameter classes occupy two of the three CRT lifts.
Their factor `2/3` restores the correct singular factor `3/2`.
-/

open Finset
open Filter
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The genuinely admissible natural residues at the exceptional prime:
they are the complement of the actual two-form affine-product roots. -/
def exceptionalThreeAdmissibleResidues
    (u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  Finset.range 3 \ affineSieveRootResidues 3 u₁ v₁ u₂ v₂

/-- At a true determinant collision with both slopes invertible, exactly
two of the three actual parameter residue classes remain admissible. -/
theorem exceptionalThreeAdmissibleResidues_card
    (u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : ¬ 3 ∣ u₁) (hu₂ : ¬ 3 ∣ u₂)
    (hdet : (u₁ : ZMod 3) * (v₂ : ZMod 3) =
      (u₂ : ZMod 3) * (v₁ : ZMod 3)) :
    (exceptionalThreeAdmissibleResidues u₁ v₁ u₂ v₂).card = 2 := by
  have hprime : Nat.Prime 3 := by norm_num
  have hroots := @affineSieveRootResidues_card_eq_one_of_prime_det_collision
    3 u₁ v₁ u₂ v₂ ⟨hprime⟩ hprime hu₁ hu₂ hdet
  have hsubset : affineSieveRootResidues 3 u₁ v₁ u₂ v₂ ⊆
      Finset.range 3 := Finset.filter_subset _ _
  unfold exceptionalThreeAdmissibleResidues
  rw [Finset.card_sdiff_of_subset hsubset, Finset.card_range, hroots]

/-- Actual exceptional-prime admissibility is exactly nondivisibility of
the original affine product, not a formal or symbolic selector. -/
theorem exceptionalThreeAdmissibleResidues_mem_mod_iff
    (u₁ v₁ u₂ v₂ t : ℕ) :
    t % 3 ∈ exceptionalThreeAdmissibleResidues u₁ v₁ u₂ v₂ ↔
      ¬ 3 ∣ affineSieveProduct u₁ v₁ u₂ v₂ t := by
  unfold exceptionalThreeAdmissibleResidues
  have hlt : t % 3 < 3 := Nat.mod_lt t (by norm_num)
  rw [Finset.mem_sdiff, Finset.mem_range,
    affineSieveRootResidues_mem_mod_iff 3 u₁ v₁ u₂ v₂ t (by norm_num)]
  simp [hlt]

/-- The real density of the genuine admissible exceptional-prime classes. -/
theorem exceptionalThreeAdmissibleResidues_density
    (u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : ¬ 3 ∣ u₁) (hu₂ : ¬ 3 ∣ u₂)
    (hdet : (u₁ : ZMod 3) * (v₂ : ZMod 3) =
      (u₂ : ZMod 3) * (v₁ : ZMod 3)) :
    ((exceptionalThreeAdmissibleResidues u₁ v₁ u₂ v₂).card : ℝ) / 3 =
      2 / 3 := by
  rw [exceptionalThreeAdmissibleResidues_card u₁ v₁ u₂ v₂
    hu₁ hu₂ hdet]
  norm_num

/-- Exact genuine simultaneous natural CRT residue selectors. -/
def naturalCrtSelectorResidues
    (m n : ℕ) (A B : Finset ℕ) : Finset ℕ :=
  (Finset.range (m * n)).filter fun r => r % m ∈ A ∧ r % n ∈ B

/-- Arbitrary actual selector sets on coprime natural moduli have exactly
the product number of global CRT lifts, without density approximation. -/
theorem naturalCrtSelectorResidues_card
    (m n : ℕ) (A B : Finset ℕ)
    (hm : 0 < m) (hn : 0 < n) (hcoprime : m.Coprime n)
    (hA : ∀ r ∈ A, r < m) (hB : ∀ r ∈ B, r < n) :
    (naturalCrtSelectorResidues m n A B).card = A.card * B.card := by
  classical
  let source := naturalCrtSelectorResidues m n A B
  have hcard : source.card = (A.product B).card := by
    apply Finset.card_bij (s := source) (t := A.product B)
      (fun r _ => (r % m, r % n))
    · intro r hr
      have hconditions := (Finset.mem_filter.mp hr).2
      exact Finset.mem_product.mpr hconditions
    · intro r hr s hs heq
      have hrlt : r < m * n :=
        Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hslt : s < m * n :=
        Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      have hfirst : r % m = s % m := congrArg Prod.fst heq
      have hsecond : r % n = s % n := congrArg Prod.snd heq
      have hmod : r ≡ s [MOD m * n] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
          ⟨hfirst, hsecond⟩
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hrlt,
        Nat.mod_eq_of_lt hslt] using hmod
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      let r : ℕ := Nat.chineseRemainder hcoprime a b
      have hra : r % m = a := by
        have heq := (Nat.chineseRemainder hcoprime a b).property.1
        simpa [r, Nat.ModEq, Nat.mod_eq_of_lt (hA a ha)] using heq
      have hrb : r % n = b := by
        have heq := (Nat.chineseRemainder hcoprime a b).property.2
        simpa [r, Nat.ModEq, Nat.mod_eq_of_lt (hB b hb)] using heq
      refine ⟨r, ?_, Prod.ext hra hrb⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr
        (Nat.chineseRemainder_lt_mul hcoprime a b
          (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)),
        by simpa [hra, hrb] using And.intro ha hb⟩
  simpa [source] using hcard

/-- Lift any actual support-selector residue set through the genuine two
allowed residue classes at the exceptional prime. -/
def exceptionalThreeLiftedSelectorResidues
    (W : ℕ) (T : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  naturalCrtSelectorResidues 3 W
    (exceptionalThreeAdmissibleResidues u₁ v₁ u₂ v₂) T

/-- Every selected support class has exactly two, not three, genuine
admissible CRT lifts modulo `3*W`. -/
theorem exceptionalThreeLiftedSelectorResidues_card
    (W : ℕ) (T : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W) (hcoprime : Nat.Coprime 3 W)
    (hT : ∀ r ∈ T, r < W)
    (hu₁ : ¬ 3 ∣ u₁) (hu₂ : ¬ 3 ∣ u₂)
    (hdet : (u₁ : ZMod 3) * (v₂ : ZMod 3) =
      (u₂ : ZMod 3) * (v₁ : ZMod 3)) :
    (exceptionalThreeLiftedSelectorResidues
      W T u₁ v₁ u₂ v₂).card = 2 * T.card := by
  unfold exceptionalThreeLiftedSelectorResidues
  rw [naturalCrtSelectorResidues_card 3 W
    (exceptionalThreeAdmissibleResidues u₁ v₁ u₂ v₂) T
    (by norm_num) hW hcoprime]
  · rw [exceptionalThreeAdmissibleResidues_card
      u₁ v₁ u₂ v₂ hu₁ hu₂ hdet]
  · intro r hr
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hr).1
  · exact hT

/-- Enlarging a modulus coprime to three multiplies its two-prime totient
normalization by `9/4`; the actual two admissible classes multiply it by
`2/3`, giving precisely the genuine singular correction `3/2`. -/
theorem exceptionalThree_totient_density_normalization
    (M : ℕ) (hM : 0 < M) (hcoprime : Nat.Coprime 3 M) :
    (((3 * M : ℕ) : ℝ) / ((3 * M).totient : ℝ)) ^ 2 *
        ((2 : ℝ) / 3) =
      (3 / 2 : ℝ) * (((M : ℝ) / M.totient) ^ 2) := by
  have htotient : (3 * M).totient = 2 * M.totient := by
    rw [Nat.totient_mul hcoprime, Nat.totient_prime (by norm_num)]
  have hphi : (M.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hM).ne'
  rw [htotient]
  push_cast
  field_simp [hphi]

/-- Correct normalization for an arbitrary actual support selector.  The
excluded sieve modulus is `3*M`, the selected CRT modulus is `3*W`, and
their coupled leading density is exactly `3/2` times the old one. -/
theorem exceptionalThreeLiftedSelector_totient_normalization
    (M W : ℕ) (T : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ)
    (hM : 0 < M) (hW : 0 < W)
    (hcoprime : Nat.Coprime 3 M) (hWM : W ∣ M)
    (hT : ∀ r ∈ T, r < W)
    (hu₁ : ¬ 3 ∣ u₁) (hu₂ : ¬ 3 ∣ u₂)
    (hdet : (u₁ : ZMod 3) * (v₂ : ZMod 3) =
      (u₂ : ZMod 3) * (v₁ : ZMod 3)) :
    (((3 * M : ℕ) : ℝ) / ((3 * M).totient : ℝ)) ^ 2 *
        (((exceptionalThreeLiftedSelectorResidues
          W T u₁ v₁ u₂ v₂).card : ℝ) / ((3 * W : ℕ) : ℝ)) =
      (3 / 2 : ℝ) * (((M : ℝ) / M.totient) ^ 2) *
        ((T.card : ℝ) / W) := by
  have hcoprimeW : Nat.Coprime 3 W :=
    hcoprime.coprime_dvd_right hWM
  have hcard := exceptionalThreeLiftedSelectorResidues_card
    W T u₁ v₁ u₂ v₂ hW hcoprimeW hT hu₁ hu₂ hdet
  have htotient : (3 * M).totient = 2 * M.totient := by
    rw [Nat.totient_mul hcoprime, Nat.totient_prime (by norm_num)]
  have hphi : (M.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hM).ne'
  have hWreal : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  rw [htotient, hcard]
  push_cast
  field_simp [hphi, hWreal]

/-- Membership in the lifted selector is exactly membership in the
original support selector together with actual nondivisibility at three. -/
theorem exceptionalThreeLiftedSelectorResidues_mem_mod_iff
    (W : ℕ) (T : Finset ℕ) (u₁ v₁ u₂ v₂ t : ℕ)
    (hW : 0 < W) :
    t % (3 * W) ∈ exceptionalThreeLiftedSelectorResidues
      W T u₁ v₁ u₂ v₂ ↔
      t % W ∈ T ∧ ¬ 3 ∣ affineSieveProduct u₁ v₁ u₂ v₂ t := by
  have hpositive : 0 < 3 * W := by omega
  have hthree : (t % (3 * W)) % 3 = t % 3 :=
    Nat.mod_mod_of_dvd t (dvd_mul_right 3 W)
  have hsupport : (t % (3 * W)) % W = t % W :=
    Nat.mod_mod_of_dvd t (dvd_mul_left W 3)
  unfold exceptionalThreeLiftedSelectorResidues naturalCrtSelectorResidues
  rw [Finset.mem_filter, Finset.mem_range, hthree, hsupport,
    exceptionalThreeAdmissibleResidues_mem_mod_iff]
  have hlt : t % (3 * W) < 3 * W := Nat.mod_lt t hpositive
  tauto

/-- The only genuine prime pairs lost by imposing exceptional-prime
admissibility are those for which one of the two prime values equals `3`. -/
def exceptionalThreePrimeValueParameters
    (N u₁ v₁ u₂ v₂ : ℕ) : Finset ℕ :=
  affineValueParameters N u₁ v₁ {3} ∪
    affineValueParameters N u₂ v₂ {3}

/-- Each positive affine form takes the exceptional prime value at most
once, so the complete actual exceptional contribution is at most two. -/
theorem exceptionalThreePrimeValueParameters_card_le
    (N u₁ v₁ u₂ v₂ : ℕ)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (exceptionalThreePrimeValueParameters N u₁ v₁ u₂ v₂).card ≤ 2 := by
  unfold exceptionalThreePrimeValueParameters
  calc
    (affineValueParameters N u₁ v₁ {3} ∪
        affineValueParameters N u₂ v₂ {3}).card ≤
      (affineValueParameters N u₁ v₁ {3}).card +
        (affineValueParameters N u₂ v₂ {3}).card :=
      Finset.card_union_le _ _
    _ ≤ ({3} : Finset ℕ).card + ({3} : Finset ℕ).card :=
      Nat.add_le_add
        (affineValueParameters_card_le N u₁ v₁ {3} hu₁)
        (affineValueParameters_card_le N u₂ v₂ {3} hu₂)
    _ = 2 := by simp

/-- Every actual selected affine prime pair either belongs to its genuine
two-class exceptional CRT lift or is one of at most two prime-value-three
exceptions.  No prime pair is dropped from the original selector. -/
theorem actualAffineSelected_prime_pair_card_le_exceptional_lift
    (N W : ℕ) (T : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) :
    (((Finset.range N).filter fun t =>
      t % W ∈ T ∧ (u₁ * t + v₁).Prime ∧
        (u₂ * t + v₂).Prime).card) ≤
      (((Finset.range N).filter fun t =>
        t % (3 * W) ∈ exceptionalThreeLiftedSelectorResidues
          W T u₁ v₁ u₂ v₂ ∧
          (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) + 2 := by
  let source := (Finset.range N).filter fun t =>
    t % W ∈ T ∧ (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime
  let good := (Finset.range N).filter fun t =>
    t % (3 * W) ∈ exceptionalThreeLiftedSelectorResidues
      W T u₁ v₁ u₂ v₂ ∧
      (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime
  let exceptions := exceptionalThreePrimeValueParameters N u₁ v₁ u₂ v₂
  have hsubset : source ⊆ good ∪ exceptions := by
    intro t ht
    obtain ⟨htN, htselector, hfirst, hsecond⟩ := Finset.mem_filter.mp ht
    by_cases hdiv : 3 ∣ affineSieveProduct u₁ v₁ u₂ v₂ t
    · have hproduct :
          3 ∣ (u₁ * t + v₁) * (u₂ * t + v₂) := hdiv
      have hthree : Nat.Prime 3 := by norm_num
      rcases hthree.dvd_mul.mp hproduct with hleft | hright
      · have heq : u₁ * t + v₁ = 3 :=
          ((Nat.prime_dvd_prime_iff_eq hthree hfirst).mp hleft).symm
        apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        exact ⟨htN, by simp [heq]⟩
      · have heq : u₂ * t + v₂ = 3 :=
          ((Nat.prime_dvd_prime_iff_eq hthree hsecond).mp hright).symm
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨htN, by simp [heq]⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨htN,
        (exceptionalThreeLiftedSelectorResidues_mem_mod_iff
          W T u₁ v₁ u₂ v₂ t hW).mpr ⟨htselector, hdiv⟩,
        hfirst, hsecond⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le good exceptions
  have hexceptions := exceptionalThreePrimeValueParameters_card_le
    N u₁ v₁ u₂ v₂ hu₁ hu₂
  change exceptions.card ≤ 2 at hexceptions
  change source.card ≤ good.card + 2
  omega

/-- Full optimized Selberg bound for the *original* actual selected
prime-pair set when the determinant collides at three.  The leading term
uses exactly `2*#T` genuine CRT classes modulo `3*W`, the excluded sieve
modulus is `3*M`, and the at-most-two prime-value-three exceptions are
retained explicitly.  Together with the preceding totient-normalization
identity this has the exact `3/2`, rather than `9/4`, leading correction. -/
theorem actualAffineSelected_exceptionalThree_prime_pair_card_le_density
    (P T : Finset ℕ) (M N z W u₁ v₁ u₂ v₂ : ℕ)
    (hW : 0 < W) (hT : ∀ r ∈ T, r < W)
    (hcoprime : Nat.Coprime 3 M) (hWM : W ∣ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hz : 0 < z)
    (hu₁ : ∀ p ∈ P, ¬ p ∣ u₁)
    (hu₂ : ∀ p ∈ P, ¬ p ∣ u₂)
    (hdet : ∀ p ∈ P,
      (u₁ : ZMod p) * (v₂ : ZMod p) ≠
        (u₂ : ZMod p) * (v₁ : ZMod p))
    (hthreeu₁ : ¬ 3 ∣ u₁) (hthreeu₂ : ¬ 3 ∣ u₂)
    (hthreedet : (u₁ : ZMod 3) * (v₂ : ZMod 3) =
      (u₂ : ZMod 3) * (v₁ : ZMod 3))
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) (3 * M))
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ z ∧ Nat.Coprime p (3 * M)))
    (hu₁positive : 0 < u₁) (hu₂positive : 0 < u₂) :
    ((((Finset.range N).filter fun t =>
      t % W ∈ T ∧
        (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      ((2 * T.card : ℕ) : ℝ) *
        (((N : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator (3 * M) z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) + 2 := by
  let lifted := exceptionalThreeLiftedSelectorResidues
    W T u₁ v₁ u₂ v₂
  have hcoprimeW : Nat.Coprime 3 W :=
    hcoprime.coprime_dvd_right hWM
  have hcard : lifted.card = 2 * T.card :=
    exceptionalThreeLiftedSelectorResidues_card
      W T u₁ v₁ u₂ v₂ hW hcoprimeW hT
      hthreeu₁ hthreeu₂ hthreedet
  have hresidues : ∀ r ∈ lifted, r < 3 * W := by
    intro r hr
    change r ∈ (Finset.range (3 * W)).filter _ at hr
    exact Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hMthree : 2 ∣ 3 * M := dvd_mul_of_dvd_right hM 3
  have hWMthree : 3 * W ∣ 3 * M := mul_dvd_mul_left 3 hWM
  have hselected := actualAffineSelected_prime_pair_card_le_density
    P lifted (3 * M) N z (3 * W)
    u₁ v₁ u₂ v₂ (by omega) hresidues
    hprime hlarge hz hu₁ hu₂ hdet hMthree hPM hWMthree hprimes
    hu₁positive hu₂positive
  have hdecomposition := actualAffineSelected_prime_pair_card_le_exceptional_lift
    N W T u₁ v₁ u₂ v₂ hW hu₁positive hu₂positive
  have hreal :
      ((((Finset.range N).filter fun t =>
        t % W ∈ T ∧
          (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
        ((((Finset.range N).filter fun t =>
          t % (3 * W) ∈ lifted ∧
            (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) + 2 := by
    exact_mod_cast hdecomposition
  calc
    ((((Finset.range N).filter fun t =>
      t % W ∈ T ∧
        (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      ((((Finset.range N).filter fun t =>
        t % (3 * W) ∈ lifted ∧
          (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) + 2 :=
        hreal
    _ ≤ (lifted.card : ℝ) *
        (((N : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator (3 * M) z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) + 2 := by
        linarith
    _ = _ := by rw [hcard]

/-- For a fixed even excluded modulus no moving-prime penalty is needed:
the genuine squarefree Selberg denominator has reciprocal at most
`121*(M/phi(M))²/log(n)²` at the exact natural fifth-root cutoff. -/
theorem twoRootSelbergDenominator_fixed_fifth_root_eventually_inv_le
    (M : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      (twoRootSelbergDenominator M
        (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤
          (121 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
            (Real.log (n : ℝ)) ^ 2 := by
  have hMpositive : 0 < M := by omega
  filter_upwards [selberg_complete_block_log_lower_eventually M hMpositive,
    eventually_ge_atTop 2] with n hcutoff hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have htotient : 0 < M.totient := Nat.totient_pos.mpr hMpositive
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpositive
  have htotientreal : (0 : ℝ) < M.totient := by exact_mod_cast htotient
  have hbase := twoRootSelbergDenominator_ge_totient_log_sq
    M (selbergSquareRootBlockCutoff n) hMeven hM
  have hlower :
      (1 / 121 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ)) ^ 2 ≤
          twoRootSelbergDenominator M (selbergSquareRootBlockCutoff n ^ 2) := by
    calc
      (1 / 121 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
          (Real.log (n : ℝ)) ^ 2 =
        (((M.totient : ℝ) / M) ^ 2) *
          (Real.log (n : ℝ) / 11) ^ 2 := by ring
      _ ≤ (((M.totient : ℝ) / M) ^ 2) *
          (Real.log
            ((selbergSquareRootBlockCutoff n / M + 1 : ℕ) : ℝ)) ^ 2 := by
        gcongr
      _ ≤ _ := hbase
  have hpositive : 0 <
      (1 / 121 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ)) ^ 2 := by positivity
  calc
    (twoRootSelbergDenominator M
        (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤
      ((1 / 121 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ)) ^ 2)⁻¹ := inv_anti₀ hpositive hlower
    _ = (121 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
        (Real.log (n : ℝ)) ^ 2 := by
      field_simp

/-- Complete eventual fifth-root Selberg bound for the *original* selected
prime pairs at the true exceptional determinant prime.  There is no
`q ≥ 5` hypothesis: the fixed excluded modulus is `3*M`, the selector
spacing is the actual `2*#T/(3*W)`, and both prime-value-three exceptions
are explicit.  Its principal coefficient is exactly `121*(3/2)` times the
old support-normalized selector density. -/
theorem actualAffineSelected_exceptionalThree_prime_pairs_fifth_root_eventually_explicit
    (M W : ℕ)
    (hMeven : 2 ∣ M) (hM : 2 ≤ M)
    (hW : 0 < W) (hcoprime : Nat.Coprime 3 M) (hWM : W ∣ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (P T : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ),
        (∀ r ∈ T, r < W) →
        (∀ p ∈ P, p.Prime) →
        (∀ p ∈ P, 2 < p) →
        (∀ p ∈ P, ¬ p ∣ u₁) →
        (∀ p ∈ P, ¬ p ∣ u₂) →
        (∀ p ∈ P,
          (u₁ : ZMod p) * (v₂ : ZMod p) ≠
            (u₂ : ZMod p) * (v₁ : ZMod p)) →
        ¬ 3 ∣ u₁ → ¬ 3 ∣ u₂ →
        (u₁ : ZMod 3) * (v₂ : ZMod 3) =
          (u₂ : ZMod 3) * (v₁ : ZMod 3) →
        Nat.Coprime (∏ p ∈ P, p) (3 * M) →
        (∀ p : ℕ, p.Prime →
          (p ∣ ∏ q ∈ P, q ↔
            p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
              Nat.Coprime p (3 * M))) →
        0 < u₁ → 0 < u₂ →
        ((((Finset.range n).filter fun t =>
          t % W ∈ T ∧
            (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
          ((2 * T.card : ℕ) : ℝ) *
            ((121 : ℝ) *
                ((((3 * M : ℕ) : ℝ) / (3 * M).totient) ^ 2) *
                (((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
                  (Real.log (n : ℝ)) ^ 2) +
              ((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) ^ 4 +
                ((2 * Nat.primeCounting
                  (selbergSquareRootBlockCutoff n ^ 2) : ℕ) : ℝ)) + 2 := by
  have hMevenThree : 2 ∣ 3 * M := dvd_mul_of_dvd_right hMeven 3
  have hMthree : 2 ≤ 3 * M := by omega
  filter_upwards
    [twoRootSelbergDenominator_fixed_fifth_root_eventually_inv_le
      (3 * M) hMevenThree hMthree, eventually_ge_atTop 1]
      with n hdenominator hn
  intro P T u₁ v₁ u₂ v₂ hT hprime hlarge hu₁ hu₂ hdet
    hthreeu₁ hthreeu₂ hthreedet hPM hprimes hu₁positive hu₂positive
  let z := selbergSquareRootBlockCutoff n ^ 2
  have hz : 0 < z :=
    selbergSquareRootBlockCutoff_sq_pos_of_pos n (by omega)
  have hpair := actualAffineSelected_exceptionalThree_prime_pair_card_le_density
    P T M n z W u₁ v₁ u₂ v₂ hW hT hcoprime hWM
    hprime hlarge hz hu₁ hu₂ hdet hthreeu₁ hthreeu₂ hthreedet
    hMeven hPM hprimes hu₁positive hu₂positive
  have hmain :
      ((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator (3 * M) z ≤
        (121 : ℝ) *
          ((((3 * M : ℕ) : ℝ) / (3 * M).totient) ^ 2) *
            (((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
              (Real.log (n : ℝ)) ^ 2) := by
    calc
      ((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator (3 * M) z =
        ((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) *
          (twoRootSelbergDenominator (3 * M) z)⁻¹ := by rfl
      _ ≤ ((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) *
          ((121 : ℝ) *
            ((((3 * M : ℕ) : ℝ) / (3 * M).totient) ^ 2) /
              (Real.log (n : ℝ)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdenominator (by positivity)
      _ = _ := by ring
  calc
    ((((Finset.range n).filter fun t =>
      t % W ∈ T ∧
        (u₁ * t + v₁).Prime ∧ (u₂ * t + v₂).Prime).card) : ℝ) ≤
      ((2 * T.card : ℕ) : ℝ) *
        (((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
          twoRootSelbergDenominator (3 * M) z + (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) + 2 := hpair
    _ ≤ ((2 * T.card : ℕ) : ℝ) *
        ((121 : ℝ) *
          ((((3 * M : ℕ) : ℝ) / (3 * M).totient) ^ 2) *
            (((n : ℝ) / ((3 * W : ℕ) : ℝ) + 1) /
              (Real.log (n : ℝ)) ^ 2) +
          (z : ℝ) ^ 4 +
            ((2 * Nat.primeCounting z : ℕ) : ℝ)) + 2 := by
      gcongr
    _ = _ := by rfl

#print axioms Erdos689.exceptionalThreeAdmissibleResidues_card
#print axioms Erdos689.exceptionalThreeAdmissibleResidues_mem_mod_iff
#print axioms Erdos689.exceptionalThreeAdmissibleResidues_density
#print axioms Erdos689.naturalCrtSelectorResidues_card
#print axioms Erdos689.exceptionalThreeLiftedSelectorResidues_card
#print axioms Erdos689.exceptionalThree_totient_density_normalization
#print axioms Erdos689.exceptionalThreeLiftedSelector_totient_normalization
#print axioms Erdos689.exceptionalThreeLiftedSelectorResidues_mem_mod_iff
#print axioms Erdos689.exceptionalThreePrimeValueParameters_card_le
#print axioms Erdos689.actualAffineSelected_prime_pair_card_le_exceptional_lift
#print axioms Erdos689.actualAffineSelected_exceptionalThree_prime_pair_card_le_density
#print axioms Erdos689.twoRootSelbergDenominator_fixed_fifth_root_eventually_inv_le
#print axioms Erdos689.actualAffineSelected_exceptionalThree_prime_pairs_fifth_root_eventually_explicit

end Erdos689
