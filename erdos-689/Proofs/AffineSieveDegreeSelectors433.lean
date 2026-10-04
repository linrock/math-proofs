module

public import UniformLocalFactors
public import SelbergExplicitConstant433

@[expose] public section


/-!
# Exact switched-support cancellation for all three two-form degree fibers

The fixed-left and fixed-right manuscript fibers have two coefficient-summed
local factors, according as the switched prime divides the fixed vertex.  Both
factors are at most one.  The fixed-label fiber has the previously verified
exceptional/generic switched factor, also at most one.  These bounds are
uniform over every finite switched support and every selector pattern.

Only finite local-factor algebra is claimed; the analytic passage from genuine
selector-restricted prime counts to these products remains separate.
-/

open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- Generic fixed-vertex switched-prime cancellation, including its extra
coefficient pattern. -/
theorem fixedVertex_generic_switched_factor_identity {s : ℝ}
    (hone : s ≠ 1) :
    s * (s - 3) / (s - 1) ^ 2 + 1 / (s - 1) =
      1 - 2 / (s - 1) ^ 2 := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hone
  field_simp
  ring

/-- Fixed-vertex switched-prime cancellation when the prime divides the
fixed vertex; its coefficient sum has no first-order loss. -/
theorem fixedVertex_divisible_switched_factor_identity {s : ℝ}
    (hone : s ≠ 1) :
    s * (s - 2) / (s - 1) ^ 2 =
      1 - 1 / (s - 1) ^ 2 := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hone
  field_simp
  ring

/-- The exact two possible coefficient-summed switched factors for either
the fixed-left or fixed-right degree fiber. -/
noncomputable def fixedVertexSwitchedFactor
    (s : ℕ) (dividesVertex : Bool) : ℝ :=
  if dividesVertex then
    1 - 1 / ((s : ℝ) - 1) ^ 2
  else
    1 - 2 / ((s : ℝ) - 1) ^ 2

/-- Both fixed-vertex switched factors are nonnegative at every actual
switched prime, indeed at every integer strictly larger than three. -/
theorem fixedVertexSwitchedFactor_nonneg
    (s : ℕ) (dividesVertex : Bool) (hlarge : 3 < s) :
    0 ≤ fixedVertexSwitchedFactor s dividesVertex := by
  have hsreal : (3 : ℝ) < s := by exact_mod_cast hlarge
  have hden : 0 < ((s : ℝ) - 1) ^ 2 := by nlinarith
  cases dividesVertex with
  | false =>
      change 0 ≤ 1 - 2 / ((s : ℝ) - 1) ^ 2
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hden).mpr
      nlinarith
  | true =>
      change 0 ≤ 1 - 1 / ((s : ℝ) - 1) ^ 2
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hden).mpr
      nlinarith

/-- Neither fixed-vertex coefficient-summed switched factor exceeds one. -/
theorem fixedVertexSwitchedFactor_le_one
    (s : ℕ) (dividesVertex : Bool) :
    fixedVertexSwitchedFactor s dividesVertex ≤ 1 := by
  cases dividesVertex <;> simp [fixedVertexSwitchedFactor]
  all_goals positivity

/-- The complete coefficient-summed fixed-left or fixed-right selector
product has absolute uniform bound one, regardless of switched support size. -/
theorem fixedVertexSwitchedFactor_product_le_one
    (S : Finset ℕ) (hlarge : ∀ s ∈ S, 3 < s)
    (dividesVertex : ℕ → Bool) :
    (∏ s ∈ S, fixedVertexSwitchedFactor s (dividesVertex s)) ≤ 1 := by
  exact Finset.prod_le_one₀
    (fun s hs => fixedVertexSwitchedFactor_nonneg
      s (dividesVertex s) (hlarge s hs))
    (fun s hs => fixedVertexSwitchedFactor_le_one s (dividesVertex s))

/-- The fixed-label switched factor is nonnegative at all actual switched
primes, in both exceptional and generic label classes. -/
theorem fixedLabel_normalizedSwitchedFactor_nonneg
    (s : ℕ) (exceptional : Bool) (hlarge : 3 < s) :
    0 ≤ normalizedSwitchedFactor s exceptional := by
  have hsreal : (3 : ℝ) < s := by exact_mod_cast hlarge
  have hden : 0 < ((s : ℝ) - 1) ^ 2 := by nlinarith
  apply le_trans _ (normalized_switched_factor_lower s exceptional)
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The complete fixed-label coefficient-summed switched selector also has
absolute uniform upper bound one. -/
theorem fixedLabel_normalizedSwitchedFactor_product_le_one
    (S : Finset ℕ) (hlarge : ∀ s ∈ S, 3 < s)
    (exceptional : ℕ → Bool) :
    (∏ s ∈ S, normalizedSwitchedFactor s (exceptional s)) ≤ 1 := by
  exact Finset.prod_le_one₀
    (fun s hs => fixedLabel_normalizedSwitchedFactor_nonneg
      s (exceptional s) (hlarge s hs))
    (fun s hs => normalized_switched_factor_upper s (exceptional s))

/-- Restoring all admissible switched factors cannot enlarge the broad
formal fixed-left leading constant `2025 / 2`, including the `q = 3` case. -/
theorem fixedVertex_selector_adjusted_leading_constant_le
    (S : Finset ℕ) (hlarge : ∀ s ∈ S, 3 < s)
    (dividesVertex : ℕ → Bool) :
    (270 : ℝ) * 2 * (3 / 2) * (5 / 4) *
      (∏ s ∈ S, fixedVertexSwitchedFactor s (dividesVertex s)) ≤
        2025 / 2 := by
  rw [unrestricted_formal_degree_leading_constant_eq]
  nlinarith [fixedVertexSwitchedFactor_product_le_one S hlarge dividesVertex]

/-- Restoring all fixed-label switched factors likewise never enlarges the
same convenient broad-formal leading constant. -/
theorem fixedLabel_selector_adjusted_leading_constant_le
    (S : Finset ℕ) (hlarge : ∀ s ∈ S, 3 < s)
    (exceptional : ℕ → Bool) :
    (270 : ℝ) * 2 * (3 / 2) * (5 / 4) *
      (∏ s ∈ S, normalizedSwitchedFactor s (exceptional s)) ≤
        2025 / 2 := by
  rw [unrestricted_formal_degree_leading_constant_eq]
  nlinarith [fixedLabel_normalizedSwitchedFactor_product_le_one
    S hlarge exceptional]

/-- The actual local moving-vertex classes: neither prime form vanishes,
and the switched target residue is forbidden. -/
noncomputable def fixedVertexAdmissibleResidues
    (K : Type*) [Field K] [Fintype K] (x b : K) : Finset K := by
  classical
  exact Finset.univ.filter fun y =>
    y ≠ 0 ∧ y ≠ x ∧ (2 : K) * y ≠ b

/-- The switched forbidden residue is exactly division by two in every field
of characteristic different from two. -/
theorem fixedVertex_two_mul_eq_iff
    {K : Type*} [Field K] (y b : K) (htwo : (2 : K) ≠ 0) :
    (2 : K) * y = b ↔ y = b / 2 := by
  rw [mul_comm]
  exact (eq_div_iff htwo).symm

/-- Exact finite-field selector set: delete the zero root, the fixed vertex,
and the actual switched target residue. -/
theorem fixedVertexAdmissibleResidues_eq_erase
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (x b : K) (htwo : (2 : K) ≠ 0) :
    fixedVertexAdmissibleResidues K x b =
      ((Finset.univ.erase 0).erase x).erase (b / 2) := by
  classical
  ext y
  simp only [fixedVertexAdmissibleResidues, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  have hswitch : (2 : K) * y ≠ b ↔ y ≠ b / 2 :=
    not_congr (fixedVertex_two_mul_eq_iff y b htwo)
  rw [hswitch]
  tauto

/-- If the switched prime divides the fixed vertex, precisely two genuine
moving residues are forbidden: zero and the nonzero switched class. -/
theorem fixedVertexAdmissibleResidues_card_of_zero
    {K : Type*} [Field K] [Fintype K]
    (b : K) (htwo : (2 : K) ≠ 0) (hb : b ≠ 0) :
    (fixedVertexAdmissibleResidues K 0 b).card =
      Fintype.card K - 2 := by
  classical
  have hhalf : b / (2 : K) ≠ 0 := div_ne_zero hb htwo
  rw [fixedVertexAdmissibleResidues_eq_erase 0 b htwo]
  simp [hhalf, Nat.sub_sub]

/-- If the fixed vertex is nonzero and its doubled class is not the switched
target, all three actual forbidden moving residues are distinct. -/
theorem fixedVertexAdmissibleResidues_card_of_ne_zero
    {K : Type*} [Field K] [Fintype K]
    (x b : K) (htwo : (2 : K) ≠ 0) (hb : b ≠ 0)
    (hx : x ≠ 0) (hfixed : (2 : K) * x ≠ b) :
    (fixedVertexAdmissibleResidues K x b).card =
      Fintype.card K - 3 := by
  classical
  have hhalf : b / (2 : K) ≠ 0 := div_ne_zero hb htwo
  have hdistinct : b / (2 : K) ≠ x := by
    intro heq
    apply hfixed
    exact (fixedVertex_two_mul_eq_iff x b htwo).mpr heq.symm
  rw [fixedVertexAdmissibleResidues_eq_erase x b htwo]
  simp [hx, hhalf, hdistinct, Nat.sub_sub]

/-- Actual switched-prime local selector count: `p-2` if the fixed vertex
vanishes modulo `p`, and `p-3` otherwise.  All residues are genuine `ZMod p`
elements; this is not an asserted symbolic local factor. -/
theorem fixedVertexAdmissibleResidues_card_zmod
    (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hpodd : p ≠ 2)
    (x b : ZMod p) (hb : b ≠ 0)
    (hfixed : (2 : ZMod p) * x ≠ b) :
    (fixedVertexAdmissibleResidues (ZMod p) x b).card =
      if x = 0 then p - 2 else p - 3 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  split_ifs with hx
  · subst x
    simpa using fixedVertexAdmissibleResidues_card_of_zero b htwo hb
  · simpa using
      fixedVertexAdmissibleResidues_card_of_ne_zero x b htwo hb hx hfixed

/-- The actual simultaneous residue classes specified by independent local
finite sets, transported through the genuine multi-modulus Chinese remainder
equivalence. -/
noncomputable def affineCrtRestrictedResidues
    {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcoprime : Pairwise fun i j => (a i).Coprime (a j))
    (T : ∀ i, Finset (ZMod (a i))) :
    Finset (ZMod (∏ i, a i)) := by
  classical
  exact (Fintype.piFinset T).image (ZMod.prodEquivPi a hcoprime).symm

/-- A global CRT residue belongs to the restricted set exactly when all of
its genuine prime-modulus coordinates belong to their prescribed selectors. -/
theorem affineCrtRestrictedResidues_mem_iff
    {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcoprime : Pairwise fun i j => (a i).Coprime (a j))
    (T : ∀ i, Finset (ZMod (a i))) (y : ZMod (∏ i, a i)) :
    y ∈ affineCrtRestrictedResidues a hcoprime T ↔
      ∀ i, (ZMod.prodEquivPi a hcoprime y i) ∈ T i := by
  classical
  change y ∈ (Fintype.piFinset T).image
    (ZMod.prodEquivPi a hcoprime).symm ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    intro i
    rw [(ZMod.prodEquivPi a hcoprime).apply_symm_apply]
    exact Fintype.mem_piFinset.mp hf i
  · intro hy
    refine ⟨ZMod.prodEquivPi a hcoprime y,
      Fintype.mem_piFinset.mpr hy, ?_⟩
    exact (ZMod.prodEquivPi a hcoprime).symm_apply_apply y

/-- Exact CRT factorization for arbitrary local selector sets: the number of
genuine simultaneous residue classes is the product of the local counts. -/
theorem affineCrtRestrictedResidues_card
    {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcoprime : Pairwise fun i j => (a i).Coprime (a j))
    (T : ∀ i, Finset (ZMod (a i))) :
    (affineCrtRestrictedResidues a hcoprime T).card =
      ∏ i, (T i).card := by
  classical
  unfold affineCrtRestrictedResidues
  rw [Finset.card_image_of_injective _
    (ZMod.prodEquivPi a hcoprime).symm.injective,
    Fintype.card_piFinset]

/-- Distinct members of a prime support are pairwise coprime, in exactly the
subtype-indexed form required by the multi-modulus CRT equivalence. -/
theorem affineSelector_primeSupport_pairwise_coprime
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    Pairwise fun (p q : S) =>
      (p : ℕ).Coprime (q : ℕ) := by
  intro p q hne
  have hp : (p : ℕ).Prime := hprime p p.property
  have hq : (q : ℕ).Prime := hprime q q.property
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  exact hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv))

/-- Actual admissible moving residues over a natural-indexed prime field. -/
noncomputable def fixedVertexNaturalAdmissibleResidues
    (p x b : ℕ) : Finset (ZMod p) :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    fixedVertexAdmissibleResidues (ZMod p)
      (x : ZMod p) (b : ZMod p)
  else ∅

/-- The natural-indexed selector has the manuscript's exact `p-2`/`p-3`
local cardinality, with genuine finite-field inequalities. -/
theorem fixedVertexNaturalAdmissibleResidues_card
    (p x b : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hb : (b : ZMod p) ≠ 0)
    (hfixed : (2 : ZMod p) * (x : ZMod p) ≠ (b : ZMod p)) :
    (fixedVertexNaturalAdmissibleResidues p x b).card =
      if (x : ZMod p) = 0 then p - 2 else p - 3 := by
  classical
  unfold fixedVertexNaturalAdmissibleResidues
  simp only [hp, ↓reduceDIte]
  exact @fixedVertexAdmissibleResidues_card_zmod
    p ⟨hp⟩ hp hpodd (x : ZMod p) (b : ZMod p) hb hfixed

/-- Exact global squarefree CRT selector count for a fixed vertex, allowing
each switched prime to have its own manuscript target `b p`.  This counts
actual simultaneous residue classes modulo the full switched-prime product. -/
theorem fixedVertexSupport_crt_selector_card
    (S : Finset ℕ) (x : ℕ) (b : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, p ≠ 2)
    (hb : ∀ p ∈ S, (b p : ZMod p) ≠ 0)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p)) :
    (affineCrtRestrictedResidues
      (fun p : S => (p : ℕ))
      (affineSelector_primeSupport_pairwise_coprime S hprime)
      (fun p : S => fixedVertexNaturalAdmissibleResidues
        (p : ℕ) x (b p))).card =
      ∏ p ∈ S, if (x : ZMod p) = 0 then p - 2 else p - 3 := by
  rw [affineCrtRestrictedResidues_card]
  calc
    (∏ p : S, (fixedVertexNaturalAdmissibleResidues
      (p : ℕ) x (b p)).card) =
        ∏ p : S, if (x : ZMod (p : ℕ)) = 0
          then (p : ℕ) - 2 else (p : ℕ) - 3 := by
      apply Finset.prod_congr rfl
      intro p _
      exact fixedVertexNaturalAdmissibleResidues_card
        p x (b p) (hprime p p.property) (hodd p p.property)
        (hb p p.property) (hfixed p p.property)
    _ = _ := Finset.prod_coe_sort S
      (fun p => if (x : ZMod p) = 0 then p - 2 else p - 3)

/-- Every divisor of a squarefree prime-support product is exactly the product
of one subset of that support. -/
theorem affineSelector_primeSupport_divisors_eq_powerset_image
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).divisors =
      S.powerset.image fun T => ∏ p ∈ T, p := by
  classical
  have hWsq : Squarefree (∏ p ∈ S, p) :=
    Sieve.prodDistinctPrimes_squarefree S hprime
  have hWne : (∏ p ∈ S, p) ≠ 0 := hWsq.ne_zero
  ext d
  rw [Nat.mem_divisors, Finset.mem_image]
  constructor
  · rintro ⟨hd, _⟩
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hd hWsq
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr ?_, ?_⟩
    · rw [← Nat.primeFactors_prod hprime]
      exact Nat.primeFactors_mono hd hWne
    · exact Nat.prod_primeFactors_of_squarefree hdsq
  · rintro ⟨T, hT, rfl⟩
    exact ⟨Finset.prod_dvd_prod_of_subset T S id
      (Finset.mem_powerset.mp hT), hWne⟩

/-- Products of subsets of a prime support are unique, since their genuine
prime-factor finsets recover exactly those subsets. -/
theorem affineSelector_primeSupport_subset_product_injective
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p)
      (↑S.powerset : Set (Finset ℕ)) := by
  intro T hT U hU heq
  have hTsub : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_coe.mp hT)
  have hUsub : U ⊆ S := Finset.mem_powerset.mp (Finset.mem_coe.mp hU)
  have hTprime : ∀ p ∈ T, p.Prime :=
    fun p hp => hprime p (hTsub hp)
  have hUprime : ∀ p ∈ U, p.Prime :=
    fun p hp => hprime p (hUsub hp)
  have hfactor := congrArg Nat.primeFactors heq
  rwa [Nat.primeFactors_prod hTprime,
    Nat.primeFactors_prod hUprime] at hfactor

/-- Exact reindexing of arbitrary coefficient sums over the manuscript's
actual squarefree divisor set by support subsets. -/
theorem affineSelector_sum_divisors_eq_powerset
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (f : ℕ → ℝ) :
    (∑ d ∈ (∏ p ∈ S, p).divisors, f d) =
      ∑ T ∈ S.powerset, f (∏ p ∈ T, p) := by
  classical
  rw [affineSelector_primeSupport_divisors_eq_powerset_image S hprime,
    Finset.sum_image]
  intro T hT U hU heq
  exact affineSelector_primeSupport_subset_product_injective S hprime
    (Finset.mem_coe.mpr hT) (Finset.mem_coe.mpr hU) heq

/-- The genuine switched-prime local coefficient sum, defined from the actual
admissible moving-residue set rather than from a presumed symbolic factor. -/
noncomputable def actualFixedVertexSwitchedFactor
    (p : ℕ) [Fact p.Prime] (x b : ZMod p) : ℝ :=
  (p : ℝ) *
      ((fixedVertexAdmissibleResidues (ZMod p) x b).card : ℝ) /
      ((p : ℝ) - 1) ^ 2 +
    if x = 0 then 0 else 1 / ((p : ℝ) - 1)

/-- The actual admissible-residue coefficient sum is exactly the normalized
factor previously used in the support-uniform cancellation argument. -/
theorem actualFixedVertexSwitchedFactor_eq
    (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hlarge : 3 < p)
    (x b : ZMod p) (hb : b ≠ 0)
    (hfixed : (2 : ZMod p) * x ≠ b) :
    actualFixedVertexSwitchedFactor p x b =
      fixedVertexSwitchedFactor p (decide (x = 0)) := by
  have hpodd : p ≠ 2 := by omega
  have hp2 : 2 ≤ p := by omega
  have hp3 : 3 ≤ p := by omega
  have hone : (p : ℝ) ≠ 1 := by
    exact_mod_cast (show p ≠ 1 by omega)
  unfold actualFixedVertexSwitchedFactor
  rw [fixedVertexAdmissibleResidues_card_zmod p hp hpodd x b hb hfixed]
  by_cases hx : x = 0
  · simp only [hx, ↓reduceIte, decide_true,
      fixedVertexSwitchedFactor, ↓reduceIte, add_zero]
    rw [Nat.cast_sub hp2]
    norm_num
    simpa [one_div] using fixedVertex_divisible_switched_factor_identity hone
  · simp only [hx, ↓reduceIte, decide_false,
      fixedVertexSwitchedFactor, Bool.false_eq, ↓reduceIte]
    rw [Nat.cast_sub hp3]
    norm_num
    simpa [one_div] using fixedVertex_generic_switched_factor_identity hone

/-- Actual admissible-residue local coefficient sums are nonnegative. -/
theorem actualFixedVertexSwitchedFactor_nonneg
    (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hlarge : 3 < p)
    (x b : ZMod p) (hb : b ≠ 0)
    (hfixed : (2 : ZMod p) * x ≠ b) :
    0 ≤ actualFixedVertexSwitchedFactor p x b := by
  rw [actualFixedVertexSwitchedFactor_eq p hp hlarge x b hb hfixed]
  exact fixedVertexSwitchedFactor_nonneg p (decide (x = 0)) hlarge

/-- Actual admissible-residue local coefficient sums never exceed one. -/
theorem actualFixedVertexSwitchedFactor_le_one
    (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hlarge : 3 < p)
    (x b : ZMod p) (hb : b ≠ 0)
    (hfixed : (2 : ZMod p) * x ≠ b) :
    actualFixedVertexSwitchedFactor p x b ≤ 1 := by
  rw [actualFixedVertexSwitchedFactor_eq p hp hlarge x b hb hfixed]
  exact fixedVertexSwitchedFactor_le_one p (decide (x = 0))

/-- A natural-coordinate presentation of the actual finite-field coefficient
factor, allowing genuine factors over differing prime fields to be multiplied
without assuming a global prime-field type-class instance. -/
noncomputable def actualFixedVertexNaturalSwitchedFactor
    (p x b : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    actualFixedVertexSwitchedFactor p (x : ZMod p) (b : ZMod p)
  else 0

/-- Natural-coordinate actual local coefficient factors equal their
normalized switched factors, with the true fixed-vertex residue selector. -/
theorem actualFixedVertexNaturalSwitchedFactor_eq
    (p x b : ℕ) (hp : p.Prime) (hlarge : 3 < p)
    (hb : (b : ZMod p) ≠ 0)
    (hfixed : (2 : ZMod p) * (x : ZMod p) ≠ (b : ZMod p)) :
    actualFixedVertexNaturalSwitchedFactor p x b =
      fixedVertexSwitchedFactor p
        (decide ((x : ZMod p) = 0)) := by
  classical
  unfold actualFixedVertexNaturalSwitchedFactor
  simp only [hp, ↓reduceDIte]
  exact @actualFixedVertexSwitchedFactor_eq p ⟨hp⟩ hp hlarge
    (x : ZMod p) (b : ZMod p) hb hfixed

/-- Arbitrarily many *actual* switched-prime moving-residue coefficient sums
have product at most one.  Every local factor here is defined by the genuine
selector set in its own prime field, not by an assumed singular series. -/
theorem actualFixedVertexNaturalSwitchedFactor_product_le_one
    (S : Finset ℕ) (x b : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, (b : ZMod p) ≠ 0)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b : ZMod p)) :
    (∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p x b) ≤ 1 := by
  calc
    (∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p x b) =
        ∏ p ∈ S, fixedVertexSwitchedFactor p
          (decide ((x : ZMod p) = 0)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact actualFixedVertexNaturalSwitchedFactor_eq p x b
        (hsupport p hp).1 (hsupport p hp).2
        (hb p hp) (hfixed p hp)
    _ ≤ 1 := fixedVertexSwitchedFactor_product_le_one S
      (fun p hp => (hsupport p hp).2)
      (fun p => decide ((x : ZMod p) = 0))

/-- The full actual selector-adjusted fixed-vertex leading constant is
absolutely uniform over switched support and bounded by `2025 / 2`. -/
theorem actualFixedVertex_selector_adjusted_leading_constant_le
    (S : Finset ℕ) (x b : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, (b : ZMod p) ≠ 0)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b : ZMod p)) :
    (270 : ℝ) * 2 * (3 / 2) * (5 / 4) *
      (∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p x b) ≤
        2025 / 2 := by
  rw [unrestricted_formal_degree_leading_constant_eq]
  nlinarith [actualFixedVertexNaturalSwitchedFactor_product_le_one
    S x b hsupport hb hfixed]

/-- The principal coefficient branch is the genuine local selector cardinality
with its full two-prime normalization. -/
noncomputable def actualFixedVertexPrincipalFactor
    (p x b : ℕ) : ℝ :=
  (p : ℝ) *
    ((fixedVertexNaturalAdmissibleResidues p x b).card : ℝ) /
      ((p : ℝ) - 1) ^ 2

/-- The second coefficient branch occurs precisely when the fixed vertex does
not vanish modulo the switched prime. -/
noncomputable def actualFixedVertexExceptionalFactor
    (p x : ℕ) : ℝ :=
  if (x : ZMod p) = 0 then 0 else 1 / ((p : ℝ) - 1)

/-- The two genuine coefficient branches add to the exact actual finite-field
selector factor, not to an assumed asymptotic singular-series value. -/
theorem actualFixedVertex_branch_sum_eq
    (p x b : ℕ) (hp : p.Prime) :
    actualFixedVertexPrincipalFactor p x b +
      actualFixedVertexExceptionalFactor p x =
        actualFixedVertexNaturalSwitchedFactor p x b := by
  classical
  simp [actualFixedVertexPrincipalFactor,
    actualFixedVertexExceptionalFactor,
    actualFixedVertexNaturalSwitchedFactor,
    fixedVertexNaturalAdmissibleResidues,
    actualFixedVertexSwitchedFactor, hp]

/-- Exact factorization of the full *actual squarefree-divisor coefficient
sum*: its principal branches use genuine local selector cardinalities and its
secondary branches use the actual fixed-vertex residue condition. -/
theorem actualFixedVertex_divisor_coefficient_sum_eq_product
    (S : Finset ℕ) (x : ℕ) (b : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    (∑ d ∈ (∏ p ∈ S, p).divisors,
      (∏ p ∈ d.primeFactors,
        actualFixedVertexPrincipalFactor p x (b p)) *
      ∏ p ∈ S \ d.primeFactors,
        actualFixedVertexExceptionalFactor p x) =
      ∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p x (b p) := by
  rw [affineSelector_sum_divisors_eq_powerset S hprime]
  calc
    (∑ T ∈ S.powerset,
      (∏ p ∈ (∏ q ∈ T, q).primeFactors,
        actualFixedVertexPrincipalFactor p x (b p)) *
      ∏ p ∈ S \ (∏ q ∈ T, q).primeFactors,
        actualFixedVertexExceptionalFactor p x) =
        ∑ T ∈ S.powerset,
          (∏ p ∈ T, actualFixedVertexPrincipalFactor p x (b p)) *
          ∏ p ∈ S \ T, actualFixedVertexExceptionalFactor p x := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTprime : ∀ p ∈ T, p.Prime := fun p hp =>
        hprime p ((Finset.mem_powerset.mp hT) hp)
      rw [Nat.primeFactors_prod hTprime]
    _ = ∏ p ∈ S,
        (actualFixedVertexPrincipalFactor p x (b p) +
          actualFixedVertexExceptionalFactor p x) :=
      (Finset.prod_add
        (fun p => actualFixedVertexPrincipalFactor p x (b p))
        (fun p => actualFixedVertexExceptionalFactor p x) S).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact actualFixedVertex_branch_sum_eq p x (b p) (hprime p hp)

/-- The actual squarefree-divisor coefficient sum, including every genuine
selector cardinality and every switched coefficient pattern, is uniformly at
most one for arbitrary support and prime-dependent switched targets. -/
theorem actualFixedVertex_divisor_coefficient_sum_le_one
    (S : Finset ℕ) (x : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, (b p : ZMod p) ≠ 0)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p)) :
    (∑ d ∈ (∏ p ∈ S, p).divisors,
      (∏ p ∈ d.primeFactors,
        actualFixedVertexPrincipalFactor p x (b p)) *
      ∏ p ∈ S \ d.primeFactors,
        actualFixedVertexExceptionalFactor p x) ≤ 1 := by
  rw [actualFixedVertex_divisor_coefficient_sum_eq_product
    S x b (fun p hp => (hsupport p hp).1)]
  calc
    (∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p x (b p)) =
        ∏ p ∈ S, fixedVertexSwitchedFactor p
          (decide ((x : ZMod p) = 0)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact actualFixedVertexNaturalSwitchedFactor_eq p x (b p)
        (hsupport p hp).1 (hsupport p hp).2
        (hb p hp) (hfixed p hp)
    _ ≤ 1 := fixedVertexSwitchedFactor_product_le_one S
      (fun p hp => (hsupport p hp).2)
      (fun p => decide ((x : ZMod p) = 0))

#print axioms Erdos689.fixedVertex_generic_switched_factor_identity
#print axioms Erdos689.fixedVertex_divisible_switched_factor_identity
#print axioms Erdos689.fixedVertexSwitchedFactor_nonneg
#print axioms Erdos689.fixedVertexSwitchedFactor_le_one
#print axioms Erdos689.fixedVertexSwitchedFactor_product_le_one
#print axioms Erdos689.fixedLabel_normalizedSwitchedFactor_nonneg
#print axioms Erdos689.fixedLabel_normalizedSwitchedFactor_product_le_one
#print axioms Erdos689.fixedVertex_selector_adjusted_leading_constant_le
#print axioms Erdos689.fixedLabel_selector_adjusted_leading_constant_le
#print axioms Erdos689.fixedVertex_two_mul_eq_iff
#print axioms Erdos689.fixedVertexAdmissibleResidues_eq_erase
#print axioms Erdos689.fixedVertexAdmissibleResidues_card_of_zero
#print axioms Erdos689.fixedVertexAdmissibleResidues_card_of_ne_zero
#print axioms Erdos689.fixedVertexAdmissibleResidues_card_zmod
#print axioms Erdos689.affineCrtRestrictedResidues_mem_iff
#print axioms Erdos689.affineCrtRestrictedResidues_card
#print axioms Erdos689.affineSelector_primeSupport_pairwise_coprime
#print axioms Erdos689.fixedVertexNaturalAdmissibleResidues_card
#print axioms Erdos689.fixedVertexSupport_crt_selector_card
#print axioms Erdos689.affineSelector_primeSupport_divisors_eq_powerset_image
#print axioms Erdos689.affineSelector_primeSupport_subset_product_injective
#print axioms Erdos689.affineSelector_sum_divisors_eq_powerset
#print axioms Erdos689.actualFixedVertexSwitchedFactor_eq
#print axioms Erdos689.actualFixedVertexSwitchedFactor_nonneg
#print axioms Erdos689.actualFixedVertexSwitchedFactor_le_one
#print axioms Erdos689.actualFixedVertexNaturalSwitchedFactor_eq
#print axioms Erdos689.actualFixedVertexNaturalSwitchedFactor_product_le_one
#print axioms Erdos689.actualFixedVertex_selector_adjusted_leading_constant_le
#print axioms Erdos689.actualFixedVertex_branch_sum_eq
#print axioms Erdos689.actualFixedVertex_divisor_coefficient_sum_eq_product
#print axioms Erdos689.actualFixedVertex_divisor_coefficient_sum_le_one

end Erdos689
