module

public import RobustCrtBridge

@[expose] public section


/-!
# Exact zero-hit CRT counts for arbitrary smooth or nonsmooth coefficients

The actual natural unit representatives modulo `W = ∏ s ∈ S, s` map
bijectively onto the complete product of local nonzero prime residues. At a
support prime dividing `c`, the target `c * r` can never hit the nonzero
designated class, leaving all `s - 1` local choices. At every other support
prime, exactly one of those choices is forbidden, leaving `s - 2`.

Consequently the exact number of reduced residues with no actual switched hit
is `∏ s ∈ S, if s ∣ c then s - 1 else s - 2`. The coefficient `c` need not be
coprime to `W`, and need not even be smooth. This bridges the true manuscript
zero-hit predicate to its mixed local Euler factors; it does not assert an
infinite smooth-core asymptotic or solve Erdős #689.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- The concrete switched-prime coordinate vector of a natural representative. -/
def primeUnitCoordinate (S : Finset ℕ) (r : ℕ) :
    {p : ℕ // p ∈ S} → ℕ := fun p => r % (p : ℕ)

/-- Actual natural units fill the complete independent prime-coordinate product. -/
theorem actual_unit_coordinate_image_eq
    (S : Finset ℕ) (hsupport : ∀ p ∈ S, p.Prime) :
    (naturalUnitResidues (∏ p ∈ S, p)).image (primeUnitCoordinate S) =
      Fintype.piFinset (fun p : {p : ℕ // p ∈ S} =>
        Finset.Ico 1 (p : ℕ)) := by
  classical
  let W := ∏ p ∈ S, p
  let A := naturalUnitResidues W
  let V := Fintype.piFinset
    (fun p : {p : ℕ // p ∈ S} => Finset.Ico 1 (p : ℕ))
  have hinj : Set.InjOn (primeUnitCoordinate S) (A : Set ℕ) := by
    intro r hr r' hr' heq
    have hrlt := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hr'lt := Finset.mem_range.mp (Finset.mem_filter.mp hr').1
    apply prime_support_residue_coordinate_injective S hsupport hrlt hr'lt
    intro p hp
    exact congrFun heq ⟨p, hp⟩
  have hsubset : A.image (primeUnitCoordinate S) ⊆ V := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro p
    exact prime_support_unit_coordinate_mem S hsupport
      (Finset.mem_filter.mp hr).2 p.2
  have hcard : V.card = (A.image (primeUnitCoordinate S)).card := by
    rw [Finset.card_image_of_injOn hinj,
      natural_unit_residues_card W, prime_support_totient_product S hsupport]
    exact prime_unit_vector_card S
  exact Finset.eq_of_subset_of_card_le hsubset hcard.le

/-- A designated nonzero support class can never hit a coefficient divisible by that prime. -/
theorem switched_prime_hit_iff_mixed_coordinate
    {S : Finset ℕ} {b : ℕ → ℕ} {c r p : ℕ}
    (_hpS : p ∈ S) (hp : p.Prime)
    (hb : Nat.Coprime (b p) p) :
    b p ≡ c * r [MOD p] ↔
      ¬ p ∣ c ∧ r % p = designatedPrimeHit p c (b p) := by
  by_cases hdiv : p ∣ c
  · have htarget : (c * r) % p = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdiv r)
    constructor
    · intro hhit
      change b p % p = (c * r) % p at hhit
      have hbdiv : p ∣ b p := Nat.dvd_of_mod_eq_zero (hhit.trans htarget)
      exact False.elim ((hp.coprime_iff_not_dvd.mp hb.symm) hbdiv)
    · intro h
      exact False.elim (h.1 hdiv)
  · have hc : Nat.Coprime c p :=
      (hp.coprime_iff_not_dvd.mpr hdiv).symm
    simpa [hdiv] using
      (actual_prime_hit_iff_coordinate_eq p c (b p) r hp hc hb)

/-- The independent local coordinate sets for an arbitrary coefficient. -/
noncomputable def mixedZeroHitCoordinates
    (S : Finset ℕ) (b : ℕ → ℕ) (c : ℕ) :
    Finset ({p : ℕ // p ∈ S} → ℕ) := by
  classical
  exact Fintype.piFinset fun p : {p : ℕ // p ∈ S} =>
    if (p : ℕ) ∣ c then Finset.Ico 1 (p : ℕ)
    else (Finset.Ico 1 (p : ℕ)).erase (designatedPrimeHit p c (b p))

/-- The exact mixed local zero-hit vector count has factors `p-1` and `p-2`. -/
theorem mixed_zero_hit_coordinates_card
    (S : Finset ℕ) (b : ℕ → ℕ) (c : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    (mixedZeroHitCoordinates S b c).card =
      ∏ p ∈ S, if p ∣ c then p - 1 else p - 2 := by
  classical
  unfold mixedZeroHitCoordinates
  rw [Fintype.card_piFinset]
  calc
    (∏ p : {p : ℕ // p ∈ S},
      (if (p : ℕ) ∣ c then Finset.Ico 1 (p : ℕ)
        else (Finset.Ico 1 (p : ℕ)).erase
          (designatedPrimeHit p c (b p))).card) =
        ∏ p : {p : ℕ // p ∈ S},
          if (p : ℕ) ∣ c then (p : ℕ) - 1 else (p : ℕ) - 2 := by
      apply Fintype.prod_congr
      intro p
      by_cases hdiv : (p : ℕ) ∣ c
      · simp [hdiv]
      · have hc : Nat.Coprime c (p : ℕ) :=
          ((hsupport p p.2).coprime_iff_not_dvd.mpr hdiv).symm
        have hdesign := (designated_prime_hit_spec p c (b p)
          (hsupport p p.2) hc (hb p p.2)).1
        simp [hdiv, Finset.card_erase_of_mem hdesign, Nat.sub_sub]
    _ = _ := Finset.prod_coe_sort S
      (fun p : ℕ => if p ∣ c then p - 1 else p - 2)

/-- The actual zero-hit natural residues are exactly the mixed CRT vector set. -/
theorem actual_zero_hit_coordinate_image_eq
    (S : Finset ℕ) (b : ℕ → ℕ) (c : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    ((naturalUnitResidues (∏ p ∈ S, p)).filter
      fun r => switchedHits S b (c * r) = 0).image
        (primeUnitCoordinate S) = mixedZeroHitCoordinates S b c := by
  classical
  let W := ∏ p ∈ S, p
  let A := naturalUnitResidues W
  let V := Fintype.piFinset
    (fun p : {p : ℕ // p ∈ S} => Finset.Ico 1 (p : ℕ))
  have hfull := actual_unit_coordinate_image_eq S hsupport
  ext v
  constructor
  · intro hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hunit, hzero⟩ := Finset.mem_filter.mp hr
    have hmiss : ∀ p ∈ S, ¬ b p ≡ c * r [MOD p] := by
      exact Finset.card_filter_eq_zero_iff.mp hzero
    apply Fintype.mem_piFinset.mpr
    intro p
    have hcoordinate := prime_support_unit_coordinate_mem
      S hsupport (Finset.mem_filter.mp hunit).2 p.2
    by_cases hdiv : (p : ℕ) ∣ c
    · simpa [mixedZeroHitCoordinates, primeUnitCoordinate, hdiv] using hcoordinate
    · have hnot : r % (p : ℕ) ≠ designatedPrimeHit p c (b p) := by
        intro heq
        exact hmiss p p.2
          ((switched_prime_hit_iff_mixed_coordinate p.2
            (hsupport p p.2) (hb p p.2)).mpr ⟨hdiv, heq⟩)
      simpa [mixedZeroHitCoordinates, primeUnitCoordinate, hdiv, Finset.mem_erase] using
        And.intro hnot hcoordinate
  · intro hv
    have hvcoords : ∀ p : {p : ℕ // p ∈ S},
        v p ∈ if (p : ℕ) ∣ c then Finset.Ico 1 (p : ℕ)
          else (Finset.Ico 1 (p : ℕ)).erase
            (designatedPrimeHit p c (b p)) :=
      Fintype.mem_piFinset.mp hv
    have hvfull : v ∈ V := by
      apply Fintype.mem_piFinset.mpr
      intro p
      specialize hvcoords p
      split_ifs at hvcoords with hdiv
      · exact hvcoords
      · exact Finset.mem_of_mem_erase hvcoords
    have himage : v ∈ A.image (primeUnitCoordinate S) := by
      rw [hfull]
      exact hvfull
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp himage
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, ?_⟩, heq⟩
    apply Finset.card_filter_eq_zero_iff.mpr
    intro p hp hhit
    have hmixed :=
      (switched_prime_hit_iff_mixed_coordinate hp (hsupport p hp)
        (hb p hp)).mp hhit
    have hcoord := hvcoords ⟨p, hp⟩
    rw [if_neg hmixed.1] at hcoord
    have hnot := (Finset.mem_erase.mp hcoord).1
    apply hnot
    rw [← heq]
    exact hmixed.2

/-- The exact actual zero-hit unit-residue count for arbitrary, possibly nonunit, `c`. -/
theorem actual_zero_hit_unit_residues_card
    (S : Finset ℕ) (b : ℕ → ℕ) (c : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    ((Finset.range (∏ p ∈ S, p)).filter fun r =>
      Nat.Coprime r (∏ p ∈ S, p) ∧ switchedHits S b (c * r) = 0).card =
        ∏ p ∈ S, if p ∣ c then p - 1 else p - 2 := by
  classical
  let W := ∏ p ∈ S, p
  let A := (naturalUnitResidues W).filter
    fun r => switchedHits S b (c * r) = 0
  have hset : ((Finset.range W).filter fun r =>
      Nat.Coprime r W ∧ switchedHits S b (c * r) = 0) = A := by
    ext r
    simp [A, naturalUnitResidues, and_assoc]
  have hinj : Set.InjOn (primeUnitCoordinate S) (A : Set ℕ) := by
    intro r hr r' hr' heq
    have hrunit := (Finset.mem_filter.mp hr).1
    have hr'unit := (Finset.mem_filter.mp hr').1
    have hrlt := Finset.mem_range.mp (Finset.mem_filter.mp hrunit).1
    have hr'lt := Finset.mem_range.mp (Finset.mem_filter.mp hr'unit).1
    apply prime_support_residue_coordinate_injective S hsupport hrlt hr'lt
    intro p hp
    exact congrFun heq ⟨p, hp⟩
  rw [hset, ← Finset.card_image_of_injOn hinj,
    actual_zero_hit_coordinate_image_eq S b c hsupport hb,
    mixed_zero_hit_coordinates_card S b c hsupport hb]


end Erdos689
