module

public import Mathlib
public import AnalyticBridge
public import RobustCrtDensity
public import RobustSupportDensity
public import UniformLocalFactors

@[expose] public section


open Finset
open scoped BigOperators

namespace Erdos689

/-- Natural unit representatives in the actual residue interval `[0,W)`. -/
noncomputable def naturalUnitResidues (W : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range W).filter fun r => Nat.Coprime r W

/-- The actual natural unit representatives have exactly Euler-totient
cardinality, including the degenerate modulus `W=1`. -/
theorem natural_unit_residues_card (W : ℕ) :
    (naturalUnitResidues W).card = W.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext r
  simp [naturalUnitResidues, Nat.coprime_comm]

/-- The real manuscript robust residues are a subset of the real natural unit
residue set, not merely of an abstract coordinate product. -/
theorem robust_residues_subset_natural_units (S : Finset ℕ) (b : ℕ → ℕ)
    (J : ℕ) :
    robustResidues S b J ⊆ naturalUnitResidues (∏ s ∈ S, s) := by
  classical
  intro r hr
  have h := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨h.1, h.2.1⟩

/-- The exact complement of the actual robust residues is precisely the set of
unit representatives failing at one of the manuscript offsets. -/
theorem mem_nonrobust_unit_residues_iff (S : Finset ℕ) (b : ℕ → ℕ)
    (J r : ℕ) :
    r ∈ naturalUnitResidues (∏ s ∈ S, s) \ robustResidues S b J ↔
      r < (∏ s ∈ S, s) ∧ Nat.Coprime r (∏ s ∈ S, s) ∧
        ∃ j ∈ Finset.Icc 1 J, switchedHits S b (j * r) < 2 := by
  classical
  simp [naturalUnitResidues, robustResidues, robustResidue]
  constructor
  · rintro ⟨⟨hr, hcoprime⟩, hfailure⟩
    obtain ⟨j, hjone, hjJ, hjhit⟩ := hfailure hr hcoprime
    exact ⟨hr, hcoprime, j, ⟨hjone, hjJ⟩, hjhit⟩
  · rintro ⟨hr, hcoprime, j, ⟨hjone, hjJ⟩, hjhit⟩
    exact ⟨⟨hr, hcoprime⟩, fun _ _ => ⟨j, hjone, hjJ, hjhit⟩⟩

/-- Actual robust and nonrobust natural unit residue counts partition the
exact Euler-totient denominator. -/
theorem robust_residues_complement_card_add (S : Finset ℕ) (b : ℕ → ℕ)
    (J : ℕ) :
    (naturalUnitResidues (∏ s ∈ S, s) \ robustResidues S b J).card +
        (robustResidues S b J).card = (∏ s ∈ S, s).totient := by
  calc
    _ = (naturalUnitResidues (∏ s ∈ S, s)).card :=
      Finset.card_sdiff_add_card_eq_card (robust_residues_subset_natural_units S b J)
    _ = _ := natural_unit_residues_card _

/-- Any independently proved upper bound on the actual bad-residue set gives
the matching exact lower bound for actual manuscript robust residues. -/
theorem robust_residues_card_ge_totient_sub (S : Finset ℕ) (b : ℕ → ℕ)
    (J B : ℕ)
    (hbad : (naturalUnitResidues (∏ s ∈ S, s) \ robustResidues S b J).card ≤ B) :
    (∏ s ∈ S, s).totient - B ≤ (robustResidues S b J).card := by
  have hpartition := robust_residues_complement_card_add S b J
  omega

/-- Natural unit representatives and units of the actual quotient ring are
canonically equivalent, preserving their concrete representatives. -/
noncomputable def naturalUnitResiduesEquivZModUnits (W : ℕ) [NeZero W] :
    {r : ℕ // r < W ∧ Nat.Coprime r W} ≃ (ZMod W)ˣ where
  toFun r := ZMod.unitOfCoprime r.1 r.2.2
  invFun u := ⟨(u : ZMod W).val, (u : ZMod W).val_lt,
    ZMod.val_coe_unit_coprime u⟩
  left_inv r := by
    apply Subtype.ext
    simp [ZMod.coe_unitOfCoprime, Nat.mod_eq_of_lt r.2.1]
  right_inv u := by
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]

/-- The concrete unit-to-natural equivalence has exactly the expected
Euler-totient cardinality. -/
theorem natural_unit_subtype_card (W : ℕ) [NeZero W] :
    Nat.card {r : ℕ // r < W ∧ Nat.Coprime r W} = W.totient := by
  rw [Nat.card_congr (naturalUnitResiduesEquivZModUnits W),
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Congruence at every distinct switched prime implies congruence modulo the
entire squarefree support product. -/
theorem prime_support_modEq_product (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (r r' : ℕ)
    (hlocal : ∀ p ∈ S, r ≡ r' [MOD p]) :
    r ≡ r' [MOD ∏ p ∈ S, p] := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Nat.modEq_one
  | @insert p T hpnot ih =>
    have hp : p.Prime := hprime p (by simp)
    have hrest : ∀ q ∈ T, q.Prime := by
      intro q hq
      exact hprime q (by simp [hq])
    have hnotdiv : ¬ p ∣ ∏ q ∈ T, q := by
      intro hdiv
      obtain ⟨q, hq, hpq⟩ :=
        (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq hp (hrest q hq)).mp hpq
      exact hpnot (by simpa [heq] using hq)
    have hcoprime : p.Coprime (∏ q ∈ T, q) :=
      hp.coprime_iff_not_dvd.mpr hnotdiv
    rw [Finset.prod_insert hpnot]
    apply (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
    exact ⟨hlocal p (by simp), ih hrest (fun q hq => hlocal q (by simp [hq]))⟩

/-- Actual natural unit representatives below the support product are
determined uniquely by their switched-prime coordinates. This is precisely the
CRT injectivity needed for the bad-residue counting argument. -/
theorem prime_support_residue_coordinate_injective (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) {r r' : ℕ}
    (hr : r < ∏ p ∈ S, p) (hr' : r' < ∏ p ∈ S, p)
    (hlocal : ∀ p ∈ S, r % p = r' % p) :
    r = r' := by
  have heq := prime_support_modEq_product S hprime r r' hlocal
  change r % (∏ p ∈ S, p) = r' % (∏ p ∈ S, p) at heq
  simpa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] using heq

/-- Every coordinate of an actual unit representative is a nonzero local
prime-unit representative. -/
theorem prime_support_unit_coordinate_mem (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) {r p : ℕ}
    (hunit : Nat.Coprime r (∏ q ∈ S, q)) (hp : p ∈ S) :
    r % p ∈ Finset.Ico 1 p := by
  have hpp := hprime p hp
  have hdvd : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
  have hcop : Nat.Coprime r p := hunit.coprime_dvd_right hdvd
  have hnot : ¬ p ∣ r := hpp.coprime_iff_not_dvd.mp hcop.symm
  have hnonzero : r % p ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_of_mod_eq_zero hzero)
  exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hnonzero,
    Nat.mod_lt r hpp.pos⟩

/-- At a switched prime, a coprime offset has at most one unit representative
solving the designated-hit congruence. -/
theorem prime_coordinate_hit_unique {p j c r₁ r₂ : ℕ}
    (hcoprime : Nat.Coprime j p) (hr₁ : r₁ < p) (hr₂ : r₂ < p)
    (h₁ : c ≡ j * r₁ [MOD p]) (h₂ : c ≡ j * r₂ [MOD p]) :
    r₁ = r₂ := by
  have hmul : j * r₁ ≡ j * r₂ [MOD p] := h₁.symm.trans h₂
  have heq : r₁ ≡ r₂ [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcoprime.symm hmul
  change r₁ % p = r₂ % p at heq
  simpa [Nat.mod_eq_of_lt hr₁, Nat.mod_eq_of_lt hr₂] using heq

/-- Every nonzero designated residue at a switched prime has exactly one
nonzero local unit coordinate producing a hit at any coprime offset. -/
theorem prime_coordinate_hit_exists_unique (p j c : ℕ) (hp : p.Prime)
    (hj : Nat.Coprime j p) (hc : Nat.Coprime c p) :
    ∃! r : ℕ, r ∈ Finset.Ico 1 p ∧ c ≡ j * r [MOD p] := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let ju : (ZMod p)ˣ := ZMod.unitOfCoprime j hj
  let cu : (ZMod p)ˣ := ZMod.unitOfCoprime c hc
  let ru : (ZMod p)ˣ := ju⁻¹ * cu
  let r : ℕ := (ru : ZMod p).val
  have hrcop : Nat.Coprime r p := ZMod.val_coe_unit_coprime ru
  have hrne : r ≠ 0 := by
    intro hzero
    have hpone : p = 1 := by simpa [hzero] using hrcop
    exact hp.ne_one hpone
  have hrmem : r ∈ Finset.Ico 1 p :=
    Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hrne, (ru : ZMod p).val_lt⟩
  have hunit : ju * ru = cu := by simp [ru]
  have hcast := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hunit
  have hmod : c ≡ j * r [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff c (j * r) p).mp
    simpa [ju, cu, r, ZMod.coe_unitOfCoprime, Nat.cast_mul] using hcast.symm
  refine ⟨r, ⟨hrmem, hmod⟩, ?_⟩
  intro r' hr'
  exact prime_coordinate_hit_unique hj (Finset.mem_Ico.mp hr'.1).2
    (Finset.mem_Ico.mp hrmem).2 hr'.2 hmod

/-- The uniquely designated unit coordinate at a switched prime; outside the
valid prime/coprimality regime it is harmlessly defined as zero. -/
noncomputable def designatedPrimeHit (p j c : ℕ) : ℕ :=
  if h : p.Prime ∧ Nat.Coprime j p ∧ Nat.Coprime c p then
    Classical.choose (prime_coordinate_hit_exists_unique p j c h.1 h.2.1 h.2.2)
  else 0

/-- The designated coordinate is genuinely a local unit and solves the
manuscript's exact target congruence. -/
theorem designated_prime_hit_spec (p j c : ℕ) (hp : p.Prime)
    (hj : Nat.Coprime j p) (hc : Nat.Coprime c p) :
    designatedPrimeHit p j c ∈ Finset.Ico 1 p ∧
      c ≡ j * designatedPrimeHit p j c [MOD p] := by
  unfold designatedPrimeHit
  rw [dif_pos ⟨hp, hj, hc⟩]
  exact (Classical.choose_spec
    (prime_coordinate_hit_exists_unique p j c hp hj hc)).1

/-- For a valid prime coordinate, the actual switched-hit congruence is
equivalent to equality with its unique designated unit coordinate. -/
theorem actual_prime_hit_iff_coordinate_eq (p j c r : ℕ) (hp : p.Prime)
    (hj : Nat.Coprime j p) (hc : Nat.Coprime c p) :
    c ≡ j * r [MOD p] ↔ r % p = designatedPrimeHit p j c := by
  have hdesign := designated_prime_hit_spec p j c hp hj hc
  constructor
  · intro hhit
    have hmod : c ≡ j * (r % p) [MOD p] := by
      change c % p = (j * (r % p)) % p
      change c % p = (j * r) % p at hhit
      simpa [Nat.mul_mod] using hhit
    exact prime_coordinate_hit_unique hj (Nat.mod_lt r hp.pos)
      (Finset.mem_Ico.mp hdesign.1).2 hmod hdesign.2
  · intro heq
    have hmod : c ≡ j * (r % p) [MOD p] := by
      simpa [heq] using hdesign.2
    change c % p = (j * r) % p
    change c % p = (j * (r % p)) % p at hmod
    simpa [Nat.mul_mod] using hmod

/-- Every positive manuscript offset strictly below a switched prime is
invertible modulo that prime. -/
theorem prime_offset_coprime (p j : ℕ) (hp : p.Prime)
    (hjpos : 0 < j) (hjlt : j < p) :
    Nat.Coprime j p :=
  (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hjpos hjlt)).symm

/-- The genuine manuscript switched-hit count equals the number of matching
coordinates in its actual prime-unit vector, with no surrogate predicate. -/
theorem switched_hits_eq_designated_coordinate_count (S : Finset ℕ)
    (b : ℕ → ℕ) (J j r : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ J < p)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p)
    (hj : j ∈ Finset.Icc 1 J) :
    switchedHits S b (j * r) =
      (Finset.univ.filter fun p : {p : ℕ // p ∈ S} =>
        r % (p : ℕ) = designatedPrimeHit p j (b p)).card := by
  classical
  unfold switchedHits
  apply Finset.card_bij
    (fun p hp => (⟨p, (Finset.mem_filter.mp hp).1⟩ : {p : ℕ // p ∈ S}))
  · intro p hp
    obtain ⟨hpS, hhit⟩ := Finset.mem_filter.mp hp
    have hprime := (hsupport p hpS).1
    have hcoprime := prime_offset_coprime p j hprime
      (Finset.mem_Icc.mp hj).1
      (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (hsupport p hpS).2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (actual_prime_hit_iff_coordinate_eq p j (b p) r hprime hcoprime
        (hb p hpS)).mp hhit⟩
  · intro p hp q hq heq
    exact congrArg Subtype.val heq
  · intro p hp
    have hcoord := (Finset.mem_filter.mp hp).2
    have hprime := (hsupport p p.2).1
    have hcoprime := prime_offset_coprime p j hprime
      (Finset.mem_Icc.mp hj).1
      (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (hsupport p p.2).2)
    refine ⟨p, Finset.mem_filter.mpr ⟨p.2, ?_⟩, ?_⟩
    · exact (actual_prime_hit_iff_coordinate_eq p j (b p) r hprime hcoprime
        (hb p p.2)).mpr hcoord
    · rfl

/-- The complete CRT/union-bound bridge for the *actual* manuscript robust
residues. Every nonrobust natural unit representative injects into the
previously counted prime-coordinate bad-vector space. -/
theorem actual_nonrobust_unit_residues_card_le (S : Finset ℕ)
    (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ J < p)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    (naturalUnitResidues (∏ p ∈ S, p) \ robustResidues S b J).card ≤
      J * ((∏ p ∈ S, (p - 2)) +
        ∑ p : {p : ℕ // p ∈ S},
          ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2)) := by
  classical
  let A := naturalUnitResidues (∏ p ∈ S, p) \ robustResidues S b J
  let coordinate : ℕ → ({p : ℕ // p ∈ S} → ℕ) :=
    fun r p => r % (p : ℕ)
  let designated : ℕ → {p : ℕ // p ∈ S} → ℕ :=
    fun j p => designatedPrimeHit p j (b p)
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hsupport p hp).1
  have hdesign : ∀ j ∈ Finset.Icc 1 J,
      ∀ p : {p : ℕ // p ∈ S}, designated j p ∈ Finset.Ico 1 (p : ℕ) := by
    intro j hj p
    have hcoprime := prime_offset_coprime p j (hprime p p.2)
      (Finset.mem_Icc.mp hj).1
      (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (hsupport p p.2).2)
    exact (designated_prime_hit_spec p j (b p) (hprime p p.2)
      hcoprime (hb p p.2)).1
  have hinj : Set.InjOn coordinate (A : Set ℕ) := by
    intro r hr r' hr' heq
    have hrinfo := (mem_nonrobust_unit_residues_iff S b J r).mp hr
    have hrinfo' := (mem_nonrobust_unit_residues_iff S b J r').mp hr'
    apply prime_support_residue_coordinate_injective S hprime hrinfo.1 hrinfo'.1
    intro p hp
    exact congrFun heq ⟨p, hp⟩
  have himage : A.image coordinate ⊆ primeOffsetBadVectors S J designated := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    have hrinfo := (mem_nonrobust_unit_residues_iff S b J r).mp hr
    have hunitvector : coordinate r ∈
        Fintype.piFinset (fun p : {p : ℕ // p ∈ S} => Finset.Ico 1 (p : ℕ)) := by
      apply Fintype.mem_piFinset.mpr
      intro p
      exact prime_support_unit_coordinate_mem S hprime hrinfo.2.1 p.2
    have hbadvector : ∃ j ∈ Finset.Icc 1 J,
        (Finset.univ.filter fun p : {p : ℕ // p ∈ S} =>
          coordinate r p = designated j p).card < 2 := by
      obtain ⟨j, hj, hbad⟩ := hrinfo.2.2
      refine ⟨j, hj, ?_⟩
      rw [switched_hits_eq_designated_coordinate_count S b J j r
        hsupport hb hj] at hbad
      exact hbad
    have hmember : coordinate r ∈
        (Fintype.piFinset fun p : {p : ℕ // p ∈ S} => Finset.Ico 1 (p : ℕ)).filter
          (fun f => ∃ j ∈ Finset.Icc 1 J,
            (Finset.univ.filter fun p : {p : ℕ // p ∈ S} =>
              f p = designated j p).card < 2) := by
      simpa only [Finset.mem_filter] using And.intro hunitvector hbadvector
    simpa only [primeOffsetBadVectors] using hmember
  calc
    _ = (A.image coordinate).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (primeOffsetBadVectors S J designated).card := Finset.card_le_card himage
    _ ≤ _ := prime_unit_multi_offset_low_hit_card_le S J designated hdesign

/-- End-to-end lower bound for the genuine manuscript robust-residue count,
with the exact Euler-totient denominator and the full switched-prime
zero-hit/one-hit correction. -/
theorem actual_robust_residues_card_lower (S : Finset ℕ)
    (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ J < p)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    (∏ p ∈ S, p).totient -
      J * ((∏ p ∈ S, (p - 2)) +
        ∑ p : {p : ℕ // p ∈ S},
          ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2)) ≤
      (robustResidues S b J).card :=
  robust_residues_card_ge_totient_sub S b J _
    (actual_nonrobust_unit_residues_card_le S b J hsupport hb)

/-- The actual *real normalized* robust-density deficit satisfies the exact
finite CRT union bound, expressed with its integer zero-hit and one-hit
counts over the actual Euler-totient denominator. -/
theorem actual_robust_density_deficit_le (S : Finset ℕ)
    (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ J < p)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    1 - ((robustResidues S b J).card : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) ≤
      (J : ℝ) *
        (((∏ p ∈ S, (p - 2)) +
          ∑ p : {p : ℕ // p ∈ S},
            ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2) : ℕ) : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
  have hpositive : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have htotient : (0 : ℝ) < (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hpositive
  have hpartition := robust_residues_complement_card_add S b J
  have hpartition_real :
      (((naturalUnitResidues (∏ p ∈ S, p) \ robustResidues S b J).card : ℕ) : ℝ) +
        (((robustResidues S b J).card : ℕ) : ℝ) =
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
    exact_mod_cast hpartition
  have hbad := actual_nonrobust_unit_residues_card_le S b J hsupport hb
  calc
    1 - ((robustResidues S b J).card : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) =
        ((naturalUnitResidues (∏ p ∈ S, p) \ robustResidues S b J).card : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
            field_simp
            linarith
    _ ≤ ((J * ((∏ p ∈ S, (p - 2)) +
        ∑ p : {p : ℕ // p ∈ S},
          ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2)) : ℕ) : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
            apply (div_le_div_iff_of_pos_right htotient).mpr
            exact_mod_cast hbad
    _ = _ := by push_cast; ring

/-- Algebraic zero-hit plus unique-hit decomposition for any finite family of
nonzero real local factors. -/
theorem real_zero_and_one_hit_product_identity {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : ι → ℝ) (hx : ∀ i, x i ≠ 0) :
    (∏ i : ι, x i) +
        ∑ i : ι, ∏ j ∈ (Finset.univ.erase i), x j =
      (∏ i : ι, x i) * (1 + ∑ i : ι, 1 / x i) := by
  have herase (i : ι) :
      (∏ j ∈ (Finset.univ.erase i), x j) = (∏ j : ι, x j) / x i := by
    apply (eq_div_iff (hx i)).mpr
    exact Finset.prod_erase_mul Finset.univ x (Finset.mem_univ i)
  simp_rw [herase, div_eq_mul_inv]
  rw [mul_add, mul_one, Finset.mul_sum]
  simp

/-- The exact natural CRT zero-hit/one-hit count, normalized by the true
Euler-totient, is *identically* the manuscript's switched-prime product
majorant. -/
theorem prime_crt_correction_normalized_identity (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    ((((∏ p ∈ S, (p - 2)) +
      ∑ p : {p : ℕ // p ∈ S},
        ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2) : ℕ) : ℝ) /
      (((∏ p ∈ S, p).totient : ℕ) : ℝ)) =
        (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) *
          (1 + ∑ p ∈ S, 1 / ((p : ℝ) - 2)) := by
  classical
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hsupport p hp).1
  have hfactor (p : ℕ) (hp : p ∈ S) :
      (((p - 2 : ℕ) : ℕ) : ℝ) = (p : ℝ) - 2 := by
    have hlarge := (hsupport p hp).2
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    norm_num
  have hzero :
      (((∏ p ∈ S, (p - 2)) : ℕ) : ℝ) =
        ∏ p : {p : ℕ // p ∈ S}, (((p : ℕ) : ℝ) - 2) := by
    calc
      (((∏ p ∈ S, (p - 2)) : ℕ) : ℝ) =
          ∏ p ∈ S, (((p - 2 : ℕ) : ℕ) : ℝ) := by norm_cast
      _ = ∏ p ∈ S, ((p : ℝ) - 2) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hfactor p hp
      _ = _ := (Finset.prod_coe_sort S (fun p : ℕ => (p : ℝ) - 2)).symm
  have hone (p : {p : ℕ // p ∈ S}) :
      (((∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2)) : ℕ) : ℝ) =
        ∏ q ∈ (Finset.univ.erase p), (((q : ℕ) : ℝ) - 2) := by
    calc
      (((∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2)) : ℕ) : ℝ) =
          ∏ q ∈ (Finset.univ.erase p), ((((q : ℕ) - 2 : ℕ) : ℕ) : ℝ) := by
            norm_cast
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q _
        exact hfactor q q.2
  have hnonzero (p : {p : ℕ // p ∈ S}) : (((p : ℕ) : ℝ) - 2) ≠ 0 := by
    have hlarge : (3 : ℝ) < (p : ℕ) := by exact_mod_cast (hsupport p p.2).2
    linarith
  have hcorrection :
      ((((∏ p ∈ S, (p - 2)) +
        ∑ p : {p : ℕ // p ∈ S},
          ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2) : ℕ) : ℝ)) =
        (∏ p : {p : ℕ // p ∈ S}, (((p : ℕ) : ℝ) - 2)) *
          (1 + ∑ p : {p : ℕ // p ∈ S}, 1 / (((p : ℕ) : ℝ) - 2)) := by
    rw [Nat.cast_add, Nat.cast_sum, hzero]
    simp_rw [hone]
    exact real_zero_and_one_hit_product_identity
      (fun p : {p : ℕ // p ∈ S} => (((p : ℕ) : ℝ) - 2)) hnonzero
  have hratio :
      (∏ p : {p : ℕ // p ∈ S}, (((p : ℕ) : ℝ) - 2)) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) =
        ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1)) := by
    have hproduct :
        (∏ p : {p : ℕ // p ∈ S}, (((p : ℕ) : ℝ) - 2)) =
          ∏ p ∈ S, ((p : ℝ) - 2) :=
      Finset.prod_coe_sort S (fun p : ℕ => (p : ℝ) - 2)
    rw [hproduct, prime_support_totient_real_product S hprime,
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hlarge : (3 : ℝ) < p := by exact_mod_cast (hsupport p hp).2
    have hden : (p : ℝ) - 1 ≠ 0 := by linarith
    calc
      ((p : ℝ) - 2) / ((p : ℝ) - 1) =
          (((p : ℝ) - 1) - 1) / ((p : ℝ) - 1) := by ring
      _ = 1 - 1 / ((p : ℝ) - 1) := by rw [sub_div, div_self hden]
  rw [hcorrection]
  calc
    (∏ p : {p : ℕ // p ∈ S}, (((p : ℕ) : ℝ) - 2)) *
        (1 + ∑ p : {p : ℕ // p ∈ S}, 1 / (((p : ℕ) : ℝ) - 2)) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) =
      ((∏ p : {p : ℕ // p ∈ S}, (((p : ℕ) : ℝ) - 2)) /
        (((∏ p ∈ S, p).totient : ℕ) : ℝ)) *
          (1 + ∑ p : {p : ℕ // p ∈ S}, 1 / (((p : ℕ) : ℝ) - 2)) := by ring
    _ = _ := by
      have hsum :
          (∑ p : {p : ℕ // p ∈ S}, 1 / (((p : ℕ) : ℝ) - 2)) =
            ∑ p ∈ S, 1 / ((p : ℝ) - 2) :=
        Finset.sum_coe_sort S (fun p : ℕ => 1 / ((p : ℝ) - 2))
      rw [hratio, hsum]

/-- The exact manuscript robust-density union bound, now applied to the actual
`robustResidues` definition with its true Euler-totient denominator. -/
theorem actual_robust_density_deficit_le_manuscript_majorant (S : Finset ℕ)
    (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ max J 3 < p)
    (hb : ∀ p ∈ S, Nat.Coprime (b p) p) :
    1 - ((robustResidues S b J).card : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) ≤
      (J : ℝ) * (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) *
        (1 + ∑ p ∈ S, 1 / ((p : ℝ) - 2)) := by
  have hJ : ∀ p ∈ S, p.Prime ∧ J < p := by
    intro p hp
    exact ⟨(hsupport p hp).1,
      lt_of_le_of_lt (le_max_left J 3) (hsupport p hp).2⟩
  have hthree : ∀ p ∈ S, p.Prime ∧ 3 < p := by
    intro p hp
    exact ⟨(hsupport p hp).1,
      lt_of_le_of_lt (le_max_right J 3) (hsupport p hp).2⟩
  calc
    1 - ((robustResidues S b J).card : ℝ) /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ)
      ≤ (J : ℝ) *
          (((∏ p ∈ S, (p - 2)) +
            ∑ p : {p : ℕ // p ∈ S},
              ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2) : ℕ) : ℝ) /
            (((∏ p ∈ S, p).totient : ℕ) : ℝ) :=
          actual_robust_density_deficit_le S b J hJ hb
    _ = (J : ℝ) *
          ((((∏ p ∈ S, (p - 2)) +
            ∑ p : {p : ℕ // p ∈ S},
              ∏ q ∈ (Finset.univ.erase p), ((q : ℕ) - 2) : ℕ) : ℝ) /
            (((∏ p ∈ S, p).totient : ℕ) : ℝ)) := by ring
    _ = _ := by
      rw [prime_crt_correction_normalized_identity S hthree]
      ring

/-- The manuscript's actual robust-residue density can be made arbitrarily
close to one. This closes the finite CRT transport, union bound, totient
normalization, and prime-support selection simultaneously, with no Mertens
estimate and no unproved analytic assumption. -/
theorem exists_support_actual_robust_density_gt (J : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ max J 3 < p) ∧
      1 - ε < ((robustResidues S (fun _ => 1) J).card : ℝ) /
        (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
  obtain ⟨S, hsupport, hmajorant⟩ := exists_prime_support_robust_majorant_lt J hε
  refine ⟨S, hsupport, ?_⟩
  have hb : ∀ p ∈ S, Nat.Coprime ((fun _ : ℕ => 1) p) p := by
    intro p _
    simp
  have hdensity := actual_robust_density_deficit_le_manuscript_majorant
    S (fun _ => 1) J hsupport hb
  linarith

end Erdos689

#print axioms Erdos689.natural_unit_residues_card
#print axioms Erdos689.robust_residues_subset_natural_units
#print axioms Erdos689.mem_nonrobust_unit_residues_iff
#print axioms Erdos689.robust_residues_complement_card_add
#print axioms Erdos689.robust_residues_card_ge_totient_sub
#print axioms Erdos689.natural_unit_subtype_card
#print axioms Erdos689.prime_support_modEq_product
#print axioms Erdos689.prime_support_residue_coordinate_injective
#print axioms Erdos689.prime_support_unit_coordinate_mem
#print axioms Erdos689.prime_coordinate_hit_unique
#print axioms Erdos689.prime_coordinate_hit_exists_unique
#print axioms Erdos689.designated_prime_hit_spec
#print axioms Erdos689.actual_prime_hit_iff_coordinate_eq
#print axioms Erdos689.prime_offset_coprime
#print axioms Erdos689.switched_hits_eq_designated_coordinate_count
#print axioms Erdos689.actual_nonrobust_unit_residues_card_le
#print axioms Erdos689.actual_robust_residues_card_lower
#print axioms Erdos689.actual_robust_density_deficit_le
#print axioms Erdos689.real_zero_and_one_hit_product_identity
#print axioms Erdos689.prime_crt_correction_normalized_identity
#print axioms Erdos689.actual_robust_density_deficit_le_manuscript_majorant
#print axioms Erdos689.exists_support_actual_robust_density_gt
