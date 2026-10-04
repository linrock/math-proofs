module

public import Mathlib


@[expose] public section

/-!
# Congruence geometry and Chinese Remainder Theorem projections

Establishes fiber cardinalities for canonical reductions $\mathbb{Z}/N\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z}$,
shows that intersections of two congruence classes modulo $m_1, m_2 \mid N$ are
either empty or a single congruence class modulo $\operatorname{lcm}(m_1, m_2)$,
and records the Chinese Remainder Theorem product projections.
-/

open scoped BigOperators

namespace Erdos2.CongruenceGeometry

theorem reduction_fiber_card {N m : ℕ} [NeZero N] [NeZero m]
    (h : m ∣ N) (a : ZMod m) :
    (Finset.univ.filter (fun x : ZMod N => ZMod.castHom h (ZMod m) x = a)).card =
      N / m := by
  classical
  let f : ZMod N →+ ZMod m := (ZMod.castHom h (ZMod m)).toAddMonoidHom
  have hs : Function.Surjective f := ZMod.castHom_surjective h
  have hq : Nat.card (ZMod N ⧸ f.ker) = m := by
    rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective f hs).toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hk : N = m * Nat.card f.ker := by
    calc
      N = Nat.card (ZMod N) := by simp [Nat.card_eq_fintype_card]
      _ = Nat.card (ZMod N ⧸ f.ker) * Nat.card f.ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
      _ = m * Nat.card f.ker := congrArg (fun t => t * Nat.card f.ker) hq
  have he : {x : ZMod N // f x = a} ≃ f.ker :=
    (Equiv.subtypeEquivRight (fun _ => by simp)).trans
      (AddMonoidHom.fiberEquivKerOfSurjective hs a)
  have hc : Nat.card {x : ZMod N // f x = a} = Nat.card f.ker :=
    Nat.card_congr he
  rw [← Fintype.card_subtype (fun x : ZMod N => ZMod.castHom h (ZMod m) x = a)]
  change Fintype.card {x : ZMod N // f x = a} = N / m
  rw [← Nat.card_eq_fintype_card, hc]
  calc
    Nat.card f.ker = (m * Nat.card f.ker) / m :=
      (Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
    _ = N / m := congrArg (fun t => t / m) hk.symm

theorem reduction_uniform_fraction {N m : ℕ} [NeZero N] [NeZero m]
    (h : m ∣ N) (a : ZMod m) :
    ((Finset.univ.filter (fun x : ZMod N => ZMod.castHom h (ZMod m) x = a)).card : ℝ)
      / (N : ℝ) = 1 / (m : ℝ) := by
  have hc := reduction_fiber_card h a
  have hmul :
      (Finset.univ.filter (fun x : ZMod N => ZMod.castHom h (ZMod m) x = a)).card * m = N := by
    rw [hc, Nat.div_mul_cancel h]
  have hmulr :
      ((Finset.univ.filter (fun x : ZMod N => ZMod.castHom h (ZMod m) x = a)).card : ℝ)
        * (m : ℝ) = (N : ℝ) := by exact_mod_cast hmul
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  apply (div_eq_div_iff hn hm).2
  simpa using hmulr

theorem modEq_pair_iff_lcm (m₁ m₂ : ℕ) (x z : ℤ) :
    (Int.ModEq (m₁ : ℤ) x z ∧ Int.ModEq (m₂ : ℤ) x z) ↔
      Int.ModEq (Nat.lcm m₁ m₂ : ℤ) x z := by
  simpa only [Int.lcm_def, Int.natAbs_natCast] using
    (Int.modEq_and_modEq_iff_modEq_lcm (a := x) (b := z)
      (m := (m₁ : ℤ)) (n := (m₂ : ℤ)))

theorem reduction_pair_eq_iff_lcm {N m₁ m₂ : ℕ}
    (h₁ : m₁ ∣ N) (h₂ : m₂ ∣ N) (x z : ZMod N) :
    (ZMod.castHom h₁ (ZMod m₁) x = ZMod.castHom h₁ (ZMod m₁) z ∧
      ZMod.castHom h₂ (ZMod m₂) x = ZMod.castHom h₂ (ZMod m₂) z) ↔
    ZMod.castHom (Nat.lcm_dvd h₁ h₂) (ZMod (Nat.lcm m₁ m₂)) x =
      ZMod.castHom (Nat.lcm_dvd h₁ h₂) (ZMod (Nat.lcm m₁ m₂)) z := by
  obtain ⟨u, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨v, rfl⟩ := ZMod.intCast_surjective z
  simpa only [map_intCast, ZMod.intCast_eq_intCast_iff] using
    (modEq_pair_iff_lcm m₁ m₂ u v)

theorem residue_intersection_eq_of_mem {N m₁ m₂ : ℕ}
    (h₁ : m₁ ∣ N) (h₂ : m₂ ∣ N) (a₁ : ZMod m₁) (a₂ : ZMod m₂)
    (z : ZMod N) (hz₁ : ZMod.castHom h₁ (ZMod m₁) z = a₁)
    (hz₂ : ZMod.castHom h₂ (ZMod m₂) z = a₂) :
    {x : ZMod N | ZMod.castHom h₁ (ZMod m₁) x = a₁ ∧
      ZMod.castHom h₂ (ZMod m₂) x = a₂} =
    {x : ZMod N | ZMod.castHom (Nat.lcm_dvd h₁ h₂)
      (ZMod (Nat.lcm m₁ m₂)) x =
      ZMod.castHom (Nat.lcm_dvd h₁ h₂) (ZMod (Nat.lcm m₁ m₂)) z} := by
  ext x
  change (_ ∧ _) ↔ _
  rw [← hz₁, ← hz₂]
  exact reduction_pair_eq_iff_lcm h₁ h₂ x z

theorem integer_residue_intersection_eq_of_mem (m₁ m₂ : ℕ)
    (a₁ a₂ z : ℤ) (hz₁ : Int.ModEq (m₁ : ℤ) a₁ z)
    (hz₂ : Int.ModEq (m₂ : ℤ) a₂ z) :
    {x : ℤ | Int.ModEq (m₁ : ℤ) a₁ x ∧ Int.ModEq (m₂ : ℤ) a₂ x} =
      {x : ℤ | Int.ModEq (Nat.lcm m₁ m₂ : ℤ) z x} := by
  ext x
  change (_ ∧ _) ↔ _
  constructor
  · rintro ⟨hx₁, hx₂⟩
    exact (modEq_pair_iff_lcm m₁ m₂ z x).mp
      ⟨hz₁.symm.trans hx₁, hz₂.symm.trans hx₂⟩
  · intro hx
    obtain ⟨hx₁, hx₂⟩ := (modEq_pair_iff_lcm m₁ m₂ z x).mpr hx
    exact ⟨hz₁.trans hx₁, hz₂.trans hx₂⟩

theorem residue_intersection_empty_or_lcm {N m₁ m₂ : ℕ}
    (h₁ : m₁ ∣ N) (h₂ : m₂ ∣ N) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    {x : ZMod N | ZMod.castHom h₁ (ZMod m₁) x = a₁ ∧
      ZMod.castHom h₂ (ZMod m₂) x = a₂} = ∅ ∨
    ∃ a : ZMod (Nat.lcm m₁ m₂),
      {x : ZMod N | ZMod.castHom h₁ (ZMod m₁) x = a₁ ∧
        ZMod.castHom h₂ (ZMod m₂) x = a₂} =
      {x : ZMod N | ZMod.castHom (Nat.lcm_dvd h₁ h₂)
        (ZMod (Nat.lcm m₁ m₂)) x = a} := by
  classical
  by_cases h : ∃ z : ZMod N,
      ZMod.castHom h₁ (ZMod m₁) z = a₁ ∧
      ZMod.castHom h₂ (ZMod m₂) z = a₂
  · obtain ⟨z, hz₁, hz₂⟩ := h
    exact Or.inr ⟨ZMod.castHom (Nat.lcm_dvd h₁ h₂)
      (ZMod (Nat.lcm m₁ m₂)) z,
      residue_intersection_eq_of_mem h₁ h₂ a₁ a₂ z hz₁ hz₂⟩
  · left
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨x, hx⟩

theorem weighted_residue_intersection_le {N m₁ m₂ : ℕ} [NeZero N]
    (h₁ : m₁ ∣ N) (h₂ : m₂ ∣ N) (a₁ : ZMod m₁) (a₂ : ZMod m₂)
    (w : ZMod N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a : ZMod (Nat.lcm m₁ m₂),
      (∑ x ∈ Finset.univ.filter (fun x : ZMod N =>
        ZMod.castHom (Nat.lcm_dvd h₁ h₂) (ZMod (Nat.lcm m₁ m₂)) x = a), w x) ≤ B) :
    (∑ x ∈ Finset.univ.filter (fun x : ZMod N =>
      ZMod.castHom h₁ (ZMod m₁) x = a₁ ∧
      ZMod.castHom h₂ (ZMod m₂) x = a₂), w x) ≤ B := by
  classical
  obtain hempty | ⟨a, ha⟩ := residue_intersection_empty_or_lcm h₁ h₂ a₁ a₂
  · have hf : Finset.univ.filter (fun x : ZMod N =>
        ZMod.castHom h₁ (ZMod m₁) x = a₁ ∧
        ZMod.castHom h₂ (ZMod m₂) x = a₂) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
      exact Set.ext_iff.mp hempty x
    rw [hf, Finset.sum_empty]
    exact hB
  · have hf : Finset.univ.filter (fun x : ZMod N =>
        ZMod.castHom h₁ (ZMod m₁) x = a₁ ∧
        ZMod.castHom h₂ (ZMod m₂) x = a₂) =
        Finset.univ.filter (fun x : ZMod N =>
          ZMod.castHom (Nat.lcm_dvd h₁ h₂) (ZMod (Nat.lcm m₁ m₂)) x = a) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Set.ext_iff.mp ha x
    rw [hf]
    exact hbound a

theorem crt_product_projection {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (fun i j => Nat.Coprime (a i) (a j)))
    (x : ZMod (∏ i, a i)) (i : ι) :
    ZMod.prodEquivPi a coprime x i =
      ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)) x :=
  ZMod.prodEquivPi_apply a coprime x i

theorem crt_primePower_equiv (N : ℕ) (hN : N ≠ 0) :
    Nonempty (ZMod N ≃+* ∀ p : N.primeFactors, ZMod ((p : ℕ) ^ N.factorization p)) :=
  ⟨ZMod.equivPi N hN⟩

end Erdos2.CongruenceGeometry
