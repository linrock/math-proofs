module

public import ProgressionArithmetic2
public import Mathlib


@[expose] public section

/-!
# Covered residue sets and Chinese Remainder Theorem fiber splitting

Defines the covered subset `coveredSet D r N` inside `ZMod N` and shows that
when passing from $Q$ to $Q p^\gamma$ with $p \nmid Q$, every covered residue
maps under `ZMod.chineseRemainder` into either the old covered cylinder over
`ZMod Q` or the union of late divisor/exponent fibers `lateFiber Q p γ r`.
-/

open scoped BigOperators

namespace Erdos2.CoveringModel

noncomputable def coveredSet (D : Finset ℕ) (r : ℕ → ℤ) (N : ℕ) [NeZero N] :
    Finset (ZMod N) := by
  classical
  exact D.attach.biUnion fun d => if hd : d.val ∣ N then
    Finset.univ.filter (fun z : ZMod N =>
      ZMod.castHom hd (ZMod d.val) z = (r d.val : ZMod d.val)) else ∅

theorem mem_coveredSet (D : Finset ℕ) (r : ℕ → ℤ) (N : ℕ) [NeZero N]
    (z : ZMod N) :
    z ∈ coveredSet D r N ↔ ∃ d ∈ D, ∃ hd : d ∣ N,
      ZMod.castHom hd (ZMod d) z = (r d : ZMod d) := by
  classical
  constructor
  · intro hz
    obtain ⟨d, _, hdz⟩ := Finset.mem_biUnion.mp hz
    by_cases hd : d.val ∣ N
    · have hclass : ZMod.castHom hd (ZMod d.val) z = (r d.val : ZMod d.val) := by
        simpa only [hd, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and] using hdz
      exact ⟨d.val, d.property, hd, hclass⟩
    · simp [hd] at hdz
  · rintro ⟨d, hd, hdiv, hclass⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨d, hd⟩, by simp, ?_⟩
    simpa only [hdiv, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and] using hclass

abbrev LateIndex (Q γ : ℕ) := Q.divisors × Fin γ

noncomputable def oldClass (Q p γ : ℕ) [NeZero Q] (r : ℕ → ℤ)
    (i : LateIndex Q γ) : Finset (ZMod Q) := by
  classical
  exact Finset.univ.filter (fun x : ZMod Q =>
    ZMod.castHom (Nat.dvd_of_mem_divisors i.1.property) (ZMod i.1.val) x =
      (r (i.1.val * p ^ (i.2.val + 1)) : ZMod i.1.val))

noncomputable def newClass (Q p γ : ℕ) [NeZero p] (r : ℕ → ℤ)
    (i : LateIndex Q γ) : Finset (ZMod (p ^ γ)) := by
  classical
  exact Finset.univ.filter (fun y : ZMod (p ^ γ) =>
    ZMod.castHom (Nat.pow_dvd_pow p (Nat.succ_le_of_lt i.2.isLt))
      (ZMod (p ^ (i.2.val + 1))) y =
      (r (i.1.val * p ^ (i.2.val + 1)) : ZMod (p ^ (i.2.val + 1))))

noncomputable def lateFiber (Q p γ : ℕ) [NeZero Q] [NeZero p] (r : ℕ → ℤ)
    (x : ZMod Q) : Finset (ZMod (p ^ γ)) := by
  classical
  exact Finset.univ.biUnion fun i : LateIndex Q γ =>
    if x ∈ oldClass Q p γ r i then newClass Q p γ r i else ∅

/-- Every actual covered residue belongs to the old covered cylinder or the
full late divisor/exponent union after the CRT step. Exponent zero is retained. -/
theorem coveredSet_crt_step (D : Finset ℕ) (r : ℕ → ℤ)
    {Q p γ : ℕ} [NeZero Q] [NeZero p] (hp : p.Prime) (hpQ : ¬p ∣ Q)
    (z : ZMod (Q * p ^ γ)) (hz : z ∈ coveredSet D r (Q * p ^ γ)) :
    ZMod.chineseRemainder ((hp.coprime_iff_not_dvd.mpr hpQ).symm.pow_right γ) z ∈
      (coveredSet D r Q).product Finset.univ ∪
      Finset.univ.filter (fun xy : ZMod Q × ZMod (p ^ γ) =>
        xy.2 ∈ lateFiber Q p γ r xy.1) := by
  classical
  let hc : Q.Coprime (p ^ γ) := (hp.coprime_iff_not_dvd.mpr hpQ).symm.pow_right γ
  change ZMod.chineseRemainder hc z ∈ _
  obtain ⟨d, hdD, hd, hclass⟩ := (mem_coveredSet D r (Q * p ^ γ) z).mp hz
  obtain ⟨m, j, hmQ, hj, heq, hpm⟩ :=
    Erdos2.ProgressionArithmetic.divisor_decomposition hp hpQ hd
  subst d
  have hpow : p ^ j ∣ p ^ γ := Nat.pow_dvd_pow p hj
  have hcm : m.Coprime (p ^ j) :=
    (hp.coprime_iff_not_dvd.mpr hpm).symm.pow_right j
  have hpair := (Erdos2.ProgressionArithmetic.crt_reduction_pair hc hcm hmQ hpow
    (r (m * p ^ j)) z).mp hclass
  by_cases hj0 : j = 0
  · apply Finset.mem_union_left
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    apply (mem_coveredSet D r Q _).mpr
    refine ⟨m, by simpa [hj0] using hdD, hmQ, ?_⟩
    simpa [hj0] using hpair.1
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases j with
    | zero => exact (hj0 rfl).elim
    | succ e =>
      let k : Fin γ := ⟨e, by omega⟩
      let i : LateIndex Q γ :=
        (⟨m, Nat.mem_divisors.mpr ⟨hmQ, NeZero.ne Q⟩⟩, k)
      have hx : (ZMod.chineseRemainder hc z).1 ∈ oldClass Q p γ r i := by
        unfold oldClass
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change ZMod.castHom hmQ (ZMod m) (ZMod.chineseRemainder hc z).1 =
          (r (m * p ^ (e + 1)) : ZMod m)
        exact hpair.1
      have hy : (ZMod.chineseRemainder hc z).2 ∈ newClass Q p γ r i := by
        unfold newClass
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change ZMod.castHom (Nat.pow_dvd_pow p (by omega : e + 1 ≤ γ))
          (ZMod (p ^ (e + 1))) (ZMod.chineseRemainder hc z).2 =
          (r (m * p ^ (e + 1)) : ZMod (p ^ (e + 1)))
        exact hpair.2
      unfold lateFiber
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simp only [hx, ↓reduceIte]
      exact hy

end Erdos2.CoveringModel
