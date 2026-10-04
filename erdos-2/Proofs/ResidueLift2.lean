module

public import Mathlib


@[expose] public section

/-!
# Signed-integer and finite-residue coverage equivalence

Proves that a family of congruences $z \equiv r_i \pmod{m_i}$ with $m_i \mid N$
covers all integers $z \in \mathbb{Z}$ if and only if its canonical projections
cover $\mathbb{Z}/N\mathbb{Z}$, and lifts any uncovered residue in `ZMod N` to
an uncovered signed integer $z \in \mathbb{Z}$.
-/

namespace Erdos2.ResidueLift

theorem integer_lift_of_avoiding_reductions {ι : Type*} {N : ℕ}
    (m : ι → ℕ) (r : ι → ℤ) (hdiv : ∀ i, m i ∣ N)
    (x : ZMod N)
    (havoid : ∀ i, ZMod.castHom (hdiv i) (ZMod (m i)) x ≠ (r i : ZMod (m i))) :
    ∃ z : ℤ, ∀ i, ¬Int.ModEq (m i : ℤ) (r i) z := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  refine ⟨z, fun i hi => ?_⟩
  apply havoid i
  simpa only [map_intCast] using
    ((ZMod.intCast_eq_intCast_iff (r i) z (m i)).mpr hi).symm

theorem reduction_cover_of_integer_cover {ι : Type*} {N : ℕ}
    (m : ι → ℕ) (r : ι → ℤ) (hdiv : ∀ i, m i ∣ N)
    (hcover : ∀ z : ℤ, ∃ i, Int.ModEq (m i : ℤ) (r i) z) :
    ∀ x : ZMod N, ∃ i,
      ZMod.castHom (hdiv i) (ZMod (m i)) x = (r i : ZMod (m i)) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨i, hi⟩ := hcover z
  refine ⟨i, ?_⟩
  simpa only [map_intCast] using
    ((ZMod.intCast_eq_intCast_iff (r i) z (m i)).mpr hi).symm

theorem integer_cover_of_reduction_cover {ι : Type*} {N : ℕ}
    (m : ι → ℕ) (r : ι → ℤ) (hdiv : ∀ i, m i ∣ N)
    (hcover : ∀ x : ZMod N, ∃ i,
      ZMod.castHom (hdiv i) (ZMod (m i)) x = (r i : ZMod (m i))) :
    ∀ z : ℤ, ∃ i, Int.ModEq (m i : ℤ) (r i) z := by
  intro z
  obtain ⟨i, hi⟩ := hcover (z : ZMod N)
  refine ⟨i, ?_⟩
  apply (ZMod.intCast_eq_intCast_iff (r i) z (m i)).mp
  simpa only [map_intCast] using hi.symm

theorem integer_cover_iff_reduction_cover {ι : Type*} {N : ℕ}
    (m : ι → ℕ) (r : ι → ℤ) (hdiv : ∀ i, m i ∣ N) :
    (∀ z : ℤ, ∃ i, Int.ModEq (m i : ℤ) (r i) z) ↔
    (∀ x : ZMod N, ∃ i,
      ZMod.castHom (hdiv i) (ZMod (m i)) x = (r i : ZMod (m i))) :=
  ⟨reduction_cover_of_integer_cover m r hdiv,
    integer_cover_of_reduction_cover m r hdiv⟩

end Erdos2.ResidueLift
