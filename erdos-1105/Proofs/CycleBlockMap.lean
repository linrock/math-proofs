module

public import Mathlib

@[expose] public section

/-!
Consecutive vertex blocks for the ordered-block cycle coloring. The target
block index is allowed one extra, potentially empty, last value so that the
division map is total for every `n` and positive block size `m`.
-/

namespace ErdosProblems.AntiRamseyCycleBlockCount

/-- Consecutive blocks of nominal size `m`, indexed by vertex division. -/
def consecutiveBlockMap (m n : ℕ) : Fin n → Fin (n / m + 1) :=
  fun x => ⟨x.val / m, Nat.lt_succ_of_le
    (Nat.div_le_div_right (Nat.le_of_lt x.isLt))⟩

@[simp] theorem consecutiveBlockMap_val (m n : ℕ) (x : Fin n) :
    (consecutiveBlockMap m n x).val = x.val / m := rfl

/-- Every fiber of the consecutive-block map has at most `m` vertices.
The residue modulo `m` injects each fiber into `Fin m`. -/
theorem consecutiveBlockMap_fiber_card_le (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m + 1)) :
    (Finset.univ.filter (fun x : Fin n => consecutiveBlockMap m n x = b)).card ≤ m := by
  classical
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun x : Fin n => consecutiveBlockMap m n x = b)
  let f : S → Fin m := fun x => ⟨x.val.val % m, Nat.mod_lt _ hm⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    have hx : consecutiveBlockMap m n x.val = b :=
      (Finset.mem_filter.mp x.property).2
    have hy : consecutiveBlockMap m n y.val = b :=
      (Finset.mem_filter.mp y.property).2
    have hquot : x.val.val / m = y.val.val / m := by
      simpa only [consecutiveBlockMap_val] using
        congrArg Fin.val (hx.trans hy.symm)
    have hmod : x.val.val % m = y.val.val % m := congrArg Fin.val hxy
    have hdecompx := Nat.mod_add_div x.val.val m
    have hdecompy := Nat.mod_add_div y.val.val m
    rw [hmod, hquot] at hdecompx
    omega
  have hcard : Fintype.card S ≤ Fintype.card (Fin m) :=
    Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

/-- With `m = k - 1`, every block is strictly smaller than a `k`-cycle. -/
theorem cycleBlockMap_small_fibers (k n : ℕ) (hk : 3 ≤ k) :
    ∀ b : Fin (n / (k - 1) + 1),
      (Finset.univ.filter
        (fun x : Fin n => consecutiveBlockMap (k - 1) n x = b)).card < k := by
  intro b
  have hm : 0 < k - 1 := by omega
  have hcard := consecutiveBlockMap_fiber_card_le (k - 1) n hm b
  omega

end ErdosProblems.AntiRamseyCycleBlockCount
