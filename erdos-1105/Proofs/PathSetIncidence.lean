module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-!
For a path with `m` consecutive-index edges, each selected vertex meets at
most two edges. This is the combinatorial obstruction in Yuan's fixed-set
lower coloring for rainbow paths.
-/

namespace ErdosProblems.PathSetLower

/-- Indices of consecutive edges with at least one endpoint in `S`. -/
def pathTouched (m : ℕ) (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i.castSucc ∈ S ∨ i.succ ∈ S)

/-- Indices of consecutive edges with both endpoints outside `S`. -/
def pathAvoiding (m : ℕ) (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ¬ (i.castSucc ∈ S ∨ i.succ ∈ S))

/-- At most two path edges touch each selected vertex. -/
theorem pathTouched_card_le (m : ℕ) (S : Finset (Fin (m + 1))) :
    (pathTouched m S).card ≤ 2 * S.card := by
  classical
  let L : Finset (Fin m) := Finset.univ.filter (fun i => i.castSucc ∈ S)
  let R : Finset (Fin m) := Finset.univ.filter (fun i => i.succ ∈ S)
  have hL : L.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (f := Fin.castSucc)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact (Fin.castSucc_injective m).injOn
  have hR : R.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (f := Fin.succ)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact (Fin.succ_injective m).injOn
  have hEq : pathTouched m S = L ∪ R := by
    ext i
    simp [pathTouched, L, R]
  calc
    (pathTouched m S).card = (L ∪ R).card := by rw [hEq]
    _ ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ S.card + S.card := Nat.add_le_add hL hR
    _ = 2 * S.card := by omega

/-- More than `ε` path edges avoid `S` once `S` is small enough. -/
theorem pathAvoiding_card_gt (m t ε : ℕ) (S : Finset (Fin (m + 1)))
    (hS : S.card ≤ t) (hm : 2 * t + ε < m) :
    ε < (pathAvoiding m S).card := by
  classical
  have hsum : (pathTouched m S).card + (pathAvoiding m S).card = m := by
    simpa [pathTouched, pathAvoiding] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin m => i.castSucc ∈ S ∨ i.succ ∈ S))
  have htouch := pathTouched_card_le m S
  omega

/-- Any coloring of the avoiding edges with only `ε` labels repeats a color. -/
theorem pathAvoiding_repeated_color (m t ε : ℕ) (S : Finset (Fin (m + 1)))
    (c : Fin m → Fin ε) (hS : S.card ≤ t) (hm : 2 * t + ε < m) :
    ∃ i ∈ pathAvoiding m S, ∃ j ∈ pathAvoiding m S,
      i ≠ j ∧ c i = c j := by
  classical
  have hcard := pathAvoiding_card_gt m t ε S hS hm
  by_contra hn
  have hinj : Set.InjOn c (pathAvoiding m S : Set (Fin m)) := by
    intro i hi j hj hij
    by_contra hne
    exact hn ⟨i, hi, j, hj, hne, hij⟩
  have hbound : (pathAvoiding m S).card ≤ ε := by
    have hmap : Set.MapsTo c (pathAvoiding m S : Finset (Fin m))
        (Finset.univ : Finset (Fin ε)) := by
      intro i hi
      exact Finset.mem_univ _
    have h := Finset.card_le_card_of_injOn c
      hmap hinj
    simpa using h
  omega

end ErdosProblems.PathSetLower
