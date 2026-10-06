module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-! A path on at least three vertices has two edges touching any two distinct vertices. -/

namespace ErdosProblems.PathCliqueLower

theorem two_incident_nat {m i j : ℕ}
    (hm : 2 ≤ m) (hi : i < m + 1) (hj : j < m + 1) (hij : i < j) :
    ∃ p q : ℕ, p < m ∧ q < m ∧ p ≠ q ∧
      (i = p ∨ i = p + 1 ∨ j = p ∨ j = p + 1) ∧
      (i = q ∨ i = q + 1 ∨ j = q ∨ j = q + 1) := by
  by_cases hsep : i + 1 < j
  · refine ⟨i, j - 1, by omega, by omega, by omega, ?_, ?_⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  · have hnext : j = i + 1 := by omega
    by_cases hi0 : i = 0
    · refine ⟨0, 1, by omega, by omega, by omega, ?_, ?_⟩
      · exact Or.inl hi0
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · refine ⟨i - 1, i, by omega, by omega, by omega, ?_, ?_⟩
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inl rfl

/-- Two distinct vertices of a path of order `m + 1`, with `m ≥ 2`, touch at
least two different consecutive-index edges. -/
theorem two_incident_path_edges_succ {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    ∃ p q : Fin m, p ≠ q ∧
      (i = p.castSucc ∨ i = p.succ ∨ j = p.castSucc ∨ j = p.succ) ∧
      (i = q.castSucc ∨ i = q.succ ∨ j = q.castSucc ∨ j = q.succ) := by
  have hlift (a b : Fin (m + 1)) (hab : a < b) :
      ∃ p q : Fin m, p ≠ q ∧
        (a = p.castSucc ∨ a = p.succ ∨ b = p.castSucc ∨ b = p.succ) ∧
        (a = q.castSucc ∨ a = q.succ ∨ b = q.castSucc ∨ b = q.succ) := by
    obtain ⟨p, q, hp, hq, hpq, hincp, hincq⟩ :=
      two_incident_nat hm a.isLt b.isLt hab
    refine ⟨⟨p, hp⟩, ⟨q, hq⟩, ?_, ?_, ?_⟩
    · intro he
      have hv := congrArg Fin.val he
      exact hpq hv
    · simpa [Fin.ext_iff] using hincp
    · simpa [Fin.ext_iff] using hincq
  rcases lt_trichotomy i j with h | h | h
  · exact hlift i j h
  · exact False.elim (hij h)
  · obtain ⟨p, q, hpq, hincp, hincq⟩ := hlift j i h
    refine ⟨p, q, hpq, ?_, ?_⟩ <;> tauto

/-- An injective placement of `r + 2` vertices into `Fin n` has at least two
vertices outside the first `r` values. -/
theorem two_vertices_outside_prefix {r n : ℕ}
    (f : Fin (r + 2) → Fin n) (hf : Function.Injective f) :
    ∃ i j : Fin (r + 2), i ≠ j ∧ r ≤ (f i).val ∧ r ≤ (f j).val := by
  classical
  let S : Finset (Fin (r + 2)) := Finset.univ.filter (fun i => (f i).val < r)
  let T : Finset (Fin (r + 2)) := Finset.univ.filter (fun i => ¬ (f i).val < r)
  have hS : S.card ≤ r := by
    let g : S → Fin r := fun i => ⟨(f i.1).val, (Finset.mem_filter.mp i.2).2⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply hf
      apply Fin.ext
      change (⟨(f a.1).val, _⟩ : Fin r) = ⟨(f b.1).val, _⟩ at hab
      exact congrArg (fun t : Fin r => t.val) hab
    simpa using Fintype.card_le_of_injective g hg
  have hsum : S.card + T.card = r + 2 := by
    simpa [S, T] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin (r + 2) => (f i).val < r))
  have hT : 1 < T.card := by omega
  obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hT
  refine ⟨i, j, hij, ?_, ?_⟩
  · exact Nat.le_of_not_gt (Finset.mem_filter.mp hi).2
  · exact Nat.le_of_not_gt (Finset.mem_filter.mp hj).2

end ErdosProblems.PathCliqueLower
