module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

/-! exact two-skip extraction. No path, coloring or Copy premise. -/

namespace ErdosProblems.AntiRamseyCycleTwoSpliceSkipExtraction

open SimpleGraph

noncomputable instance graph_neighborSet_fintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Fintype (G.neighborSet v) := Fintype.ofFinite _

/-- Exact shifted intersection extraction for the final partial reversal.
The two internal degrees are on the literal castSucc/succ tail images. -/
theorem exists_two_splice_skips {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (_hm : 2 ≤ m) (G : SimpleGraph V)
    (R : Fin (m + 3) → V) (hR : Function.Injective R)
    (hleft : ¬ G.Adj (R 0) (R ⟨m + 1, by omega⟩))
    (hright : ¬ G.Adj (R ⟨1, by omega⟩) (R (Fin.last (m + 2))))
    (hsum : m + 2 ≤
      (G.neighborFinset (R 0) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.castSucc i))).card +
      (G.neighborFinset (R ⟨1, by omega⟩) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.succ i))).card) :
    ∃ a : Fin (m + 3), ∃ _ha2 : 2 ≤ a.val, ∃ ham : a.val ≤ m,
      G.Adj (R 0) (R a) ∧
      G.Adj (R ⟨1, by omega⟩) (R ⟨a.val + 1, by omega⟩) := by
  classical
  let p : Fin (m + 2) → V := fun i => R (Fin.castSucc i)
  let q : Fin (m + 2) → V := fun i => R (Fin.succ i)
  let P : Finset V := Finset.univ.image p
  let Q : Finset V := Finset.univ.image q
  let A : Finset (Fin (m + 2)) := Finset.univ.filter (fun i => G.Adj (R 0) (p i))
  let B : Finset (Fin (m + 2)) :=
    Finset.univ.filter (fun i => G.Adj (R ⟨1, by omega⟩) (q i))
  have hp : Function.Injective p := by
    intro i j h
    exact Fin.castSucc_inj.mp (hR h)
  have hq : Function.Injective q := by
    intro i j h
    exact Fin.succ_inj.mp (hR h)
  have hAimage : A.image p = G.neighborFinset (R 0) ∩ P := by
    calc
      A.image p = P.filter (G.Adj (R 0)) := by
        simpa only [A, P] using
          (Finset.filter_image (s := Finset.univ) (f := p) (p := G.Adj (R 0))).symm
      _ = _ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_comm
  have hBimage : B.image q = G.neighborFinset (R ⟨1, by omega⟩) ∩ Q := by
    calc
      B.image q = Q.filter (G.Adj (R ⟨1, by omega⟩)) := by
        simpa only [B, Q] using
          (Finset.filter_image (s := Finset.univ) (f := q)
            (p := G.Adj (R ⟨1, by omega⟩))).symm
      _ = _ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_comm
  have hAcard : (G.neighborFinset (R 0) ∩ P).card = A.card := by
    rw [← hAimage]
    exact Finset.card_image_of_injective A hp
  have hBcard : (G.neighborFinset (R ⟨1, by omega⟩) ∩ Q).card = B.card := by
    rw [← hBimage]
    exact Finset.card_image_of_injective B hq
  have hABsum : m + 2 ≤ A.card + B.card := by
    change m + 2 ≤ (G.neighborFinset (R 0) ∩ P).card +
      (G.neighborFinset (R ⟨1, by omega⟩) ∩ Q).card at hsum
    rw [hAcard, hBcard] at hsum
    exact hsum
  have hAbounds : ∀ j : Fin (m + 2), j ∈ A → 1 ≤ j.val ∧ j.val ≤ m := by
    intro j hj
    have hadj : G.Adj (R 0) (R (Fin.castSucc j)) :=
      (Finset.mem_filter.mp hj).2
    have hj0 : j.val ≠ 0 := by
      intro heq
      have hidx : Fin.castSucc j = (0 : Fin (m + 3)) := Fin.ext heq
      rw [hidx] at hadj
      exact G.irrefl hadj
    have hjlast : j.val ≠ m + 1 := by
      intro heq
      have hidx : Fin.castSucc j = (⟨m + 1, by omega⟩ : Fin (m + 3)) := Fin.ext heq
      apply hleft
      simpa only [hidx] using hadj
    have hjlt := j.isLt
    omega
  have hBbounds : ∀ j : Fin (m + 2), j ∈ B → 1 ≤ j.val ∧ j.val ≤ m := by
    intro j hj
    have hadj : G.Adj (R ⟨1, by omega⟩) (R (Fin.succ j)) :=
      (Finset.mem_filter.mp hj).2
    have hj0 : j.val ≠ 0 := by
      intro heq
      have hidx : Fin.succ j = (⟨1, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        change j.val + 1 = 1
        omega
      rw [hidx] at hadj
      exact G.irrefl hadj
    have hjlast : j.val ≠ m + 1 := by
      intro heq
      have hidx : Fin.succ j = Fin.last (m + 2) := by
        apply Fin.ext
        change j.val + 1 = m + 2
        omega
      apply hright
      simpa only [hidx] using hadj
    have hjlt := j.isLt
    omega
  let S : Finset (Fin (m + 3)) := A.image Fin.succ
  let T : Finset (Fin (m + 3)) := B.image Fin.succ
  let u : Fin m → Fin (m + 3) := fun i => ⟨i.val + 2, by have hi := i.isLt; omega⟩
  let U : Finset (Fin (m + 3)) := Finset.univ.image u
  have hsucc : Function.Injective (Fin.succ : Fin (m + 2) → Fin (m + 3)) := by
    intro i j h
    exact Fin.succ_inj.mp h
  have hu : Function.Injective u := by
    intro i j h
    have hv : i.val + 2 = j.val + 2 := congrArg Fin.val h
    apply Fin.ext
    omega
  have hScard : S.card = A.card := Finset.card_image_of_injective A hsucc
  have hTcard : T.card = B.card := Finset.card_image_of_injective B hsucc
  have hUcard : U.card = m := by
    change (Finset.univ.image u).card = m
    rw [Finset.card_image_of_injective Finset.univ hu]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hSU : S ⊆ U := by
    intro b hb
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
    have hbounds := hAbounds j hj
    let i : Fin m := ⟨j.val - 1, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hjb]
    apply Fin.ext
    change (j.val - 1) + 2 = j.val + 1
    omega
  have hTU : T ⊆ U := by
    intro b hb
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
    have hbounds := hBbounds j hj
    let i : Fin m := ⟨j.val - 1, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hjb]
    apply Fin.ext
    change (j.val - 1) + 2 = j.val + 1
    omega
  have hUnion : (S ∪ T).card ≤ m := by
    have hbound : (S ∪ T).card ≤ U.card := by
      apply Finset.card_le_card
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hSU hb
      · exact hTU hb
    exact hbound.trans_eq hUcard
  have hSTsum : m + 2 ≤ S.card + T.card := by
    rw [hScard, hTcard]
    exact hABsum
  have hInter : 1 < (S ∩ T).card := by
    have hidentity := Finset.card_union_add_card_inter S T
    omega
  obtain ⟨b, hb, hbne⟩ := Finset.exists_mem_ne hInter (⟨2, by omega⟩ : Fin (m + 3))
  obtain ⟨j, hjA, hjb⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
  obtain ⟨l, hlB, hlb⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).2
  have hjl : j = l := hsucc (hjb.trans hlb.symm)
  have hjB : j ∈ B := hjl.symm ▸ hlB
  have hbounds := hAbounds j hjA
  have hjone : j.val ≠ 1 := by
    intro heq
    apply hbne
    calc
      b = Fin.succ j := hjb.symm
      _ = (⟨2, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        change j.val + 1 = 2
        omega
  let a : Fin (m + 3) := Fin.castSucc j
  have ha2 : 2 ≤ a.val := by
    change 2 ≤ j.val
    omega
  have ham : a.val ≤ m := hbounds.2
  refine ⟨a, ha2, ham, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hjA).2
  · have hadj : G.Adj (R ⟨1, by omega⟩) (R (Fin.succ j)) :=
      (Finset.mem_filter.mp hjB).2
    have hidx : (⟨a.val + 1, by omega⟩ : Fin (m + 3)) = Fin.succ j := Fin.ext rfl
    simpa only [hidx] using hadj

end ErdosProblems.AntiRamseyCycleTwoSpliceSkipExtraction
