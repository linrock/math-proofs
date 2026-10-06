module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Finite residual classification showing that a graph of minimum degree at least
one avoiding `P_4`, `3 K_2`, and `P_3 ⊔ K_2` is a union of stars with a small
vertex cover.
-/

namespace ErdosProblems.PathUpperReduction.ResidualForestStar1105

open SimpleGraph

/-- Ordinary P3 plus a vertex-disjoint ordinary P2 is forbidden. -/
def NoP3AndP2 {V : Type*} (R : SimpleGraph V) : Prop :=
  ∀ p : Fin 5 → V, Function.Injective p →
    R.Adj (p 0) (p 1) → R.Adj (p 1) (p 2) → R.Adj (p 3) (p 4) → False

/-- Three vertex-disjoint ordinary edges are forbidden. -/
def NoThreeP2 {V : Type*} (R : SimpleGraph V) : Prop :=
  ∀ p : Fin 6 → V, Function.Injective p →
    R.Adj (p 0) (p 1) → R.Adj (p 2) (p 3) → R.Adj (p 4) (p 5) → False

/-- Reuse the checked H3 proof's exact ordinary IsPath-to-Copy bridge. -/
theorem false_of_three_edge_chain {V : Type*}
    (R : SimpleGraph V) (hfree : (pathGraph 4).Free R)
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h01 : R.Adj a b) (h12 : R.Adj b c) (h23 : R.Adj c d) : False := by
  classical
  let p : R.Walk a d := .cons h01 (.cons h12 (.cons h23 .nil))
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [p, hab, hac, had, hbc, hbd, hcd]
  have hcopy : pathGraph 4 ⊑ R := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

theorem no_edge_outside_two_edge_path {V : Type*} [DecidableEq V]
    (R : SimpleGraph V) (hforest : NoP3AndP2 R)
    (a b c : V) (hac : a ≠ c) (hab : R.Adj a b) (hbc : R.Adj b c)
    (x y : V) (hx : x ∉ ({a, b, c} : Finset V))
    (hy : y ∉ ({a, b, c} : Finset V)) : ¬ R.Adj x y := by
  classical
  intro hxy
  have habne : a ≠ b := hab.ne
  have hbcne : b ≠ c := hbc.ne
  have hxyne : x ≠ y := hxy.ne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  rcases hx with ⟨hxa, hxb, hxc⟩
  rcases hy with ⟨hya, hyb, hyc⟩
  let p : Fin 5 → V := ![a, b, c, x, y]
  have hinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [p, habne, habne.symm, hac, hac.symm, hbcne, hbcne.symm,
        hxa, Ne.symm hxa, hxb, Ne.symm hxb, hxc, Ne.symm hxc,
        hya, Ne.symm hya, hyb, Ne.symm hyb, hyc, Ne.symm hyc,
        hxyne, hxyne.symm] at hij ⊢
  exact hforest p hinj (by simpa [p] using hab)
    (by simpa [p] using hbc) (by simpa [p] using hxy)

theorem exists_two_edge_path {V : Type*} [Fintype V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : 5 ≤ Fintype.card V) (hmin : ∀ x, 1 ≤ R.degree x)
    (hforest : NoThreeP2 R) :
    ∃ a b c : V, a ≠ c ∧ R.Adj a b ∧ R.Adj b c := by
  classical
  by_contra hnone
  have hpartner : ∀ u v w : V, R.Adj u v → R.Adj u w → w = v := by
    intro u v w huv huw
    by_contra hwv
    exact hnone ⟨v, u, w, Ne.symm hwv, huv.symm, huw⟩
  have neighbor (x : V) : ∃ y, R.Adj x y := by
    apply (R.degree_pos_iff_exists_adj x).mp
    have hx := hmin x
    omega
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a : V := Classical.arbitrary V
  obtain ⟨b, hab⟩ := neighbor a
  let T : Finset V := {a, b}
  have hTcard : T.card = 2 := by simp [T, hab.ne]
  have hTsmall : T.card < (Finset.univ : Finset V).card := by
    rw [hTcard, Finset.card_univ]
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hTsmall
  obtain ⟨d, hcd⟩ := neighbor c
  have hd : d ∉ T := by
    intro hd
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hda | hdb
    · rw [hda] at hcd
      have hcb := hpartner a b c hab hcd.symm
      exact hc (by simp [T, hcb])
    · rw [hdb] at hcd
      have hca := hpartner b a c hab.symm hcd.symm
      exact hc (by simp [T, hca])
  simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  rcases hc with ⟨hca, hcb⟩
  rcases hd with ⟨hda, hdb⟩
  have habne : a ≠ b := hab.ne
  have hcdne : c ≠ d := hcd.ne
  let U : Finset V := {a, b, c, d}
  have hUcard : U.card = 4 := by
    simp [U, habne, Ne.symm hca, Ne.symm hda, Ne.symm hcb, Ne.symm hdb, hcdne]
  have hUsmall : U.card < (Finset.univ : Finset V).card := by
    rw [hUcard, Finset.card_univ]
    omega
  obtain ⟨e, _, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hUsmall
  obtain ⟨f, hef⟩ := neighbor e
  have hf : f ∉ U := by
    intro hf
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with hfa | hfb | hfc | hfd
    · rw [hfa] at hef
      have heb := hpartner a b e hab hef.symm
      exact he (by simp [U, heb])
    · rw [hfb] at hef
      have hea := hpartner b a e hab.symm hef.symm
      exact he (by simp [U, hea])
    · rw [hfc] at hef
      have hed := hpartner c d e hcd hef.symm
      exact he (by simp [U, hed])
    · rw [hfd] at hef
      have hec := hpartner d c e hcd.symm hef.symm
      exact he (by simp [U, hec])
  simp only [U, Finset.mem_insert, Finset.mem_singleton, not_or] at he hf
  rcases he with ⟨hea, heb, hec, hed⟩
  rcases hf with ⟨hfa, hfb, hfc, hfd⟩
  have hefne : e ≠ f := hef.ne
  let p : Fin 6 → V := ![a, b, c, d, e, f]
  have hinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [p, habne, habne.symm, hca, Ne.symm hca, hcb, Ne.symm hcb,
        hda, Ne.symm hda, hdb, Ne.symm hdb, hcdne, hcdne.symm,
        hea, Ne.symm hea, heb, Ne.symm heb, hec, Ne.symm hec, hed, Ne.symm hed,
        hfa, Ne.symm hfa, hfb, Ne.symm hfb, hfc, Ne.symm hfc, hfd, Ne.symm hfd,
        hefne, hefne.symm] at hij ⊢
  exact hforest p hinj (by simpa [p] using hab)
    (by simpa [p] using hcd) (by simpa [p] using hef)

/-- At least five ORIGINAL vertices, minimum degree one, ordinary P4 freedom,
and exclusion of the other two three-edge linear forests force a spanning
star. The actual center is derived and its singleton covers every edge. -/
theorem exists_center_of_min_degree_and_no_three_edge_linear_forest
    {V : Type*} [Fintype V] (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : 5 ≤ Fintype.card V) (hmin : ∀ x : V, 1 ≤ R.degree x)
    (hfree : (pathGraph 4).Free R)
    (hP3P2 : NoP3AndP2 R) (h3P2 : NoThreeP2 R) :
    ∃ b : V, (∀ x : V, x ≠ b → R.Adj b x) ∧
      (∀ x : V, x ≠ b → ∀ y : V, y ≠ b → ¬ R.Adj x y) ∧
      R.IsVertexCover ({b} : Set V) := by
  classical
  obtain ⟨a, b, c, hac, hab, hbc⟩ := exists_two_edge_path R hcard hmin h3P2
  let T : Finset V := {a, b, c}
  have hcenter : ∀ x : V, x ≠ b → R.Adj b x := by
    intro x hxb
    by_cases hx : x ∈ T
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hab.symm
      · exact False.elim (hxb rfl)
      · exact hbc
    · have hxpos : 0 < R.degree x := by
        have hm := hmin x
        omega
      obtain ⟨y, hxy⟩ := (R.degree_pos_iff_exists_adj x).mp hxpos
      have hy : y ∈ T := by
        by_contra hy
        exact no_edge_outside_two_edge_path R hP3P2 a b c hac hab hbc
          x y hx hy hxy
      have hxa : x ≠ a := by intro h; exact hx (by simp [T, h])
      have hxc : x ≠ c := by intro h; exact hx (by simp [T, h])
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hya | hyb | hyc
      · subst hya
        exact False.elim (false_of_three_edge_chain R hfree x y b c
          hxa hxb hxc hab.ne hac hbc.ne hxy hab hbc)
      · subst hyb
        exact hxy.symm
      · subst hyc
        exact False.elim (false_of_three_edge_chain R hfree x y b a
          hxc hxb hxa hbc.ne.symm hac.symm hab.ne.symm
          hxy hbc.symm hab.symm)
  have hleaves : ∀ x : V, x ≠ b → ∀ y : V, y ≠ b → ¬ R.Adj x y := by
    intro x hxb y hyb hxy
    let U : Finset V := {b, x, y}
    have hUcard : U.card = 3 := by simp [U, hxb.symm, hyb.symm, hxy.ne]
    have hsmall : U.card < (Finset.univ : Finset V).card := by
      rw [hUcard, Finset.card_univ]
      omega
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
    have hzb : z ≠ b := by intro h; exact hz (by simp [U, h])
    have hzx : z ≠ x := by intro h; exact hz (by simp [U, h])
    have hzy : z ≠ y := by intro h; exact hz (by simp [U, h])
    exact false_of_three_edge_chain R hfree z b x y
      hzb hzx hzy hxb.symm hyb.symm hxy.ne
      (hcenter z hzb).symm (hcenter x hxb) hxy
  refine ⟨b, hcenter, hleaves, ?_⟩
  intro x y hxy
  by_cases hx : x = b
  · exact Or.inl (by simpa only [Set.mem_singleton_iff] using hx)
  by_cases hy : y = b
  · exact Or.inr (by simpa only [Set.mem_singleton_iff] using hy)
  exact False.elim (hleaves x hx y hy hxy)

end ErdosProblems.PathUpperReduction.ResidualForestStar1105
