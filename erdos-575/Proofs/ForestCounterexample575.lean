module

/-
Lean 4.35.0-rc2 formalization of the classic bipartite forest counterexample
`F_0 = {K_{1,2}, 2K_2}` to the literal statement of Erdős Problem #575, unified
over the common `CompactnessConjecture.FiniteGraph` and `Erdos575` definitions:
- `cherryGraph` (`K_{1,2}` on `Fin 3`) and `twoMatchingGraph` (`2K_2` on `Fin 4`)
  are both bipartite.
- Any host graph on `Fin n` that is both `K_{1,2}`-free and `2K_2`-free has at
  most `1` edge, so `familyExtremal forestFamily n ≤ 1` for all `n`.
- The star graph on `Fin n` is `2K_2`-free with at least `n - 1` edges, so
  `n - 1 ≤ extremalNumber n twoMatchingGraph.graph`.
- The matching graph on `Fin n` is `K_{1,2}`-free with at least `n / 2` edges, so
  `n / 2 ≤ extremalNumber n cherryGraph.graph`.
- Consequently neither member of `forestFamily` controls the family extremal
  number, refuting `IsBipartiteCompactFamily forestFamily` and
  `BipartiteCompactnessStatement`.
-/
public import Erdos575


@[expose] public section

namespace Erdos575.ForestCounterexample

open CompactnessConjecture Erdos575 Filter SimpleGraph
open scoped Classical Topology

/-- The star simple graph on `Fin n` centered at vertex `0` (when `n > 0`). -/
def starSimpleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val = 0 ∨ v.val = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
theorem starSimpleGraph_adj {n : ℕ} {u v : Fin n} :
    (starSimpleGraph n).Adj u v ↔ u ≠ v ∧ (u.val = 0 ∨ v.val = 0) :=
  Iff.rfl

/-- The matching simple graph on `Fin n` pairing `2k` with `2k + 1`. -/
def matchingSimpleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val / 2 = v.val / 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
theorem matchingSimpleGraph_adj {n : ℕ} {u v : Fin n} :
    (matchingSimpleGraph n).Adj u v ↔ u ≠ v ∧ u.val / 2 = v.val / 2 :=
  Iff.rfl

/-- The cherry graph `K_{1,2}` on `Fin 3` with edges `{0,1}` and `{0,2}`. -/
abbrev cherryGraph : FiniteGraph := ⟨3, starSimpleGraph 3⟩

/-- The two-edge matching `2K_2` on `Fin 4` with edges `{0,1}` and `{2,3}`. -/
abbrev twoMatchingGraph : FiniteGraph := ⟨4, matchingSimpleGraph 4⟩

/-- The two-forest family `F_0 = {K_{1,2}, 2K_2}`. -/
noncomputable def forestFamily : Finset FiniteGraph :=
  {cherryGraph, twoMatchingGraph}

/-- Every `starSimpleGraph n` is bipartite (2-colorable). -/
theorem starSimpleGraph_isBipartite (n : ℕ) : (starSimpleGraph n).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v : Fin n => if v.val = 0 then (0 : Fin 2) else 1) ?_⟩
  rintro u v ⟨hne, h0 | h0⟩ hcol <;>
    exact hne (Fin.ext (by split_ifs at hcol <;> omega))

/-- Every `matchingSimpleGraph n` is bipartite (2-colorable by parity). -/
theorem matchingSimpleGraph_isBipartite (n : ℕ) : (matchingSimpleGraph n).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v : Fin n => (⟨v.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
  rintro u v ⟨hne, hdiv⟩ hmod
  have : u.val % 2 = v.val % 2 := congrArg Fin.val hmod
  exact hne (Fin.ext (by omega))

/-- `cherryGraph` (`K_{1,2}`) is bipartite. -/
theorem cherryGraph_isBipartite : cherryGraph.graph.IsBipartite :=
  starSimpleGraph_isBipartite 3

/-- `twoMatchingGraph` (`2K_2`) is bipartite. -/
theorem twoMatchingGraph_isBipartite : twoMatchingGraph.graph.IsBipartite :=
  matchingSimpleGraph_isBipartite 4

/-- `forestFamily` is nonempty. -/
theorem forestFamily_nonempty : forestFamily.Nonempty := by
  exact ⟨cherryGraph, by simp [forestFamily]⟩

/-- Every member of `forestFamily` is bipartite. -/
theorem forestFamily_allBipartite :
    ∀ H ∈ forestFamily, H.graph.IsBipartite := by
  simp [forestFamily, starSimpleGraph_isBipartite, matchingSimpleGraph_isBipartite]

/-- `forestFamily` contains a bipartite member. -/
theorem forestFamily_containsBipartiteMember :
    ContainsBipartiteMember forestFamily :=
  ⟨cherryGraph, by simp [forestFamily], cherryGraph_isBipartite⟩

/-- Two incident distinct edges in `host` yield a copy of `cherryGraph`. -/
theorem not_cherry_free_of_adj_adj {n : ℕ} {host : SimpleGraph (Fin n)}
    {a b c : Fin n} (hab : host.Adj a b) (hac : host.Adj a c) (hbc : b ≠ c) :
    ¬ cherryGraph.graph.Free host :=
  fun hfree => hfree ⟨{
    toHom := {
      toFun := ![a, b, c]
      map_rel' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [cherryGraph, starSimpleGraph] at hij ⊢ <;>
          first | exact hab | exact hac | exact hab.symm | exact hac.symm
    }
    injective' := by
      have := hab.ne; have := hac.ne
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp at hij ⊢ <;> tauto
  }⟩

/-- Two vertex-disjoint edges in `host` yield a copy of `twoMatchingGraph`. -/
theorem not_twoMatching_free_of_disjoint_adj {n : ℕ} {host : SimpleGraph (Fin n)}
    {u₁ v₁ u₂ v₂ : Fin n} (h₁ : host.Adj u₁ v₁) (h₂ : host.Adj u₂ v₂)
    (hu₁u₂ : u₁ ≠ u₂) (hu₁v₂ : u₁ ≠ v₂) (hv₁u₂ : v₁ ≠ u₂) (hv₁v₂ : v₁ ≠ v₂) :
    ¬ twoMatchingGraph.graph.Free host :=
  fun hfree => hfree ⟨{
    toHom := {
      toFun := ![u₁, v₁, u₂, v₂]
      map_rel' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [twoMatchingGraph, matchingSimpleGraph] at hij ⊢ <;>
          first | exact h₁ | exact h₁.symm | exact h₂ | exact h₂.symm
    }
    injective' := by
      have := h₁.ne; have := h₂.ne
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp at hij ⊢ <;> tauto
  }⟩

/-- Any `forestFamily`-free graph on `Fin n` has at most one edge. -/
theorem card_edgeFinset_le_one_of_familyFree {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree forestFamily host) :
    host.edgeFinset.card ≤ 1 := by
  have hcherry : cherryGraph.graph.Free host :=
    hfree cherryGraph (by simp [forestFamily])
  have hmatch : twoMatchingGraph.graph.Free host :=
    hfree twoMatchingGraph (by simp [forestFamily])
  rw [Finset.card_le_one]
  intro e₁ he₁ e₂ he₂
  induction e₁ using Sym2.ind with
  | _ u₁ v₁ =>
    induction e₂ using Sym2.ind with
    | _ u₂ v₂ =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he₁ he₂
      by_contra hne
      rcases eq_or_ne u₁ u₂ with rfl | hu₁u₂
      · exact not_cherry_free_of_adj_adj he₁ he₂ (fun h => hne (by rw [h])) hcherry
      rcases eq_or_ne u₁ v₂ with rfl | hu₁v₂
      · exact not_cherry_free_of_adj_adj he₁ he₂.symm (fun h => hne (by rw [h, Sym2.eq_swap])) hcherry
      rcases eq_or_ne v₁ u₂ with rfl | hv₁u₂
      · exact not_cherry_free_of_adj_adj he₁.symm he₂ (fun h => hne (by rw [h, Sym2.eq_swap])) hcherry
      rcases eq_or_ne v₁ v₂ with rfl | hv₁v₂
      · exact not_cherry_free_of_adj_adj he₁.symm he₂.symm hu₁u₂ hcherry
      exact not_twoMatching_free_of_disjoint_adj he₁ he₂ hu₁u₂ hu₁v₂ hv₁u₂ hv₁v₂ hmatch

/-- The family extremal number of `forestFamily` is at most `1` for every `n`. -/
theorem familyExtremal_forestFamily_le_one (n : ℕ) :
    familyExtremal forestFamily n ≤ 1 :=
  Finset.sup_le fun _ hmem =>
    card_edgeFinset_le_one_of_familyFree (Finset.mem_filter.mp hmem).2

/-- The star graph on `Fin n` is `2K_2`-free. -/
theorem twoMatchingGraph_free_starSimpleGraph (n : ℕ) :
    twoMatchingGraph.graph.Free (starSimpleGraph n) := by
  rintro ⟨f⟩
  have h01 : (starSimpleGraph n).Adj (f (0 : Fin 4)) (f (1 : Fin 4)) :=
    f.toHom.map_adj (⟨by decide, rfl⟩ : twoMatchingGraph.graph.Adj (0 : Fin 4) (1 : Fin 4))
  have h23 : (starSimpleGraph n).Adj (f (2 : Fin 4)) (f (3 : Fin 4)) :=
    f.toHom.map_adj (⟨by decide, rfl⟩ : twoMatchingGraph.graph.Adj (2 : Fin 4) (3 : Fin 4))
  rcases h01 with ⟨_, h0 | h1⟩ <;> rcases h23 with ⟨_, h2 | h3⟩ <;>
    [have : (0 : Fin 4) = 2 := f.injective (Fin.ext (h0.trans h2.symm));
     have : (0 : Fin 4) = 3 := f.injective (Fin.ext (h0.trans h3.symm));
     have : (1 : Fin 4) = 2 := f.injective (Fin.ext (h1.trans h2.symm));
     have : (1 : Fin 4) = 3 := f.injective (Fin.ext (h1.trans h3.symm))] <;>
    exact absurd this (by decide)

/-- Explicit spoke edges of `starSimpleGraph n`. -/
def starEdge (n : ℕ) (i : Fin (n - 1)) : Sym2 (Fin n) :=
  s(⟨0, by have := i.isLt; omega⟩, ⟨i.val + 1, by have := i.isLt; omega⟩)

theorem starEdge_mem_edgeFinset (n : ℕ) (i : Fin (n - 1)) :
    starEdge n i ∈ (starSimpleGraph n).edgeFinset := by
  simp [starEdge, Fin.ext_iff]

theorem starEdge_injective (n : ℕ) : Function.Injective (starEdge n) := by
  intro i j hij
  simp [starEdge, Fin.ext_iff] at hij
  exact Fin.ext (by omega)

/-- An injective family of `k` edges in `G.edgeFinset` witnesses `k ≤ G.edgeFinset.card`. -/
theorem le_card_edgeFinset_of_injective {n k : ℕ} {G : SimpleGraph (Fin n)}
    (e : Fin k → Sym2 (Fin n)) (he : ∀ i, e i ∈ G.edgeFinset) (hinj : Function.Injective e) :
    k ≤ G.edgeFinset.card := by
  simpa [Finset.card_image_of_injective _ hinj] using
    Finset.card_le_card (s := Finset.univ.image e)
      (Finset.image_subset_iff.mpr fun i _ => he i)

/-- `starSimpleGraph n` has at least `n - 1` edges. -/
theorem le_card_edgeFinset_starSimpleGraph (n : ℕ) :
    n - 1 ≤ (starSimpleGraph n).edgeFinset.card :=
  le_card_edgeFinset_of_injective (starEdge n) (starEdge_mem_edgeFinset n) (starEdge_injective n)

/-- Lower bound `n - 1 ≤ ex(n, 2K_2)` for all `n`. -/
theorem le_extremalNumber_twoMatchingGraph (n : ℕ) :
    n - 1 ≤ SimpleGraph.extremalNumber n twoMatchingGraph.graph := by
  simpa using (le_card_edgeFinset_starSimpleGraph n).trans
    (SimpleGraph.card_edgeFinset_le_extremalNumber (twoMatchingGraph_free_starSimpleGraph n))

/-- The matching graph on `Fin n` is `K_{1,2}`-free. -/
theorem cherryGraph_free_matchingSimpleGraph (n : ℕ) :
    cherryGraph.graph.Free (matchingSimpleGraph n) := by
  rintro ⟨f⟩
  have h01 : (matchingSimpleGraph n).Adj (f (0 : Fin 3)) (f (1 : Fin 3)) :=
    f.toHom.map_adj (⟨by decide, Or.inl rfl⟩ : cherryGraph.graph.Adj (0 : Fin 3) (1 : Fin 3))
  have h02 : (matchingSimpleGraph n).Adj (f (0 : Fin 3)) (f (2 : Fin 3)) :=
    f.toHom.map_adj (⟨by decide, Or.inl rfl⟩ : cherryGraph.graph.Adj (0 : Fin 3) (2 : Fin 3))
  have hne01 : (f (0 : Fin 3)).val ≠ (f (1 : Fin 3)).val :=
    Fin.val_ne_of_ne (f.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hne02 : (f (0 : Fin 3)).val ≠ (f (2 : Fin 3)).val :=
    Fin.val_ne_of_ne (f.injective.ne (by decide : (0 : Fin 3) ≠ 2))
  have hne12 : (f (1 : Fin 3)).val ≠ (f (2 : Fin 3)).val :=
    Fin.val_ne_of_ne (f.injective.ne (by decide : (1 : Fin 3) ≠ 2))
  have hdiv1 := h01.2
  have hdiv2 := h02.2
  omega

/-- Explicit matching edges of `matchingSimpleGraph n`. -/
def matchingEdge (n : ℕ) (i : Fin (n / 2)) : Sym2 (Fin n) :=
  s(⟨2 * i.val, by have := i.isLt; omega⟩, ⟨2 * i.val + 1, by have := i.isLt; omega⟩)

theorem matchingEdge_mem_edgeFinset (n : ℕ) (i : Fin (n / 2)) :
    matchingEdge n i ∈ (matchingSimpleGraph n).edgeFinset := by
  simp [matchingEdge, Fin.ext_iff]
  omega

theorem matchingEdge_injective (n : ℕ) : Function.Injective (matchingEdge n) := by
  intro i j hij
  simp [matchingEdge, Fin.ext_iff] at hij
  exact Fin.ext (by omega)

/-- `matchingSimpleGraph n` has at least `n / 2` edges. -/
theorem le_card_edgeFinset_matchingSimpleGraph (n : ℕ) :
    n / 2 ≤ (matchingSimpleGraph n).edgeFinset.card :=
  le_card_edgeFinset_of_injective (matchingEdge n) (matchingEdge_mem_edgeFinset n) (matchingEdge_injective n)

/-- Lower bound `n / 2 ≤ ex(n, K_{1,2})` for all `n`. -/
theorem le_extremalNumber_cherryGraph (n : ℕ) :
    n / 2 ≤ SimpleGraph.extremalNumber n cherryGraph.graph := by
  simpa using (le_card_edgeFinset_matchingSimpleGraph n).trans
    (SimpleGraph.card_edgeFinset_le_extremalNumber (cherryGraph_free_matchingSimpleGraph n))

/-- General archimedean refutation: if `familyExtremal family n ≤ 1` for all `n`
while `m ≤ extremalNumber (2 * m) H.graph` for all `m`, then `H` cannot control
`family`. -/
theorem not_controlsFamily_of_unbounded {family : Finset FiniteGraph} {H : FiniteGraph}
    (hfam : ∀ n : ℕ, familyExtremal family n ≤ 1)
    (hunb : ∀ m : ℕ, m ≤ SimpleGraph.extremalNumber (2 * m) H.graph) :
    ¬ ControlsFamily family H := by
  rintro ⟨C, hC, hbound⟩
  rw [Filter.eventually_atTop] at hbound
  rcases hbound with ⟨N, hN⟩
  obtain ⟨k, hk⟩ := exists_nat_gt C
  let m := max N (k + 1)
  have hm : (m : ℝ) ≤ SimpleGraph.extremalNumber (2 * m) H.graph := by exact_mod_cast hunb m
  have hf : (familyExtremal family (2 * m) : ℝ) ≤ 1 := by exact_mod_cast hfam (2 * m)
  have hkm : (k + 1 : ℝ) ≤ m := by exact_mod_cast le_max_right N (k + 1)
  nlinarith [hN (2 * m) (by omega)]

/-- `cherryGraph` does not control `forestFamily`. -/
theorem not_controlsFamily_cherryGraph :
    ¬ ControlsFamily forestFamily cherryGraph := by
  refine not_controlsFamily_of_unbounded familyExtremal_forestFamily_le_one fun m => ?_
  simpa using le_extremalNumber_cherryGraph (2 * m)

/-- `twoMatchingGraph` does not control `forestFamily`. -/
theorem not_controlsFamily_twoMatchingGraph :
    ¬ ControlsFamily forestFamily twoMatchingGraph := by
  refine not_controlsFamily_of_unbounded familyExtremal_forestFamily_le_one fun m => ?_
  exact le_trans (by omega : m ≤ 2 * m - 1) (le_extremalNumber_twoMatchingGraph (2 * m))

/-- `forestFamily` is not bipartite-compact. -/
theorem forestFamily_not_isBipartiteCompact :
    ¬ IsBipartiteCompactFamily forestFamily := by
  rintro ⟨H, hH, _, hcontrol⟩
  simp only [forestFamily, Finset.mem_insert, Finset.mem_singleton] at hH
  rcases hH with rfl | rfl
  exacts [not_controlsFamily_cherryGraph hcontrol, not_controlsFamily_twoMatchingGraph hcontrol]

/-- The literal statement of Erdős Problem #575 is false, witnessed by `forestFamily`. -/
theorem not_erdos_575_literal :
    ¬ BipartiteCompactnessStatement :=
  fun hstatement => forestFamily_not_isBipartiteCompact
    (hstatement forestFamily forestFamily_nonempty forestFamily_containsBipartiteMember)

/-- Complete quantitative package for the bipartite forest counterexample `{K_{1,2}, 2K_2}`. -/
theorem forestCounterexample :
    forestFamily.Nonempty ∧
    ContainsBipartiteMember forestFamily ∧
    (∀ forbidden ∈ forestFamily, forbidden.graph.IsBipartite) ∧
    (∀ n : ℕ, familyExtremal forestFamily n ≤ 1) ∧
    (∀ n : ℕ, n / 2 ≤ SimpleGraph.extremalNumber n cherryGraph.graph) ∧
    (∀ n : ℕ, n - 1 ≤ SimpleGraph.extremalNumber n twoMatchingGraph.graph) ∧
    ¬ IsBipartiteCompactFamily forestFamily :=
  ⟨forestFamily_nonempty, forestFamily_containsBipartiteMember,
    forestFamily_allBipartite, familyExtremal_forestFamily_le_one,
    le_extremalNumber_cherryGraph, le_extremalNumber_twoMatchingGraph,
    forestFamily_not_isBipartiteCompact⟩

end Erdos575.ForestCounterexample
