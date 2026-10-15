module

/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open SimpleGraph Filter

namespace Combinatorics
namespace Diagonal

/-- `HasRamseyProperty N s t` asserts: for every `m`, every coloring
`c : Finset (Fin m) → Bool`, and every `V : Finset (Fin m)` with `V.card ≥ N`, the subset
`V` contains either a subset of size `s` whose 2-element subsets are all `false`-coloured,
or a subset of size `t` whose 2-element subsets are all `true`-coloured. -/
def HasRamseyProperty (N s t : ℕ) : Prop :=
  ∀ {m : ℕ} (c : Finset (Fin m) → Bool) (V : Finset (Fin m)), N ≤ V.card →
    (∃ S ⊆ V, S.card = s ∧ ∀ e ⊆ S, e.card = 2 → c e = false) ∨
    (∃ S ⊆ V, S.card = t ∧ ∀ e ⊆ S, e.card = 2 → c e = true)

lemma forall_two_subset_singleton {m : ℕ} (v : Fin m) (b : Bool)
    (c : Finset (Fin m) → Bool) :
    ∀ e ⊆ ({v} : Finset (Fin m)), e.card = 2 → c e = b := by
  intro e he hecard
  have : e.card ≤ 1 := by
    have := Finset.card_le_card he
    simpa using this
  omega

lemma hasRamseyProperty_one_left (t : ℕ) : HasRamseyProperty 1 1 t := by
  intro m c V hV
  obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Or.inl ⟨{v}, by simpa using hv, by simp, ?_⟩
  exact forall_two_subset_singleton v false c

lemma hasRamseyProperty_one_right (s : ℕ) : HasRamseyProperty 1 s 1 := by
  intro m c V hV
  obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Or.inr ⟨{v}, by simpa using hv, by simp, ?_⟩
  exact forall_two_subset_singleton v true c

lemma card_false_true_split {m : ℕ} (c : Finset (Fin m) → Bool) (V : Finset (Fin m))
    {v : Fin m} (hv : v ∈ V) :
    ((V.erase v).filter (fun u => c {v, u} = false)).card
      + ((V.erase v).filter (fun u => c {v, u} = true)).card = V.card - 1 := by
  classical
  have hsplit :
      ((V.erase v).filter (fun u => c {v, u} = false)).card
        + ((V.erase v).filter (fun u => ¬ c {v, u} = false)).card = (V.erase v).card :=
    Finset.card_filter_add_card_filter_not (s := V.erase v) (fun u => c {v, u} = false)
  have hne_true : ∀ u : Fin m, ¬ (c {v, u} = false) ↔ c {v, u} = true := by
    intro u
    cases c {v, u} <;> simp
  have hrw : ((V.erase v).filter (fun u => ¬ c {v, u} = false)).card
      = ((V.erase v).filter (fun u => c {v, u} = true)).card := by
    congr 1
    ext u
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact hne_true u
  rw [hrw] at hsplit
  rw [hsplit, Finset.card_erase_of_mem hv]

lemma mono_insert {m : ℕ} {c : Finset (Fin m) → Bool} {b : Bool}
    {S : Finset (Fin m)} (hSmono : ∀ e ⊆ S, e.card = 2 → c e = b)
    {v : Fin m} (hvAdj : ∀ u ∈ S, c {v, u} = b) :
    ∀ e ⊆ insert v S, e.card = 2 → c e = b := by
  classical
  intro e he hecard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  have hx : x ∈ insert v S := he (Finset.mem_insert_self _ _)
  have hy : y ∈ insert v S :=
    he (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  rcases Finset.mem_insert.mp hx with hx_eq | hxS
  · rcases Finset.mem_insert.mp hy with hy_eq | hyS
    · exact (hxy (hx_eq.trans hy_eq.symm)).elim
    · rw [hx_eq]; exact hvAdj y hyS
  · rcases Finset.mem_insert.mp hy with hy_eq | hyS
    · rw [hy_eq, Finset.pair_comm]; exact hvAdj x hxS
    · have hsub : ({x, y} : Finset (Fin m)) ⊆ S := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hz_eq | hz'
        · rw [hz_eq]; exact hxS
        · rw [Finset.mem_singleton.mp hz']; exact hyS
      have hcard2 : ({x, y} : Finset (Fin m)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
      exact hSmono _ hsub hcard2

lemma HasRamseyProperty.step {Ns Nt s t : ℕ}
    (hs : HasRamseyProperty Ns s (t + 1))
    (ht : HasRamseyProperty Nt (s + 1) t) (hNs : 1 ≤ Ns) :
    HasRamseyProperty (Ns + Nt) (s + 1) (t + 1) := by
  classical
  intro m c V hV
  have hVpos : 0 < V.card := by
    have : 1 ≤ V.card := Nat.le_trans hNs (Nat.le_trans (Nat.le_add_right _ _) hV)
    exact this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
  set R := (V.erase v).filter (fun u => c {v, u} = false)
  set B := (V.erase v).filter (fun u => c {v, u} = true)
  have hsplit : R.card + B.card = V.card - 1 :=
    card_false_true_split c V hv
  have hRsubV : R ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBsubV : B ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hvnR : v ∉ R := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  have hvnB : v ∉ B := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  obtain hRcard | hRcard := le_or_gt Ns R.card
  · rcases hs c R hRcard with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · have hvS : v ∉ S := fun h => hvnR (hSsub h)
      refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hRsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem hvS, hScard]
      · apply mono_insert hSmono
        intro u hu
        have hu' : u ∈ R := hSsub hu
        exact (Finset.mem_filter.mp hu').2
    · exact Or.inr ⟨S, hSsub.trans hRsubV, hScard, hSmono⟩
  · rcases ht c B (by omega) with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · exact Or.inl ⟨S, hSsub.trans hBsubV, hScard, hSmono⟩
    · have hvS : v ∉ S := fun h => hvnB (hSsub h)
      refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hBsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem hvS, hScard]
      · apply mono_insert hSmono
        intro u hu
        have hu' : u ∈ B := hSsub hu
        exact (Finset.mem_filter.mp hu').2

end Diagonal
end Combinatorics

namespace Erdos667.Core

/-- A graph `G` on `n` vertices is *`(p, q)`-locally dense* if every set of `p` of its vertices
spans at least `q` edges of `G`; equivalently, every induced subgraph on `p` vertices has at
least `q` edges. -/
def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard

open Classical in
/-- `H p q n` is `H(n) = H(n; p, q)`: the largest `m` such that *every* `(p, q)`-locally dense
graph on `n` vertices must contain a complete graph on `m` vertices `Kₘ`. -/
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n

/-- The growth exponent `c(p, q) = liminf_{n → ∞} (log H(n)) / (log n)`. -/
noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop

/-- The main conjecture of Erdős Problem 667. -/
def Erdos667Conjecture : Prop :=
  ∀ p : ℕ, StrictMonoOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1))

theorem locallyDense_anti_q {p q₁ q₂ n : ℕ} {G : SimpleGraph (Fin n)}
    (hq : q₁ ≤ q₂) (h : LocallyDense p q₂ G) : LocallyDense p q₁ G :=
  fun s hs => hq.trans (h s hs)

theorem locallyDense_zero (p : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    LocallyDense p 0 G :=
  fun _ _ => Nat.zero_le _

theorem locallyDense_of_lt {p q n : ℕ} (h : n < p) (G : SimpleGraph (Fin n)) :
    LocallyDense p q G := by
  intro s hs
  have hle : s.card ≤ n := by simpa [Fintype.card_fin] using Finset.card_le_univ s
  omega

theorem H_le (p q n : ℕ) : H p q n ≤ n :=
  Nat.findGreatest_le n

theorem H_zero_right (p q : ℕ) : H p q 0 = 0 := by
  have := H_le p q 0
  omega

theorem H_spec {p q n : ℕ} :
    ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree (H p q n) := by
  have h0 : ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree 0 :=
    fun _ _ => SimpleGraph.not_cliqueFree_zero
  exact Nat.findGreatest_spec
    (P := fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m)
    (Nat.zero_le n) h0

theorem le_H_of_forall {p q n m : ℕ} (hm : m ≤ n)
    (h : ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) :
    m ≤ H p q n :=
  Nat.le_findGreatest hm h

theorem le_H_iff {p q n m : ℕ} (hm : m ≤ n) :
    m ≤ H p q n ↔ ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m :=
  ⟨fun h G hG hcf => H_spec G hG (hcf.mono h), le_H_of_forall hm⟩

theorem one_le_H {p q n : ℕ} (hn : 1 ≤ n) : 1 ≤ H p q n := by
  apply le_H_of_forall hn
  intro G _
  rw [SimpleGraph.cliqueFree_one]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact not_isEmpty_of_nonempty (Fin n)

theorem H_one_right (p q : ℕ) : H p q 1 = 1 := by
  have hle := H_le p q 1
  have hge : 1 ≤ H p q 1 := one_le_H le_rfl
  omega

theorem H_mono_q {p q₁ q₂ n : ℕ} (hq : q₁ ≤ q₂) : H p q₁ n ≤ H p q₂ n :=
  Nat.findGreatest_mono_left (fun _ hm G hG => hm G (locallyDense_anti_q hq hG)) n

theorem H_zero_q {p n : ℕ} (hn : 1 ≤ n) : H p 0 n = 1 := by
  apply le_antisymm
  · by_contra hgt
    have h2 : 2 ≤ H p 0 n := by omega
    have hbot := H_spec (⊥ : SimpleGraph (Fin n)) (locallyDense_zero p ⊥)
    have hcf2 : (⊥ : SimpleGraph (Fin n)).CliqueFree 2 := SimpleGraph.cliqueFree_bot (by omega)
    exact hbot (hcf2.mono h2)
  · exact one_le_H hn

theorem log_H_div_log_nonneg (p q n : ℕ) : 0 ≤ Real.log (H p q n) / Real.log n := by
  rcases lt_or_ge n 1 with hn0 | hn1
  · have : n = 0 := by omega
    subst this
    simp
  · apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast one_le_H (p := p) (q := q) hn1
    · apply Real.log_nonneg
      exact_mod_cast hn1

theorem log_H_div_log_le_one (p q n : ℕ) : Real.log (H p q n) / Real.log n ≤ 1 := by
  rcases lt_or_ge n 2 with hn2 | hn2
  · interval_cases n <;> simp
  · have hn1 : 1 ≤ n := by omega
    have hH1 : (0 : ℝ) < (H p q n : ℝ) := by
      have : 1 ≤ H p q n := one_le_H hn1
      positivity
    have hlogn : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hn2
    rw [div_le_one hlogn]
    exact Real.log_le_log hH1 (by exact_mod_cast H_le p q n)

theorem isBoundedUnder_log_H (p q : ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => Real.log (H p q n) / Real.log n) :=
  ⟨0, eventually_map.mpr (Eventually.of_forall (log_H_div_log_nonneg p q))⟩

theorem isCoboundedUnder_log_H (p q : ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (fun n : ℕ => Real.log (H p q n) / Real.log n) :=
  isCoboundedUnder_ge_of_le atTop (log_H_div_log_le_one p q)

theorem zero_le_c (p q : ℕ) : 0 ≤ c p q :=
  le_liminf_of_le (isCoboundedUnder_log_H p q) (Eventually.of_forall (log_H_div_log_nonneg p q))

theorem c_le_one (p q : ℕ) : c p q ≤ 1 :=
  liminf_le_of_frequently_le (Frequently.of_forall (log_H_div_log_le_one p q))
    (isBoundedUnder_log_H p q)

theorem log_H_div_log_mono_q {p q₁ q₂ n : ℕ} (hq : q₁ ≤ q₂) :
    Real.log (H p q₁ n) / Real.log n ≤ Real.log (H p q₂ n) / Real.log n := by
  rcases lt_or_ge n 1 with hn0 | hn1
  · have : n = 0 := by omega
    subst this
    simp
  · apply div_le_div_of_nonneg_right
    · apply Real.log_le_log
      · have : 1 ≤ H p q₁ n := one_le_H hn1
        positivity
      · exact_mod_cast H_mono_q (p := p) (n := n) hq
    · apply Real.log_nonneg
      exact_mod_cast hn1

theorem c_mono_q (p : ℕ) : Monotone (c p) :=
  fun _ _ hq => liminf_le_liminf (Eventually.of_forall (fun _ => log_H_div_log_mono_q hq))
    (isBoundedUnder_log_H p _) (isCoboundedUnder_log_H p _)

theorem variantsMonotoneOn (p : ℕ) :
    MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) :=
  (c_mono_q p).monotoneOn _

theorem c_zero_q (p : ℕ) : c p 0 = 0 := by
  have hev : (fun n : ℕ => Real.log (H p 0 n) / Real.log n) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [H_zero_q (p := p) hn]
  unfold c
  rw [liminf_congr hev, liminf_const]

/-! ## Part 1: Induced Subgraph Edge Bounds & Complete Threshold (`q ≥ C(p, 2)`) -/

theorem induce_edgeSet_ncard_eq_card_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    (G.induce (s : Set (Fin n))).edgeSet.ncard =
      (G.induce (s : Set (Fin n))).edgeFinset.card := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

theorem induce_edgeSet_ncard_le_choose_two {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    (G.induce (s : Set (Fin n))).edgeSet.ncard ≤ s.card.choose 2 := by
  rw [induce_edgeSet_ncard_eq_card_edgeFinset]
  have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.induce (s : Set (Fin n)))
  simpa using h1

theorem not_locallyDense_of_choose_two_lt {p q n : ℕ} (hpn : p ≤ n) (hq : p.choose 2 < q)
    (G : SimpleGraph (Fin n)) : ¬ LocallyDense p q G := by
  intro hG
  have hcard : p ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hpn
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  have h1 := hG s hs
  have h2 := induce_edgeSet_ncard_le_choose_two G s
  rw [hs] at h2
  omega

theorem H_eq_self_of_choose_two_lt {p q n : ℕ} (hpn : p ≤ n) (hq : p.choose 2 < q) :
    H p q n = n := by
  apply le_antisymm (H_le p q n)
  apply le_H_of_forall le_rfl
  intro G hG
  exact False.elim (not_locallyDense_of_choose_two_lt hpn hq G hG)

theorem locallyDense_top_of_le_choose_two {p q n : ℕ} (hq : q ≤ p.choose 2) :
    LocallyDense p q (⊤ : SimpleGraph (Fin n)) := by
  intro s hs
  rw [SimpleGraph.induce_top, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcard : (⊤ : SimpleGraph s).edgeFinset.card = s.card.choose 2 := by
    simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := s)
  rw [hcard, hs]
  exact hq

theorem eq_top_of_locallyDense_choose_two {p n : ℕ} (hp : 2 ≤ p) (hpn : p ≤ n)
    {G : SimpleGraph (Fin n)} (hG : LocallyDense p (p.choose 2) G) : G = ⊤ := by
  ext u v
  simp only [top_adj]
  constructor
  · exact G.ne_of_adj
  · intro huv
    by_contra hnad
    have hpair_card : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have hrem : p - 2 ≤ ((Finset.univ : Finset (Fin n)) \ {u, v}).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hpair_card,
        Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hrem
    have hdisj : Disjoint ({u, v} : Finset (Fin n)) t :=
      Disjoint.mono_right ht_sub disjoint_sdiff_self_right
    let s := ({u, v} : Finset (Fin n)) ∪ t
    have hs_card : s.card = p := by
      rw [Finset.card_union_of_disjoint hdisj, hpair_card, ht_card]
      omega
    have h_dense := hG s hs_card
    have hu_s : u ∈ s := Finset.mem_union_left _ (by simp)
    have hv_s : v ∈ s := Finset.mem_union_left _ (by simp)
    let su : s := ⟨u, hu_s⟩
    let sv : s := ⟨v, hv_s⟩
    have hsu_sv : su ≠ sv := fun h => huv (congrArg Subtype.val h)
    have hnot_mem : s(su, sv) ∉ (G.induce (s : Set (Fin n))).edgeFinset := by
      simp [su, sv, hnad]
    have hmem_top : s(su, sv) ∈ ((⊤ : SimpleGraph s).edgeFinset) := by
      simp [hsu_sv]
    have hsub_edge : (G.induce (s : Set (Fin n))).edgeFinset ⊂ (⊤ : SimpleGraph s).edgeFinset := by
      rw [Finset.ssubset_iff_of_subset (SimpleGraph.edgeFinset_mono le_top)]
      exact ⟨s(su, sv), hmem_top, hnot_mem⟩
    have hlt_card : (G.induce (s : Set (Fin n))).edgeFinset.card <
        (⊤ : SimpleGraph s).edgeFinset.card :=
      Finset.card_lt_card hsub_edge
    have htop_card : (⊤ : SimpleGraph s).edgeFinset.card = s.card.choose 2 := by
      simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := s)
    rw [induce_edgeSet_ncard_eq_card_edgeFinset] at h_dense
    rw [htop_card, hs_card] at hlt_card
    omega

theorem not_cliqueFree_top_self (n : ℕ) : ¬ (⊤ : SimpleGraph (Fin n)).CliqueFree n := by
  have hcl : (⊤ : SimpleGraph (Fin n)).IsNClique n Finset.univ := by
    refine ⟨SimpleGraph.IsClique.top _, ?_⟩
    simp
  exact hcl.not_cliqueFree

theorem H_eq_self_of_choose_two_le {p q n : ℕ} (hp : 2 ≤ p) (hpn : p ≤ n)
    (hq : p.choose 2 ≤ q) : H p q n = n := by
  apply le_antisymm (H_le p q n)
  have h1 : n ≤ H p (p.choose 2) n := by
    apply le_H_of_forall le_rfl
    intro G hG
    rw [eq_top_of_locallyDense_choose_two hp hpn hG]
    exact not_cliqueFree_top_self n
  exact h1.trans (H_mono_q hq)

theorem H_eq_one_of_lt {p q n : ℕ} (hn1 : 1 ≤ n) (hnp : n < p) : H p q n = 1 := by
  apply le_antisymm
  · by_contra hgt
    have h2 : 2 ≤ H p q n := by omega
    have hbot : ¬ (⊥ : SimpleGraph (Fin n)).CliqueFree (H p q n) :=
      H_spec (⊥ : SimpleGraph (Fin n)) (locallyDense_of_lt hnp ⊥)
    have hcf2 : (⊥ : SimpleGraph (Fin n)).CliqueFree 2 := SimpleGraph.cliqueFree_bot (by omega)
    exact hbot (hcf2.mono h2)
  · exact one_le_H hn1

/-! ## Part 2: Greedy Clique Extension & Right Endpoint (`erdos_667.variants.endpoint`) -/

theorem induce_insert_edgeSet_ncard_le_choose_two_of_forall_not_adj
    {n : ℕ} (G : SimpleGraph (Fin n)) {v : Fin n} {t : Finset (Fin n)}
    (hadj : ∀ u ∈ t, ¬ G.Adj v u) :
    (G.induce (insert v t : Finset (Fin n))).edgeSet.ncard ≤ t.card.choose 2 := by
  let s : Finset (Fin n) := insert v t
  let H : SimpleGraph s := G.induce (s : Set (Fin n))
  let H' : SimpleGraph t := G.induce (t : Set (Fin n))
  have hsub : t ⊆ s := Finset.subset_insert v t
  let f : t → s := fun x => ⟨x.1, hsub x.2⟩
  have h_surj : H.edgeSet ⊆ Sym2.map f '' H'.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x.1 y.1 := he
      have hxv : x.1 ≠ v := by
        intro hx_eq
        have hvy : G.Adj v y.1 := hx_eq ▸ hxy
        rcases Finset.mem_insert.mp y.2 with hy_eq | hyt
        · exact G.ne_of_adj hvy hy_eq.symm
        · exact hadj y.1 hyt hvy
      have hyv : y.1 ≠ v := by
        intro hy_eq
        have hvx : G.Adj v x.1 := hy_eq ▸ hxy.symm
        rcases Finset.mem_insert.mp x.2 with hx_eq | hxt
        · exact G.ne_of_adj hvx hx_eq.symm
        · exact hadj x.1 hxt hvx
      have hxt : x.1 ∈ t := by
        rcases Finset.mem_insert.mp x.2 with hx_eq | hxt
        · exact False.elim (hxv hx_eq)
        · exact hxt
      have hyt : y.1 ∈ t := by
        rcases Finset.mem_insert.mp y.2 with hy_eq | hyt
        · exact False.elim (hyv hy_eq)
        · exact hyt
      refine ⟨s(⟨x.1, hxt⟩, ⟨y.1, hyt⟩), hxy, rfl⟩
  calc H.edgeSet.ncard
      ≤ (Sym2.map f '' H'.edgeSet).ncard := Set.ncard_le_ncard h_surj
    _ ≤ H'.edgeSet.ncard := Set.ncard_image_le
    _ ≤ t.card.choose 2 := induce_edgeSet_ncard_le_choose_two G t

noncomputable def nonNeighborAndSelf {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun u => ¬ G.Adj v u)

theorem mem_nonNeighborAndSelf_self {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    v ∈ nonNeighborAndSelf G v := by
  simp [nonNeighborAndSelf]

theorem nonNeighborAndSelf_card_le_pred_of_locallyDense_endpoint
    {p n : ℕ} (hp : 2 ≤ p) {G : SimpleGraph (Fin n)}
    (hG : LocallyDense p ((p - 1).choose 2 + 1) G) (v : Fin n) :
    (nonNeighborAndSelf G v).card ≤ p - 1 := by
  by_contra hgt
  have hle : p - 1 ≤ ((nonNeighborAndSelf G v).erase v).card := by
    rw [Finset.card_erase_of_mem (mem_nonNeighborAndSelf_self G v)]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hle
  have hvt : v ∉ t := fun hv => Finset.notMem_erase v _ (ht_sub hv)
  have hadj : ∀ u ∈ t, ¬ G.Adj v u := by
    intro u hu
    have hu' := Finset.mem_of_mem_erase (ht_sub hu)
    simpa [nonNeighborAndSelf] using hu'
  have hs_card : (insert v t).card = p := by
    rw [Finset.card_insert_of_notMem hvt, ht_card]
    omega
  have h_dense := hG (insert v t) hs_card
  have h_ub := induce_insert_edgeSet_ncard_le_choose_two_of_forall_not_adj G hadj
  rw [ht_card] at h_ub
  omega

theorem exists_isNClique_of_nonNeighborAndSelf_le
    {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ v : Fin n, (nonNeighborAndSelf G v).card ≤ d) :
    ∀ m : ℕ, m * d < n + d → ∃ K : Finset (Fin n), G.IsNClique m K := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨∅, SimpleGraph.isNClique_empty.mpr rfl⟩
  | succ m ih =>
    intro hm
    have hmul : (m + 1) * d = m * d + d := Nat.succ_mul m d
    have hmd_lt : m * d < n := by omega
    obtain ⟨K, hK⟩ := ih (by omega)
    let bad := K.biUnion (nonNeighborAndSelf G)
    have hbad_card : bad.card ≤ m * d := by
      calc bad.card ≤ ∑ v ∈ K, (nonNeighborAndSelf G v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ K, d := Finset.sum_le_sum (fun v _ => hd v)
        _ = K.card * d := by simp
        _ = m * d := by rw [hK.card_eq]
    have hbad_lt : bad.card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨w, _, hw_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
    have hw_adj : ∀ v ∈ K, G.Adj w v := by
      intro v hv
      by_contra hnav
      apply hw_not
      refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
      simp only [nonNeighborAndSelf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hvw => hnav hvw.symm
    exact ⟨insert w K, hK.insert hw_adj⟩

theorem nat_le_ceil_div_mul (n d : ℕ) (hd : 1 ≤ d) :
    n ≤ ((n + d - 1) / d) * d := by
  have hmod := Nat.div_add_mod (n + d - 1) d
  have hlt : (n + d - 1) % d < d := Nat.mod_lt _ (by omega)
  have hcomm : d * ((n + d - 1) / d) = ((n + d - 1) / d) * d := Nat.mul_comm _ _
  omega

theorem ceil_div_le_self (n d : ℕ) (hd : 1 ≤ d) :
    (n + d - 1) / d ≤ n := by
  rw [Nat.div_le_iff_le_mul_add_pred hd]
  have : 1 * n ≤ d * n := Nat.mul_le_mul_right n hd
  omega

theorem ceil_div_pred_le_H_endpoint {p n : ℕ} (hp : 2 ≤ p) :
    (n + p - 2) / (p - 1) ≤ H p ((p - 1).choose 2 + 1) n := by
  have hd : 1 ≤ p - 1 := by omega
  have heq : n + p - 2 = n + (p - 1) - 1 := by omega
  rw [heq]
  apply le_H_of_forall (ceil_div_le_self n (p - 1) hd)
  intro G hG
  have hdG := nonNeighborAndSelf_card_le_pred_of_locallyDense_endpoint hp hG
  have h_mul : ((n + (p - 1) - 1) / (p - 1)) * (p - 1) ≤ n + (p - 1) - 1 :=
    Nat.div_mul_le_self (n + (p - 1) - 1) (p - 1)
  obtain ⟨K, hK⟩ := exists_isNClique_of_nonNeighborAndSelf_le G hdG
    ((n + (p - 1) - 1) / (p - 1)) (by omega)
  exact hK.not_cliqueFree

theorem nat_le_H_endpoint_mul_pred {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    n ≤ H p ((p - 1).choose 2 + 1) n * (p - 1) := by
  have hd : 1 ≤ p - 1 := by omega
  have h1 := nat_le_ceil_div_mul n (p - 1) hd
  have h2 := ceil_div_pred_le_H_endpoint (p := p) (n := n) hp
  have heq : n + (p - 1) - 1 = n + p - 2 := by omega
  rw [heq] at h1
  exact h1.trans (Nat.mul_le_mul_right (p - 1) h2)

theorem endpoint_c_eq_one_of_nat_le {p q : ℕ} (hp : 2 ≤ p)
    (hH : ∀ n : ℕ, n ≤ H p q n * (p - 1)) :
    c p q = 1 := by
  apply le_antisymm (c_le_one p q)
  by_contra! hlt
  let ε : ℝ := (1 - c p q) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h1 : 1 - ε ≤ c p q := by
    unfold c
    apply le_liminf_of_le (isCoboundedUnder_log_H p q)
    let C : ℝ := Real.log ((p - 1 : ℕ) : ℝ)
    let N : ℕ := max p (Nat.ceil (Real.exp (C / ε)) + 2)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn2 : 2 ≤ n := by omega
    have hpm1_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      have : 1 ≤ p - 1 := by omega
      positivity
    have hn_le_H : (n : ℝ) ≤ (H p q n : ℝ) * ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hH n
    have hdiv_le : (n : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ (H p q n : ℝ) :=
      (div_le_iff₀ hpm1_pos).mpr hn_le_H
    have hdiv_pos : 0 < (n : ℝ) / ((p - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) := by positivity
      exact div_pos this hpm1_pos
    have hlog_le : Real.log (n : ℝ) - C ≤ Real.log (H p q n : ℝ) := by
      have := Real.log_le_log hdiv_pos hdiv_le
      rwa [Real.log_div (by positivity) (by positivity)] at this
    have hlogn_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hn2
    have hexp_le : Real.exp (C / ε) < (n : ℝ) := by
      have hN_le : Nat.ceil (Real.exp (C / ε)) + 2 ≤ n := le_trans (le_max_right _ _) hn
      have hceil : Real.exp (C / ε) ≤ (Nat.ceil (Real.exp (C / ε)) : ℝ) := Nat.le_ceil _
      have hcast : ((Nat.ceil (Real.exp (C / ε)) + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hN_le
      push_cast at hcast
      linarith
    have hC_lt : C / ε < Real.log (n : ℝ) := by
      rw [← Real.lt_log_iff_exp_lt (by positivity)] at hexp_le
      exact hexp_le
    have hC_le_eps : C / Real.log (n : ℝ) ≤ ε := by
      rw [div_le_iff₀ hlogn_pos]
      have := (div_lt_iff₀ hε).mp hC_lt
      linarith
    calc 1 - ε ≤ 1 - C / Real.log (n : ℝ) := by linarith
      _ = (Real.log (n : ℝ) - C) / Real.log (n : ℝ) := by
        rw [sub_div, div_self (ne_of_gt hlogn_pos)]
      _ ≤ Real.log (H p q n : ℝ) / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hlog_le (le_of_lt hlogn_pos)
  dsimp [ε] at h1
  linarith

theorem variantsEndpoint (p : ℕ) (hp : 2 ≤ p) :
    c p (Nat.choose (p - 1) 2 + 1) = 1 :=
  endpoint_c_eq_one_of_nat_le hp (nat_le_H_endpoint_mul_pred hp)

theorem c_eq_one_of_endpoint_le {p q : ℕ} (hp : 2 ≤ p)
    (hq : Nat.choose (p - 1) 2 + 1 ≤ q) : c p q = 1 := by
  apply le_antisymm (c_le_one p q)
  rw [← variantsEndpoint p hp]
  exact c_mono_q p hq

theorem c_two_one : c 2 1 = 1 := by
  simpa using variantsEndpoint 2 le_rfl

/-- Negative control for `erdos_667.variants.ramsey_bounds`: at `p = 2`, the condition `q = 1`
forces `G` to be complete (`c 2 1 = 1`), so the upper bound `c p 1 ≤ 2 / (p + 1)` fails at `p = 2`
and requires the hypothesis `3 ≤ p`. -/
theorem not_ramsey_upper_bound_at_two : ¬ (c 2 1 ≤ 2 / ((2 : ℝ) + 1)) := by
  rw [c_two_one]
  norm_num

/-! ## Part 3: Cocktail-Party Construction & Exact Formula for `H(n; 3, 2)` -/

def cocktailPartyGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u.1 / 2 ≠ v.1 / 2
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

theorem cocktailPartyGraph_cliqueFree (n : ℕ) :
    (cocktailPartyGraph n).CliqueFree ((n + 1) / 2 + 1) := by
  intro K hK
  have hinj : Set.InjOn (fun v : Fin n => v.1 / 2) (K : Set (Fin n)) := by
    intro u hu v hv huv
    by_contra hne
    have hadj : (cocktailPartyGraph n).Adj u v := hK.isClique hu hv hne
    exact hadj huv
  have hmaps : Set.MapsTo (fun v : Fin n => v.1 / 2)
      (K : Set (Fin n)) (Finset.range ((n + 1) / 2)) := by
    intro v _
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hcard := Finset.card_le_card_of_injOn (fun v : Fin n => v.1 / 2) hmaps hinj
  have hKcard := hK.card_eq
  simp only [Finset.card_range] at hcard
  omega

theorem edgeSet_ncard_ge_two_of_two_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz_ne : y ≠ z) :
    2 ≤ G.edgeSet.ncard := by
  have h1 : s(x, y) ∈ G.edgeSet := hxy
  have h2 : s(x, z) ∈ G.edgeSet := hxz
  have hne : (s(x, y) : Sym2 V) ≠ s(x, z) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · exact hyz_ne rfl
    · exact G.ne_of_adj hxy rfl
  have hsub : ({s(x, y), s(x, z)} : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    rcases Set.mem_insert_iff.mp he with rfl | he'
    · exact h1
    · rw [Set.mem_singleton_iff.mp he']
      exact h2
  have hfinite : G.edgeSet.Finite := Set.toFinite _
  calc 2 = ({s(x, y), s(x, z)} : Set (Sym2 V)).ncard := (Set.ncard_pair hne).symm
    _ ≤ G.edgeSet.ncard := Set.ncard_le_ncard hsub hfinite

theorem cocktailPartyGraph_locallyDense_three_two (n : ℕ) :
    LocallyDense 3 2 (cocktailPartyGraph n) := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, hs_eq⟩ := Finset.card_eq_three.mp hs
  let sa : s := ⟨a, by simp [hs_eq]⟩
  let sb : s := ⟨b, by simp [hs_eq]⟩
  let sc : s := ⟨c, by simp [hs_eq]⟩
  have hsa_sb : sa ≠ sb := fun h => hab (congrArg Subtype.val h)
  have hsa_sc : sa ≠ sc := fun h => hac (congrArg Subtype.val h)
  have hsb_sc : sb ≠ sc := fun h => hbc (congrArg Subtype.val h)
  by_cases h1 : a.1 / 2 = b.1 / 2
  · have h2 : a.1 / 2 ≠ c.1 / 2 := by
      intro hc
      have : a.1 = b.1 ∨ a.1 = c.1 ∨ b.1 = c.1 := by omega
      rcases this with h | h | h
      · exact hab (Fin.ext h)
      · exact hac (Fin.ext h)
      · exact hbc (Fin.ext h)
    have h3 : b.1 / 2 ≠ c.1 / 2 := by omega
    exact edgeSet_ncard_ge_two_of_two_adj ((cocktailPartyGraph n).induce (s : Set (Fin n)))
      (x := sc) (y := sa) (z := sb) (Ne.symm h2) (Ne.symm h3) hsa_sb
  · by_cases h2 : a.1 / 2 = c.1 / 2
    · have h3 : b.1 / 2 ≠ c.1 / 2 := by omega
      exact edgeSet_ncard_ge_two_of_two_adj ((cocktailPartyGraph n).induce (s : Set (Fin n)))
        (x := sb) (y := sa) (z := sc) (Ne.symm h1) h3 hsa_sc
    · exact edgeSet_ncard_ge_two_of_two_adj ((cocktailPartyGraph n).induce (s : Set (Fin n)))
        (x := sa) (y := sb) (z := sc) h1 h2 hsb_sc

theorem H_three_two_le (n : ℕ) : H 3 2 n ≤ (n + 1) / 2 := by
  by_contra hgt
  have hle : (n + 1) / 2 + 1 ≤ H 3 2 n := by omega
  have hnot := H_spec (cocktailPartyGraph n) (cocktailPartyGraph_locallyDense_three_two n)
  exact hnot ((cocktailPartyGraph_cliqueFree n).mono hle)

theorem H_three_two_eq (n : ℕ) : H 3 2 n = (n + 1) / 2 := by
  apply le_antisymm (H_three_two_le n)
  have h := ceil_div_pred_le_H_endpoint (p := 3) (n := n) (by omega)
  simpa using h

/-! ## Part 4: Classical Ramsey Equivalence (`q = 1`), Erdős–Szekeres Lower Bound, & Block-Clique Upper Bounds -/

theorem le_card_of_not_cliqueFree {n m : ℕ} {G : SimpleGraph (Fin n)} (h : ¬ G.CliqueFree m) :
    m ≤ n := by
  by_contra hlt
  have hcf : G.CliqueFree m := SimpleGraph.cliqueFree_of_card_lt (by simpa using Nat.lt_of_not_ge hlt)
  exact h hcf

theorem locallyDense_one_iff_compl_cliqueFree {p n : ℕ} (G : SimpleGraph (Fin n)) :
    LocallyDense p 1 G ↔ Gᶜ.CliqueFree p := by
  constructor
  · intro hG s hs
    have hcard : s.card = p := hs.card_eq
    have h1 : 1 ≤ (G.induce (s : Set (Fin n))).edgeSet.ncard := hG s hcard
    have hne : (G.induce (s : Set (Fin n))).edgeSet.Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x.1 y.1 := he
      have hne_xy : x.1 ≠ y.1 := G.ne_of_adj hxy
      have hcompl : Gᶜ.Adj x.1 y.1 := hs.isClique x.2 y.2 hne_xy
      exact (SimpleGraph.compl_adj G x.1 y.1).mp hcompl |>.2 hxy
  · intro hcf s hs
    have hnot : ¬ Gᶜ.IsNClique p s := hcf s
    have hnot_cl : ¬ Gᶜ.IsClique (s : Set (Fin n)) := fun hcl => hnot ⟨hcl, hs⟩
    rw [SimpleGraph.isClique_iff, Set.Pairwise] at hnot_cl
    push Not at hnot_cl
    obtain ⟨x, hx, y, hy, hxy_ne, hnot_compl⟩ := hnot_cl
    have hxy : G.Adj x y := by
      by_contra hnad
      exact hnot_compl ((SimpleGraph.compl_adj G x y).mpr ⟨hxy_ne, hnad⟩)
    have hmem : s(⟨x, hx⟩, ⟨y, hy⟩) ∈ (G.induce (s : Set (Fin n))).edgeSet := hxy
    have hfin : (G.induce (s : Set (Fin n))).edgeSet.Finite := Set.toFinite _
    exact (Set.ncard_pos hfin).mpr ⟨_, hmem⟩

theorem hasRamseyProperty_choose_succ : ∀ (s t : ℕ),
    Combinatorics.Diagonal.HasRamseyProperty (Nat.choose (s + t) s) (s + 1) (t + 1) := by
  suffices h : ∀ (n : ℕ), ∀ (s t : ℕ), s + t = n →
      Combinatorics.Diagonal.HasRamseyProperty (Nat.choose n s) (s + 1) (t + 1) by
    intro s t
    exact h (s + t) s t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hst
    match s, t, hst with
    | 0, t, hst =>
      show Combinatorics.Diagonal.HasRamseyProperty (Nat.choose n 0) 1 (t + 1)
      rw [Nat.choose_zero_right]
      exact Combinatorics.Diagonal.hasRamseyProperty_one_left (t + 1)
    | s + 1, 0, hst =>
      have h1 : n = s + 1 := by omega
      show Combinatorics.Diagonal.HasRamseyProperty (Nat.choose n (s + 1)) (s + 1 + 1) 1
      rw [h1, Nat.choose_self]
      exact Combinatorics.Diagonal.hasRamseyProperty_one_right (s + 1 + 1)
    | s + 1, t + 1, hst =>
      have hn_pred : n - 1 + 1 = n := by omega
      have hs_ih : Combinatorics.Diagonal.HasRamseyProperty (Nat.choose (n - 1) s) (s + 1) (t + 1 + 1) :=
        ih (n - 1) (by omega) s (t + 1) (by omega)
      have ht_ih : Combinatorics.Diagonal.HasRamseyProperty (Nat.choose (n - 1) (s + 1)) (s + 1 + 1) (t + 1) :=
        ih (n - 1) (by omega) (s + 1) t (by omega)
      have hNs_pos : 1 ≤ Nat.choose (n - 1) s := Nat.choose_pos (by omega)
      have hrec : Combinatorics.Diagonal.HasRamseyProperty
          (Nat.choose (n - 1) s + Nat.choose (n - 1) (s + 1)) (s + 1 + 1) (t + 1 + 1) :=
        Combinatorics.Diagonal.HasRamseyProperty.step hs_ih ht_ih hNs_pos
      have hpascal : Nat.choose n (s + 1) = Nat.choose (n - 1) s + Nat.choose (n - 1) (s + 1) := by
        conv_lhs => rw [← hn_pred]
        rw [Nat.choose_succ_succ]
      show Combinatorics.Diagonal.HasRamseyProperty (Nat.choose n (s + 1)) (s + 1 + 1) (t + 1 + 1)
      rw [hpascal]
      exact hrec

noncomputable def colorOfGraph {N : ℕ} (G : SimpleGraph (Fin N)) (e : Finset (Fin N)) : Bool :=
  decide (G.IsClique (e : Set (Fin N)))

theorem not_cliqueFree_of_hasRamseyProperty {N p m n : ℕ}
    (hR : Combinatorics.Diagonal.HasRamseyProperty N p m) (hN : N ≤ n)
    {G : SimpleGraph (Fin n)} (hG : LocallyDense p 1 G) : ¬ G.CliqueFree m := by
  have hcompl : Gᶜ.CliqueFree p := (locallyDense_one_iff_compl_cliqueFree G).mp hG
  have hV : N ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hN
  rcases hR (colorOfGraph G) Finset.univ hV with ⟨S, _, hScard, hSfalse⟩ | ⟨S, _, hScard, hStrue⟩
  · exfalso
    apply hcompl S
    refine ⟨?_, hScard⟩
    intro a ha b hb hab
    refine (SimpleGraph.compl_adj G a b).mpr ⟨hab, ?_⟩
    intro hadj
    have hc : colorOfGraph G {a, b} = false :=
      hSfalse {a, b} (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)) (Finset.card_pair hab)
    have hcl : G.IsClique ({a, b} : Set (Fin n)) :=
      SimpleGraph.isClique_pair.mpr (fun _ => hadj)
    simp [colorOfGraph, hcl] at hc
  · intro hcf
    apply hcf S
    refine ⟨?_, hScard⟩
    intro a ha b hb hab
    have hc : colorOfGraph G {a, b} = true :=
      hStrue {a, b} (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)) (Finset.card_pair hab)
    have hcl : G.IsClique (({a, b} : Finset (Fin n)) : Set (Fin n)) := by
      simpa only [colorOfGraph, decide_eq_true_eq] using hc
    exact hcl (by simp) (by simp) hab

theorem erdos_szekeres_le_H_one {p m n : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hchoose : Nat.choose (p - 1 + (m - 1)) (p - 1) ≤ n) :
    m ≤ H p 1 n := by
  have hR : Combinatorics.Diagonal.HasRamseyProperty
      (Nat.choose (p - 1 + (m - 1)) (p - 1)) p m := by
    have h1 : Combinatorics.Diagonal.HasRamseyProperty
        (Nat.choose (p - 1 + (m - 1)) (p - 1)) (p - 1 + 1) (m - 1 + 1) :=
      hasRamseyProperty_choose_succ (p - 1) (m - 1)
    have hp_eq : p - 1 + 1 = p := by omega
    have hm_eq : m - 1 + 1 = m := by omega
    rwa [hp_eq, hm_eq] at h1
  have h_all : ∀ G : SimpleGraph (Fin n), LocallyDense p 1 G → ¬ G.CliqueFree m :=
    fun G hG => not_cliqueFree_of_hasRamseyProperty hR hchoose hG
  have htop_dense : LocallyDense p 1 (⊤ : SimpleGraph (Fin n)) := by
    exact locallyDense_top_of_le_choose_two (Nat.choose_pos hp)
  have hmn : m ≤ n := le_card_of_not_cliqueFree (h_all ⊤ htop_dense)
  exact le_H_of_forall hmn h_all

theorem choose_add_le_pow : ∀ (s t : ℕ), Nat.choose (s + t) s ≤ (t + 1) ^ s
  | 0, t => by simp
  | s + 1, 0 => by simp
  | s + 1, t + 1 => by
    have h1 := choose_add_le_pow s (t + 1)
    have h2 := choose_add_le_pow (s + 1) t
    have hpascal : Nat.choose (s + 1 + (t + 1)) (s + 1) =
        Nat.choose (s + (t + 1)) s + Nat.choose (s + 1 + t) (s + 1) := by
      have : s + 1 + (t + 1) = (s + (t + 1)) + 1 := by omega
      have hsub : s + 1 + t = s + (t + 1) := by omega
      rw [this, hsub, Nat.choose_succ_succ]
    have hpow_mono : (t + 1) ^ s ≤ (t + 1 + 1) ^ s :=
      Nat.pow_le_pow_left (by omega) s
    have hpow_step : (t + 1 + 1) ^ s + (t + 1) ^ (s + 1) ≤ (t + 1 + 1) ^ (s + 1) := by
      calc (t + 1 + 1) ^ s + (t + 1) ^ (s + 1)
          = (t + 1 + 1) ^ s + (t + 1) ^ s * (t + 1) := by rw [pow_succ]
        _ ≤ (t + 1 + 1) ^ s + (t + 1 + 1) ^ s * (t + 1) := by gcongr
        _ = (t + 1 + 1) ^ s * (t + 1 + 1) := by ring
        _ = (t + 1 + 1) ^ (s + 1) := by rw [← pow_succ]
    omega

theorem pow_le_imp_le_H_one {p m n : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hpow : m ^ (p - 1) ≤ n) : m ≤ H p 1 n := by
  apply erdos_szekeres_le_H_one hp hm
  have h1 := choose_add_le_pow (p - 1) (m - 1)
  have hm_eq : m - 1 + 1 = m := by omega
  rw [hm_eq] at h1
  exact h1.trans hpow

theorem nat_le_two_mul_H_one_pow {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) :
    n ≤ (2 * H p 1 n) ^ (p - 1) := by
  have hlt : n < (H p 1 n + 1) ^ (p - 1) := by
    by_contra hge
    have hle : H p 1 n + 1 ≤ H p 1 n :=
      pow_le_imp_le_H_one hp (by omega) (Nat.le_of_not_lt hge)
    omega
  have hH1 : 1 ≤ H p 1 n := one_le_H hn
  have hbase : H p 1 n + 1 ≤ 2 * H p 1 n := by omega
  have hpow : (H p 1 n + 1) ^ (p - 1) ≤ (2 * H p 1 n) ^ (p - 1) :=
    Nat.pow_le_pow_left hbase (p - 1)
  omega

theorem ramsey_lower_bound_of_nat_pow_bound {p : ℕ} (hp : 2 ≤ p)
    (hH : ∀ n : ℕ, 1 ≤ n → n ≤ (2 * H p 1 n) ^ (p - 1)) :
    1 / ((p : ℝ) - 1) ≤ c p 1 := by
  by_contra! hlt
  let target : ℝ := 1 / ((p : ℝ) - 1)
  let ε : ℝ := (target - c p 1) / 2
  have hε : 0 < ε := by dsimp [ε, target]; linarith
  have hpm1_nat : 1 ≤ p - 1 := by omega
  have hpm1_eq : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hpm1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    rw [← hpm1_eq]
    positivity
  have h1 : target - ε ≤ c p 1 := by
    unfold c
    apply le_liminf_of_le (isCoboundedUnder_log_H p 1)
    let C : ℝ := Real.log 2
    let N : ℕ := Nat.ceil (Real.exp (C / ε)) + 2
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn2 : 2 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hH1 : 1 ≤ H p 1 n := one_le_H hn1
    have hH_pos : (0 : ℝ) < (H p 1 n : ℝ) := by positivity
    have h2H_pos : (0 : ℝ) < 2 * (H p 1 n : ℝ) := by positivity
    have hn_le_pow : (n : ℝ) ≤ (2 * (H p 1 n : ℝ)) ^ (p - 1) := by
      exact_mod_cast hH n hn1
    have hlog_pow : Real.log (n : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * (C + Real.log (H p 1 n : ℝ)) := by
      have h1 := Real.log_le_log (by positivity) hn_le_pow
      rw [Real.log_pow, Real.log_mul two_ne_zero (ne_of_gt hH_pos)] at h1
      exact h1
    rw [hpm1_eq, mul_comm] at hlog_pow
    have hdiv_le : Real.log (n : ℝ) / ((p : ℝ) - 1) - C ≤ Real.log (H p 1 n : ℝ) := by
      have := (div_le_iff₀ hpm1_pos).mpr hlog_pow
      linarith
    have hlogn_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hn2
    have hexp_le : Real.exp (C / ε) < (n : ℝ) := by
      have hceil : Real.exp (C / ε) ≤ (Nat.ceil (Real.exp (C / ε)) : ℝ) := Nat.le_ceil _
      have hcast : ((Nat.ceil (Real.exp (C / ε)) + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      push_cast at hcast
      linarith
    have hC_lt : C / ε < Real.log (n : ℝ) := by
      rw [← Real.lt_log_iff_exp_lt (by positivity)] at hexp_le
      exact hexp_le
    have hC_le_eps : C / Real.log (n : ℝ) ≤ ε := by
      rw [div_le_iff₀ hlogn_pos]
      have := (div_lt_iff₀ hε).mp hC_lt
      linarith
    calc target - ε ≤ target - C / Real.log (n : ℝ) := by linarith
      _ = (Real.log (n : ℝ) / ((p : ℝ) - 1) - C) / Real.log (n : ℝ) := by
        dsimp [target]
        rw [sub_div, div_right_comm, div_self (ne_of_gt hlogn_pos)]
      _ ≤ Real.log (H p 1 n : ℝ) / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hdiv_le (le_of_lt hlogn_pos)
  dsimp [ε] at h1
  linarith

/-- Universal Erdős–Szekeres Ramsey lower bound for `c(p, 1)` (and all `c(p, q)` with `q ≥ 1`):
for every `p ≥ 2`, `1 / (p - 1) ≤ c p 1`, unconditionally resolving the lower bound of
`erdos_667.variants.ramsey_bounds`. -/
theorem ramseyLowerBound (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ≤ c p 1 :=
  ramsey_lower_bound_of_nat_pow_bound hp (fun _ hn => nat_le_two_mul_H_one_pow hp hn)

theorem cGeInvPred {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    1 / ((p : ℝ) - 1) ≤ c p q :=
  (ramseyLowerBound p hp).trans (c_mono_q p hq)

def blockCliqueGraph (m n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.1 / m = v.1 / m
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem blockCliqueGraph_cliqueFree {m n : ℕ} (hm : 1 ≤ m) :
    (blockCliqueGraph m n).CliqueFree (m + 1) := by
  intro K hK
  have hK_card := hK.card_eq
  have hinj : Set.InjOn (fun v : Fin n => v.1 % m) (K : Set (Fin n)) := by
    intro u hu v hv huv
    by_contra hne
    have hadj : (blockCliqueGraph m n).Adj u v := hK.isClique hu hv hne
    have hdiv : u.1 / m = v.1 / m := hadj.2
    have hmod : u.1 % m = v.1 % m := huv
    have h1 := Nat.div_add_mod u.1 m
    have h2 := Nat.div_add_mod v.1 m
    apply hne
    ext
    rw [← h1, ← h2, hdiv, hmod]
  have hmaps : Set.MapsTo (fun v : Fin n => v.1 % m) (K : Set (Fin n)) (Finset.range m) := by
    intro v _
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.mod_lt v.1 hm
  have hcard := Finset.card_le_card_of_injOn (fun v : Fin n => v.1 % m) hmaps hinj
  simp only [Finset.card_range] at hcard
  omega

theorem blockCliqueGraph_locallyDense_one {p m n : ℕ} (hp : 2 ≤ p)
    (hn : n ≤ (p - 1) * m) :
    LocallyDense p 1 (blockCliqueGraph m n) := by
  rw [locallyDense_one_iff_compl_cliqueFree]
  intro K hK
  have hK_card := hK.card_eq
  have hinj : Set.InjOn (fun v : Fin n => v.1 / m) (K : Set (Fin n)) := by
    intro u hu v hv huv
    by_contra hne
    have hadj : (blockCliqueGraph m n)ᶜ.Adj u v := hK.isClique hu hv hne
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 ⟨hne, huv⟩
  have hmaps : Set.MapsTo (fun v : Fin n => v.1 / m)
      (K : Set (Fin n)) (Finset.range (p - 1)) := by
    intro v _
    simp only [Finset.mem_coe, Finset.mem_range]
    apply Nat.div_lt_of_lt_mul
    calc v.1 < n := v.2
      _ ≤ (p - 1) * m := hn
      _ = m * (p - 1) := Nat.mul_comm _ _
  have hcard := Finset.card_le_card_of_injOn (fun v : Fin n => v.1 / m) hmaps hinj
  simp only [Finset.card_range] at hcard
  omega

theorem H_one_le_of_le_pred_mul {p m n : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hn : n ≤ (p - 1) * m) : H p 1 n ≤ m := by
  by_contra hgt
  have hle : m + 1 ≤ H p 1 n := by omega
  have hnot := H_spec (blockCliqueGraph m n) (blockCliqueGraph_locallyDense_one hp hn)
  exact hnot ((blockCliqueGraph_cliqueFree hm).mono hle)

theorem H_one_eq_two_of_le_two_mul_pred {p n : ℕ} (hp : 2 ≤ p) (hpn : p ≤ n)
    (hn : n ≤ 2 * (p - 1)) : H p 1 n = 2 := by
  apply le_antisymm
  · apply H_one_le_of_le_pred_mul hp (by omega)
    omega
  · apply erdos_szekeres_le_H_one hp (by omega)
    change Nat.choose (p - 1 + 1) (p - 1) ≤ n
    rw [Nat.choose_succ_self_right (p - 1)]
    omega

theorem H_three_one_six : H 3 1 6 = 3 := by
  apply le_antisymm
  · exact H_one_le_of_le_pred_mul (by omega) (by omega) (by omega)
  · exact erdos_szekeres_le_H_one (by omega) (by omega) (by decide)

end Erdos667.Core
end
