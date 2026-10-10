module

/-
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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Image
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.FinCases
public import PathLowerAndSmallCases

@[expose] public section

/-!
# PathResidualDecomposition

Erdős–Gallai path/cycle bounds, Lemma 4 scalar envelopes, eligible interior representative choices, bridge cuts, residual greedy recursion, and global cut-family ledgers for Erdős Problem 1105.
-/

namespace ErdosProblems.PathUpperDenseDisconnectedBridgeBound

open SimpleGraph

theorem choose_three_positive
    (s t u : ℕ) (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) :
    s.choose 2 + t.choose 2 + u.choose 2 ≤ (s + t + u - 2).choose 2 := by
  let x := s - 1
  let y := t - 1
  let z := u - 1
  have hsx : s = x + 1 := by dsimp [x]; omega
  have hty : t = y + 1 := by dsimp [y]; omega
  have huz : u = z + 1 := by dsimp [z]; omega
  have hshift : s + t + u - 2 = x + y + z + 1 := by omega
  have hx : (x + 1) * x = (x + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq x 1
  have hy : (y + 1) * y = (y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq y 1
  have hz : (z + 1) * z = (z + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq z 1
  have hxyz : (x + y + z + 1) * (x + y + z) =
      (x + y + z + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq (x + y + z) 1
  rw [hshift, hsx, hty, huz]
  nlinarith [Nat.zero_le (x * y), Nat.zero_le (x * z), Nat.zero_le (y * z)]

/-- A disconnected graph on `k` vertices with an actual bridge has at most
`choose (k - 2) 2 + 1` edges. Membership in the original edge set is essential:
Mathlib's `IsBridge` also holds for some absent pairs. -/
theorem edge_card_le_of_disconnected_actual_bridge
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hdis : ¬ G.Connected) (f : Sym2 (Fin k))
    (hf : f ∈ G.edgeSet) (hbridge : G.IsBridge f) :
    G.edgeFinset.card ≤ (k - 2).choose 2 + 1 := by
  classical
  revert hf hbridge
  refine Sym2.inductionOn f ?_
  intro a b hf hbridge
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin k)))
  have hle : D ≤ G := G.deleteEdges_le _
  have hab : G.Adj a b := G.mem_edgeSet.mp hf
  have hsep : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  let S : Finset (Fin k) := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset (Fin k) := Finset.univ.filter (fun x => D.Reachable b x)
  let U : Finset (Fin k) := Finset.univ \ (S ∪ T)
  have hS (x : Fin k) : x ∈ S ↔ D.Reachable a x := by simp [S]
  have hT (x : Fin k) : x ∈ T ↔ D.Reachable b x := by simp [T]
  have hU (x : Fin k) : x ∈ U ↔ x ∉ S ∧ x ∉ T := by simp [U]
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact hsep (((hS x).mp hxS).trans ((hT x).mp hxT).symm)
  have hSTU : Disjoint (S ∪ T) U := Finset.disjoint_sdiff
  have hparts : (S ∪ T) ∪ U = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsum : S.card + T.card + U.card = k := by
    calc
      S.card + T.card + U.card = (S ∪ T).card + U.card := by
        rw [Finset.card_union_of_disjoint hST]
      _ = ((S ∪ T) ∪ U).card := (Finset.card_union_of_disjoint hSTU).symm
      _ = k := by simp only [hparts, Finset.card_univ, Fintype.card_fin]
  have hSpos : 0 < S.card :=
    Finset.card_pos.mpr ⟨a, (hS a).mpr (SimpleGraph.Reachable.refl _)⟩
  have hTpos : 0 < T.card :=
    Finset.card_pos.mpr ⟨b, (hT b).mpr (SimpleGraph.Reachable.refl _)⟩
  have hzexists : ∃ z : Fin k, ¬ G.Reachable a z := by
    by_contra hz
    apply hdis
    apply (G.connected_iff_exists_forall_reachable).mpr
    refine ⟨a, ?_⟩
    intro z
    by_contra haz
    exact hz ⟨z, haz⟩
  obtain ⟨z, haz⟩ := hzexists
  have hzS : z ∉ S := by
    intro hzS
    exact haz (SimpleGraph.Reachable.mono hle ((hS z).mp hzS))
  have hzT : z ∉ T := by
    intro hzT
    exact haz (hab.reachable.trans (SimpleGraph.Reachable.mono hle ((hT z).mp hzT)))
  have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨z, (hU z).mpr ⟨hzS, hzT⟩⟩
  have hSclosed : ∀ {x y : Fin k}, D.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    exact (hS y).mpr (((hS x).mp hx).trans hxy.reachable)
  have hTclosed : ∀ {x y : Fin k}, D.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    exact (hT y).mpr (((hT x).mp hx).trans hxy.reachable)
  have hUclosed : ∀ {x y : Fin k}, D.Adj x y → x ∈ U → y ∈ U := by
    intro x y hxy hx
    obtain ⟨hxS, hxT⟩ := (hU x).mp hx
    apply (hU y).mpr
    constructor
    · intro hyS
      exact hxS (hSclosed hxy.symm hyS)
    · intro hyT
      exact hxT (hTclosed hxy.symm hyT)
  let ES := D.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := D.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  let EU := D.edgeFinset.filter (fun e => e.toFinset ⊆ U)
  have hcover : D.edgeFinset ⊆ (ES ∪ ET) ∪ EU := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : D.Adj x y := D.mem_edgeSet.mp (D.mem_edgeFinset.mp he)
    by_cases hxS : x ∈ S
    · have hsub : s(x, y).toFinset ⊆ S := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxS (hSclosed hxy hxS)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨he, hsub⟩))))
    · by_cases hxT : x ∈ T
      · have hsub : s(x, y).toFinset ⊆ T := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxT (hTclosed hxy hxT)
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))))
      · have hxU : x ∈ U := (hU x).mpr ⟨hxS, hxT⟩
        have hsub : s(x, y).toFinset ⊆ U := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxU (hUclosed hxy hxU)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))
  have hES : ES.card ≤ S.card.choose 2 := by
    calc
      ES.card = (D.induce (↑S : Set (Fin k))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) S
      _ ≤ (Fintype.card S).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑S : Set (Fin k)))
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hET : ET.card ≤ T.card.choose 2 := by
    calc
      ET.card = (D.induce (↑T : Set (Fin k))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) T
      _ ≤ (Fintype.card T).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑T : Set (Fin k)))
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hEU : EU.card ≤ U.card.choose 2 := by
    calc
      EU.card = (D.induce (↑U : Set (Fin k))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) U
      _ ≤ (Fintype.card U).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑U : Set (Fin k)))
      _ = U.card.choose 2 := by rw [Fintype.card_coe]
  have hDcap : D.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 := by
    calc
      D.edgeFinset.card ≤ ((ES ∪ ET) ∪ EU).card := Finset.card_le_card hcover
      _ ≤ (ES ∪ ET).card + EU.card := Finset.card_union_le (ES ∪ ET) EU
      _ ≤ ES.card + ET.card + EU.card :=
        Nat.add_le_add_right (Finset.card_union_le ES ET) EU.card
      _ ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 := by omega
  have hchoose : S.card.choose 2 + T.card.choose 2 + U.card.choose 2 ≤ (k - 2).choose 2 := by
    simpa only [hsum] using choose_three_positive S.card T.card U.card hSpos hTpos hUpos
  have hdelete : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, Finset.coe_erase, D, SimpleGraph.edgeSet_deleteEdges]
  have hedge : D.edgeFinset.card + 1 = G.edgeFinset.card := by
    rw [hdelete]
    exact Finset.card_erase_add_one (G.mem_edgeFinset.mpr hf)
  omega

/-- In a disconnected graph above the bridge bound, every actual edge is a nonbridge. -/
theorem actual_edge_not_bridge_of_dense_disconnected
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hdis : ¬ G.Connected) (hdense : (k - 2).choose 2 + 2 ≤ G.edgeFinset.card) :
    ∀ f ∈ G.edgeSet, ¬ G.IsBridge f := by
  intro f hf hbridge
  have hcap := edge_card_le_of_disconnected_actual_bridge G hdis f hf hbridge
  omega

end ErdosProblems.PathUpperDenseDisconnectedBridgeBound

namespace ErdosProblems.PathLemmaFourScalar

/-- The polynomial expression for a binomial coefficient of order two. -/
noncomputable def q (x : ℝ) : ℝ := x * (x - 1) / 2

/-- Transparent natural-number version of the published h expression. -/
def h (v p j : ℕ) : ℕ :=
  (p - j).choose 2 + j * (v - p + j)

/-- Clique cap below the forbidden path order; maximum-h cap above it. -/
def scalarCap (p v : ℕ) : ℕ :=
  if v ≤ p then v.choose 2 else max (h v p 1) (h v p ((p - 1) / 2))

/-- Exactly the natural choose/div/parity maximum in FC1105 part ii. -/
def pathFormula (n k : ℕ) : ℕ :=
  let ℓ := (k - 1) / 2
  let ε := if Odd k then 1 else 2
  max ((k - 2).choose 2 + 1)
    ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)

noncomputable def capR (P V B : ℝ) : ℝ :=
  if V ≤ P then q V
  else max (q (P - 1) + (V - P + 1))
    (q (P - B) + B * (V - P + B))

theorem cast_sub_eq (x y : ℕ) (hy : y ≤ x) :
    ((x - y : ℕ) : ℝ) = (x : ℝ) - (y : ℝ) := by
  have hn : (x - y) + y = x := by omega
  have hr : ((x - y : ℕ) : ℝ) + (y : ℝ) = (x : ℝ) := by
    exact_mod_cast hn
  linarith

theorem choose_cast (n : ℕ) :
    (n.choose 2 : ℝ) = q (n : ℝ) := by
  exact Nat.cast_choose_two ℝ n

theorem nonneg_of_pos_mul (x y : ℝ) (hx : 0 < x) (hxy : 0 ≤ x * y) :
    0 ≤ y := by
  by_contra hn
  have hy : y < 0 := lt_of_not_ge hn
  have hbad : x * y < 0 := mul_neg_of_pos_of_neg hx hy
  exact (not_lt_of_ge hxy) hbad

theorem h_cast (v p j : ℕ) (hj : j ≤ p) (hv : p ≤ v) :
    (h v p j : ℝ) =
      q ((p : ℝ) - (j : ℝ)) +
        (j : ℝ) * ((v : ℝ) - (p : ℝ) + (j : ℝ)) := by
  simp only [h, Nat.cast_add, Nat.cast_mul, choose_cast]
  rw [cast_sub_eq p j hj, cast_sub_eq v p hv]

theorem cap_cast (p v : ℕ) (hp : 2 ≤ p) (hv : p ≤ v) :
    (scalarCap p v : ℝ) =
      capR (p : ℝ) (v : ℝ) (((p - 1) / 2 : ℕ) : ℝ) := by
  have hb : (p - 1) / 2 ≤ p := by omega
  by_cases hle : v ≤ p
  · have hleR : (v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    simp only [scalarCap, capR, ite_eq_left hle, ite_eq_left hleR, choose_cast]
  · have hleR : ¬(v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    simp only [scalarCap, capR, ite_eq_right hle, ite_eq_right hleR, Nat.cast_max]
    rw [h_cast v p 1 (by omega) hv, h_cast v p ((p - 1) / 2) hb hv]
    simp only [Nat.cast_one, one_mul]

theorem formula_cast (p d N : ℕ) (hpd : d ≤ p) (hd : 2 ≤ d)
    (hN : p + d + 1 ≤ N) :
    (pathFormula N (p + d + 1) : ℝ) =
      max (q ((p : ℝ) + (d : ℝ) - 1) + 1)
        (((((p + d - 2) / 2 : ℕ) : ℝ)) * (N : ℝ) -
          q (((((p + d - 2) / 2 : ℕ) : ℝ)) + 1) +
          (1 + (((p + d - 2) % 2 : ℕ) : ℝ))) := by
  let a : ℕ := (p + d - 2) / 2
  let δ : ℕ := (p + d - 2) % 2
  have hk : p + d + 1 - 2 = p + d - 1 := by omega
  have he : (p + d + 1 - 1) / 2 - 1 = a := by dsimp [a]; omega
  have hn : N - (p + d + 1 - 1) / 2 + 1 = N - a := by
    dsimp [a]
    omega
  have haN : a ≤ N := by dsimp [a]; omega
  have hε : (if Odd (p + d + 1) then (1 : ℕ) else 2) = 1 + δ := by
    split_ifs with ho
    · have hm := Nat.odd_iff.mp ho
      dsimp [δ]
      omega
    · have hm := Nat.not_odd_iff.mp ho
      dsimp [δ]
      omega
  have hnat : pathFormula N (p + d + 1) =
      max ((p + d - 1).choose 2 + 1)
        (a.choose 2 + a * (N - a) + (1 + δ)) := by
    dsimp only [pathFormula]
    rw [hk, he, hn, hε]
  rw [hnat, Nat.cast_max]
  congr 1
  · rw [Nat.cast_add, choose_cast, Nat.cast_one,
      cast_sub_eq (p + d) 1 (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, choose_cast]
    rw [cast_sub_eq N a haN]
    change q (a : ℝ) + (a : ℝ) * ((N : ℝ) - (a : ℝ)) +
      (1 + (δ : ℝ)) =
      (a : ℝ) * (N : ℝ) - q ((a : ℝ) + 1) + (1 + (δ : ℝ))
    dsimp [q]
    ring

/-- The uniform real-algebra layer; floor information is supplied as exact identities. -/
theorem scalar_real (P D V S R a b δ η : ℝ)
    (hpd : D ≤ P) (hd : 2 ≤ D) (hv : P ≤ V) (hs : 0 ≤ S)
    (hr : 1 ≤ R) (hrd : R ≤ D) (hN : P + D + 1 ≤ V + S * D + R)
    (ha : 0 < a) (hda : D - 1 ≤ a) (hba : b ≤ a) (hb : 0 ≤ b)
    (hz : P + D = 2 * a + 2 + δ) (hp : P = 2 * b + 1 + η)
    (hδ : δ = 0 ∨ δ = 1) (hη : η = 0 ∨ η = 1) :
    capR P V b + S * (q D + 1) + q R ≤
      max (q (P + D - 1) + 1)
        (a * (V + S * D + R) - q (a + 1) + (1 + δ)) := by
  let u := S * D + R
  let N := V + S * D + R
  let c := (D - 1) / 2 + 1 / D
  let first := q (P + D - 1) + 1
  let lin := fun x : ℝ => a * x - q (a + 1) + (1 + δ)
  let q0 := fun x : ℝ => q P + c * (x - P)
  let qb := fun x : ℝ => b * x - q (b + 1) + η
  let nc := (5 * a + 3 + 4 * δ) / 2
  let T := (5 * (P + D) - 1) / 4
  let tail := S * (q D + 1) + q R
  have hdpos : 0 < D := by linarith
  have hdne : D ≠ 0 := ne_of_gt hdpos
  have hδ0 : 0 ≤ δ := by rcases hδ with h0 | h1 <;> linarith
  have hδ1 : δ ≤ 1 := by rcases hδ with h0 | h1 <;> linarith
  have hη0 : 0 ≤ η := by rcases hη with h0 | h1 <;> linarith
  have hη1 : η ≤ 1 := by rcases hη with h0 | h1 <;> linarith
  have hu : 0 ≤ u := by
    dsimp [u]
    nlinarith only [hr, mul_nonneg hs (le_of_lt hdpos)]
  have hdc : D * c = q D + 1 := by
    dsimp [c, q]
    field_simp [hdne]
  have hc1id : 2 * D * (c - 1) = (D - 1) * (D - 2) := by
    dsimp [c]
    field_simp [hdne]
    ring
  have hc1 : 1 ≤ c := by
    have hm : 0 ≤ (D - 1) * (D - 2) := mul_nonneg (by linarith) (by linarith)
    have hprod : 0 ≤ 2 * D * (c - 1) := by rw [hc1id]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) (c - 1) (by positivity) hprod
    linarith only [hsub]
  have hcdid : 2 * D * ((D - 1) - c) = (D - 2) * (D + 1) := by
    dsimp [c]
    field_simp [hdne]
    ring
  have hcd : c ≤ D - 1 := by
    have hm : 0 ≤ (D - 2) * (D + 1) := mul_nonneg (by linarith) (by linarith)
    have hprod : 0 ≤ 2 * D * ((D - 1) - c) := by rw [hcdid]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) ((D - 1) - c) (by positivity) hprod
    linarith only [hsub]
  have hca : c ≤ a := hcd.trans hda
  have hc0 : 0 ≤ c := by linarith
  have hrid : 2 * D * (c * R - q R) = R * (D * (D - R) + 2) := by
    dsimp [c, q]
    field_simp [hdne]
    ring
  have hqr : q R ≤ c * R := by
    have hm : 0 ≤ R * (D * (D - R) + 2) :=
      mul_nonneg (by linarith only [hr])
        (by nlinarith only [mul_nonneg (le_of_lt hdpos) (sub_nonneg.mpr hrd)])
    have hprod : 0 ≤ 2 * D * (c * R - q R) := by rw [hrid]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) (c * R - q R) (by positivity) hprod
    linarith only [hsub]
  have ht : tail ≤ c * u := by
    calc
      tail = c * (S * D) + q R := by dsimp [tail]; rw [← hdc]; ring
      _ ≤ c * (S * D) + c * R := add_le_add_right hqr _
      _ = c * u := by dsimp [u]; ring
  have hintersection : first = lin nc := by
    dsimp [first, lin, nc]
    rw [hz]
    rcases hδ with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
  have hncT : nc ≤ T := by dsimp [nc, T]; linarith only [hz, hδ1]
  have hfactor :
      8 * D * (first - q0 T) =
        (P - D) * (7 * D * (D - 1) - 2) +
          (D - 2) * (6 * D ^ 2 - D + 1) + 4 := by
    dsimp [first, q0, T, c, q]
    field_simp [hdne]
    ring
  have hfpos : 0 < first - q0 T := by
    have hcoef : 0 ≤ 7 * D * (D - 1) - 2 := by
      nlinarith only [hd,
        mul_nonneg (by linarith : 0 ≤ D - 2) (by linarith : 0 ≤ D - 1)]
    have hpoly : 0 ≤ 6 * D ^ 2 - D + 1 := by
      nlinarith only [hd, sq_nonneg (D - 2)]
    have hright : 0 <
        (P - D) * (7 * D * (D - 1) - 2) +
          (D - 2) * (6 * D ^ 2 - D + 1) + 4 := by
      have hm1 := mul_nonneg (sub_nonneg.mpr hpd) hcoef
      have hm2 := mul_nonneg (by linarith : 0 ≤ D - 2) hpoly
      linarith
    have hprod : 0 < 8 * D * (first - q0 T) := by rw [hfactor]; exact hright
    by_contra hnot
    have hm : first - q0 T ≤ 0 := le_of_not_gt hnot
    have hbad := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 8 * D) hm
    linarith
  have hmid : q0 nc < first := by
    have hq : q0 nc ≤ q0 T := by
      dsimp [q0]
      nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hncT)]
    linarith only [hq, hfpos]
  have hq0 : q0 N ≤ max first (lin N) := by
    by_cases hsmall : N ≤ nc
    · have hq : q0 N ≤ q0 nc := by
        dsimp [q0]
        nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hsmall)]
      exact (hq.trans hmid.le).trans (le_max_left _ _)
    · have hmul : 0 ≤ (a - c) * (N - nc) :=
        mul_nonneg (sub_nonneg.mpr hca) (by linarith)
      have hi : lin N - q0 N =
          (lin nc - q0 nc) + (a - c) * (N - nc) := by
        dsimp [lin, q0]
        ring
      have hbase : 0 ≤ lin nc - q0 nc := by rw [← hintersection]; linarith
      have hq : q0 N ≤ lin N := by linarith only [hi, hmul, hbase]
      exact hq.trans (le_max_right _ _)
  have hqb : qb N ≤ max first (lin N) := by
    have hi : lin N - qb N =
        (a - b) * (N - (a + b + 1) / 2) + (1 + δ) - η := by
      dsimp [lin, qb, q]
      ring
    have hbracket : 0 ≤ N - (a + b + 1) / 2 := by
      dsimp [N]
      linarith only [hN, hz, hba, ha, hδ0]
    have hmul := mul_nonneg (sub_nonneg.mpr hba) hbracket
    have hq : qb N ≤ lin N := by linarith only [hi, hmul, hδ0, hη1]
    exact hq.trans (le_max_right _ _)
  have hbform (x : ℝ) :
      q (P - b) + b * (x - P + b) = b * x - q (b + 1) + η := by
    rw [hp]
    rcases hη with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
  have hbbase : q (P - b) + b * (P - P + b) ≤ q P := by
    have hi : q P - (q (P - b) + b * (P - P + b)) =
        b * (b + 1 + 2 * η) / 2 := by
      rw [hp]
      rcases hη with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
    have hm : 0 ≤ b * (b + 1 + 2 * η) := mul_nonneg hb (by linarith)
    nlinarith only [hi, hm]
  have hclique : q P + tail ≤ max first (lin N) := by
    calc
      q P + tail ≤ q P + c * u := add_le_add_right ht _
      _ ≤ q0 N := by
        dsimp [q0, N, u]
        nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hv)]
      _ ≤ max first (lin N) := hq0
  have hfirst : q (P - 1) + (V - P + 1) + tail ≤ max first (lin N) := by
    have hcore : q (P - 1) + (V - P + 1) ≤ q P + c * (V - P) := by
      have hm := mul_nonneg (by linarith : 0 ≤ c - 1) (sub_nonneg.mpr hv)
      dsimp [q]
      nlinarith only [hm, hd, hpd]
    calc
      q (P - 1) + (V - P + 1) + tail ≤ q P + c * (V - P) + c * u :=
        add_le_add hcore ht
      _ = q0 N := by dsimp [q0, N, u]; ring
      _ ≤ max first (lin N) := hq0
  have hsecond : q (P - b) + b * (V - P + b) + tail ≤ max first (lin N) := by
    by_cases hbc : b ≤ c
    · have hcore : q (P - b) + b * (V - P + b) ≤ q P + c * (V - P) := by
        have hm := mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hv)
        nlinarith only [hbbase, hm]
      calc
        q (P - b) + b * (V - P + b) + tail ≤ q P + c * (V - P) + c * u :=
          add_le_add hcore ht
        _ = q0 N := by dsimp [q0, N, u]; ring
        _ ≤ max first (lin N) := hq0
    · have htb : tail ≤ b * u :=
        ht.trans (mul_le_mul_of_nonneg_right (lt_of_not_ge hbc).le hu)
      calc
        q (P - b) + b * (V - P + b) + tail ≤
            q (P - b) + b * (V - P + b) + b * u := add_le_add_right htb _
        _ = qb N := by rw [hbform]; dsimp [qb, N, u]; ring
        _ ≤ max first (lin N) := hqb
  rw [add_assoc]
  change capR P V b + tail ≤ max first (lin N)
  by_cases hle : V ≤ P
  · have heq : V = P := le_antisymm hle hv
    simpa only [capR, heq, ite_eq_left (le_refl P)] using hclique
  · simp only [capR, ite_eq_right hle]
    rcases le_total (q (P - 1) + (V - P + 1))
        (q (P - b) + b * (V - P + b)) with hm | hm
    · rw [max_eq_right hm]
      exact hsecond
    · rw [max_eq_left hm]
      exact hfirst

/-- Exact pure scalar core (S), with natural choose/div/parity and FC's maximum.
No graph hypotheses or external mathematical axioms occur. -/
theorem scalar_core (p d v s r : ℕ) (hpd : d ≤ p) (hd : 2 ≤ d)
    (hv : p ≤ v) (hs : 0 ≤ s) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hN : p + d + 1 ≤ v + s * d + r) :
    scalarCap p v + s * (d.choose 2 + 1) + r.choose 2 ≤
      pathFormula (v + s * d + r) (p + d + 1) := by
  let a : ℕ := (p + d - 2) / 2
  let b : ℕ := (p - 1) / 2
  let δ : ℕ := (p + d - 2) % 2
  let η : ℕ := (p - 1) % 2
  have hz : p + d = 2 * a + 2 + δ := by dsimp [a, δ]; omega
  have hp : p = 2 * b + 1 + η := by dsimp [b, η]; omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hda : d - 1 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [b, a]; omega
  have hδ : δ = 0 ∨ δ = 1 := by dsimp [δ]; omega
  have hη : η = 0 ∨ η = 1 := by dsimp [η]; omega
  have hzR : (p : ℝ) + (d : ℝ) = 2 * (a : ℝ) + 2 + (δ : ℝ) := by
    exact_mod_cast hz
  have hpR : (p : ℝ) = 2 * (b : ℝ) + 1 + (η : ℝ) := by exact_mod_cast hp
  have hδR : (δ : ℝ) = 0 ∨ (δ : ℝ) = 1 := by
    rcases hδ with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hηR : (η : ℝ) = 0 ∨ (η : ℝ) = 1 := by
    rcases hη with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hdaR : (d : ℝ) - 1 ≤ (a : ℝ) := by
    have ht : d ≤ a + 1 := by
      calc
        d = (d - 1) + 1 := by omega
        _ ≤ a + 1 := Nat.add_le_add_right hda 1
    have htR : (d : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast ht
    linarith
  have hx := scalar_real (p : ℝ) (d : ℝ) (v : ℝ) (s : ℝ) (r : ℝ)
    (a : ℝ) (b : ℝ) (δ : ℝ) (η : ℝ)
    (by exact_mod_cast hpd) (by exact_mod_cast hd) (by exact_mod_cast hv)
    (by exact_mod_cast hs) (by exact_mod_cast hr) (by exact_mod_cast hrd)
    (by exact_mod_cast hN)
    (by
      have ht : 0 < a := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) ha
      exact_mod_cast ht) hdaR
    (by exact_mod_cast hba) (Nat.cast_nonneg b) hzR hpR hδR hηR
  have hcap := cap_cast p v (by omega) hv
  have hform := formula_cast p d (v + s * d + r) hpd hd hN
  have hcast :
      (scalarCap p v + s * (d.choose 2 + 1) + r.choose 2 : ℝ) ≤
        (pathFormula (v + s * d + r) (p + d + 1) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, choose_cast, hcap, hform]
      using hx
  exact_mod_cast hcast

end ErdosProblems.PathLemmaFourScalar

namespace ErdosProblems.PathLemmaFourEnvelope

/-- The polynomial expression for a binomial coefficient of order two. -/
noncomputable def q (x : ℝ) : ℝ := x * (x - 1) / 2

/-- Transparent natural-number version of the published h expression. -/
def h (v p j : ℕ) : ℕ :=
  (p - j).choose 2 + j * (v - p + j)

/-- Clique cap below the forbidden path order; maximum-h cap above it. -/
def scalarCap (p v : ℕ) : ℕ :=
  if v ≤ p then v.choose 2 else max (h v p 1) (h v p ((p - 1) / 2))

/-- Exactly the natural choose/div/parity maximum in FC1105 part ii. -/
def pathFormula (n k : ℕ) : ℕ :=
  let ℓ := (k - 1) / 2
  let ε := if Odd k then 1 else 2
  max ((k - 2).choose 2 + 1)
    ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)

noncomputable def capR (P V B : ℝ) : ℝ :=
  if V ≤ P then q V
  else max (q (P - 1) + (V - P + 1))
    (q (P - B) + B * (V - P + B))

theorem cast_sub_eq (x y : ℕ) (hy : y ≤ x) :
    ((x - y : ℕ) : ℝ) = (x : ℝ) - (y : ℝ) := by
  have hn : (x - y) + y = x := by omega
  have hr : ((x - y : ℕ) : ℝ) + (y : ℝ) = (x : ℝ) := by
    exact_mod_cast hn
  linarith

theorem choose_cast (n : ℕ) :
    (n.choose 2 : ℝ) = q (n : ℝ) := by
  exact Nat.cast_choose_two ℝ n

theorem nonneg_of_pos_mul (x y : ℝ) (hx : 0 < x) (hxy : 0 ≤ x * y) :
    0 ≤ y := by
  by_contra hn
  have hy : y < 0 := lt_of_not_ge hn
  have hbad : x * y < 0 := mul_neg_of_pos_of_neg hx hy
  exact (not_lt_of_ge hxy) hbad

theorem h_cast (v p j : ℕ) (hj : j ≤ p) (hv : p ≤ v) :
    (h v p j : ℝ) =
      q ((p : ℝ) - (j : ℝ)) +
        (j : ℝ) * ((v : ℝ) - (p : ℝ) + (j : ℝ)) := by
  simp only [h, Nat.cast_add, Nat.cast_mul, choose_cast]
  rw [cast_sub_eq p j hj, cast_sub_eq v p hv]

theorem cap_cast (p v : ℕ) (hp : 2 ≤ p) (hv : p ≤ v) :
    (scalarCap p v : ℝ) =
      capR (p : ℝ) (v : ℝ) (((p - 1) / 2 : ℕ) : ℝ) := by
  have hb : (p - 1) / 2 ≤ p := by omega
  by_cases hle : v ≤ p
  · have hleR : (v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    simp only [scalarCap, capR, ite_eq_left hle, ite_eq_left hleR, choose_cast]
  · have hleR : ¬(v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
    simp only [scalarCap, capR, ite_eq_right hle, ite_eq_right hleR, Nat.cast_max]
    rw [h_cast v p 1 (by omega) hv, h_cast v p ((p - 1) / 2) hb hv]
    simp only [Nat.cast_one, one_mul]

theorem formula_cast (p d N : ℕ) (hpd : d ≤ p) (hd : 2 ≤ d)
    (hN : p + d + 1 ≤ N) :
    (pathFormula N (p + d + 1) : ℝ) =
      max (q ((p : ℝ) + (d : ℝ) - 1) + 1)
        (((((p + d - 2) / 2 : ℕ) : ℝ)) * (N : ℝ) -
          q (((((p + d - 2) / 2 : ℕ) : ℝ)) + 1) +
          (1 + (((p + d - 2) % 2 : ℕ) : ℝ))) := by
  let a : ℕ := (p + d - 2) / 2
  let δ : ℕ := (p + d - 2) % 2
  have hk : p + d + 1 - 2 = p + d - 1 := by omega
  have he : (p + d + 1 - 1) / 2 - 1 = a := by dsimp [a]; omega
  have hn : N - (p + d + 1 - 1) / 2 + 1 = N - a := by
    dsimp [a]
    omega
  have haN : a ≤ N := by dsimp [a]; omega
  have hε : (if Odd (p + d + 1) then (1 : ℕ) else 2) = 1 + δ := by
    split_ifs with ho
    · have hm := Nat.odd_iff.mp ho
      dsimp [δ]
      omega
    · have hm := Nat.not_odd_iff.mp ho
      dsimp [δ]
      omega
  have hnat : pathFormula N (p + d + 1) =
      max ((p + d - 1).choose 2 + 1)
        (a.choose 2 + a * (N - a) + (1 + δ)) := by
    dsimp only [pathFormula]
    rw [hk, he, hn, hε]
  rw [hnat, Nat.cast_max]
  congr 1
  · rw [Nat.cast_add, choose_cast, Nat.cast_one,
      cast_sub_eq (p + d) 1 (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, choose_cast]
    rw [cast_sub_eq N a haN]
    change q (a : ℝ) + (a : ℝ) * ((N : ℝ) - (a : ℝ)) +
      (1 + (δ : ℝ)) =
      (a : ℝ) * (N : ℝ) - q ((a : ℝ) + 1) + (1 + (δ : ℝ))
    dsimp [q]
    ring

/-- Uniform affine domination for arbitrary nonnegative real tail size. -/
theorem scalar_affine_real (P D V U a b δ η : ℝ)
    (hpd : D ≤ P) (hd : 2 ≤ D) (hv : P ≤ V) (hU : 0 ≤ U)
    (hN : P + D + 1 ≤ V + U)
    (ha : 0 < a) (hda : D - 1 ≤ a) (hba : b ≤ a) (hb : 0 ≤ b)
    (hz : P + D = 2 * a + 2 + δ) (hp : P = 2 * b + 1 + η)
    (hδ : δ = 0 ∨ δ = 1) (hη : η = 0 ∨ η = 1) :
    capR P V b + ((D - 1) / 2 + 1 / D) * U ≤
      max (q (P + D - 1) + 1)
        (a * (V + U) - q (a + 1) + (1 + δ)) := by
  let N := V + U
  let c := (D - 1) / 2 + 1 / D
  let first := q (P + D - 1) + 1
  let lin := fun x : ℝ => a * x - q (a + 1) + (1 + δ)
  let q0 := fun x : ℝ => q P + c * (x - P)
  let qb := fun x : ℝ => b * x - q (b + 1) + η
  let nc := (5 * a + 3 + 4 * δ) / 2
  let T := (5 * (P + D) - 1) / 4
  have hdpos : 0 < D := by linarith
  have hdne : D ≠ 0 := ne_of_gt hdpos
  have hδ0 : 0 ≤ δ := by rcases hδ with h0 | h1 <;> linarith
  have hδ1 : δ ≤ 1 := by rcases hδ with h0 | h1 <;> linarith
  have hη0 : 0 ≤ η := by rcases hη with h0 | h1 <;> linarith
  have hη1 : η ≤ 1 := by rcases hη with h0 | h1 <;> linarith
  have hc1id : 2 * D * (c - 1) = (D - 1) * (D - 2) := by
    dsimp [c]
    field_simp [hdne]
    ring
  have hc1 : 1 ≤ c := by
    have hm : 0 ≤ (D - 1) * (D - 2) := mul_nonneg (by linarith) (by linarith)
    have hprod : 0 ≤ 2 * D * (c - 1) := by rw [hc1id]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) (c - 1) (by positivity) hprod
    linarith only [hsub]
  have hcdid : 2 * D * ((D - 1) - c) = (D - 2) * (D + 1) := by
    dsimp [c]
    field_simp [hdne]
    ring
  have hcd : c ≤ D - 1 := by
    have hm : 0 ≤ (D - 2) * (D + 1) := mul_nonneg (by linarith) (by linarith)
    have hprod : 0 ≤ 2 * D * ((D - 1) - c) := by rw [hcdid]; exact hm
    have hsub := nonneg_of_pos_mul (2 * D) ((D - 1) - c) (by positivity) hprod
    linarith only [hsub]
  have hca : c ≤ a := hcd.trans hda
  have hc0 : 0 ≤ c := by linarith
  have hintersection : first = lin nc := by
    dsimp [first, lin, nc]
    rw [hz]
    rcases hδ with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
  have hncT : nc ≤ T := by dsimp [nc, T]; linarith only [hz, hδ1]
  have hfactor :
      8 * D * (first - q0 T) =
        (P - D) * (7 * D * (D - 1) - 2) +
          (D - 2) * (6 * D ^ 2 - D + 1) + 4 := by
    dsimp [first, q0, T, c, q]
    field_simp [hdne]
    ring
  have hfpos : 0 < first - q0 T := by
    have hcoef : 0 ≤ 7 * D * (D - 1) - 2 := by
      nlinarith only [hd,
        mul_nonneg (by linarith : 0 ≤ D - 2) (by linarith : 0 ≤ D - 1)]
    have hpoly : 0 ≤ 6 * D ^ 2 - D + 1 := by
      nlinarith only [hd, sq_nonneg (D - 2)]
    have hright : 0 <
        (P - D) * (7 * D * (D - 1) - 2) +
          (D - 2) * (6 * D ^ 2 - D + 1) + 4 := by
      have hm1 := mul_nonneg (sub_nonneg.mpr hpd) hcoef
      have hm2 := mul_nonneg (by linarith : 0 ≤ D - 2) hpoly
      linarith
    have hprod : 0 < 8 * D * (first - q0 T) := by rw [hfactor]; exact hright
    by_contra hnot
    have hm : first - q0 T ≤ 0 := le_of_not_gt hnot
    have hbad := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 8 * D) hm
    linarith
  have hmid : q0 nc < first := by
    have hq : q0 nc ≤ q0 T := by
      dsimp [q0]
      nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hncT)]
    linarith only [hq, hfpos]
  have hq0 : q0 N ≤ max first (lin N) := by
    by_cases hsmall : N ≤ nc
    · have hq : q0 N ≤ q0 nc := by
        dsimp [q0]
        nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hsmall)]
      exact (hq.trans hmid.le).trans (le_max_left _ _)
    · have hmul : 0 ≤ (a - c) * (N - nc) :=
        mul_nonneg (sub_nonneg.mpr hca) (by linarith)
      have hi : lin N - q0 N =
          (lin nc - q0 nc) + (a - c) * (N - nc) := by
        dsimp [lin, q0]
        ring
      have hbase : 0 ≤ lin nc - q0 nc := by rw [← hintersection]; linarith
      have hq : q0 N ≤ lin N := by linarith only [hi, hmul, hbase]
      exact hq.trans (le_max_right _ _)
  have hqb : qb N ≤ max first (lin N) := by
    have hi : lin N - qb N =
        (a - b) * (N - (a + b + 1) / 2) + (1 + δ) - η := by
      dsimp [lin, qb, q]
      ring
    have hbracket : 0 ≤ N - (a + b + 1) / 2 := by
      dsimp [N]
      linarith only [hN, hz, hba, ha, hδ0]
    have hmul := mul_nonneg (sub_nonneg.mpr hba) hbracket
    have hq : qb N ≤ lin N := by linarith only [hi, hmul, hδ0, hη1]
    exact hq.trans (le_max_right _ _)
  have hbform (x : ℝ) :
      q (P - b) + b * (x - P + b) = b * x - q (b + 1) + η := by
    rw [hp]
    rcases hη with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
  have hbbase : q (P - b) + b * (P - P + b) ≤ q P := by
    have hi : q P - (q (P - b) + b * (P - P + b)) =
        b * (b + 1 + 2 * η) / 2 := by
      rw [hp]
      rcases hη with h0 | h0 <;> rw [h0] <;> dsimp [q] <;> ring
    have hm : 0 ≤ b * (b + 1 + 2 * η) := mul_nonneg hb (by linarith)
    nlinarith only [hi, hm]
  have hclique : q P + c * U ≤ max first (lin N) := by
    calc
      q P + c * U ≤ q0 N := by
        dsimp [q0, N]
        nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hv)]
      _ ≤ max first (lin N) := hq0
  have hfirst : q (P - 1) + (V - P + 1) + c * U ≤ max first (lin N) := by
    have hcore : q (P - 1) + (V - P + 1) ≤ q P + c * (V - P) := by
      have hm := mul_nonneg (by linarith : 0 ≤ c - 1) (sub_nonneg.mpr hv)
      dsimp [q]
      nlinarith only [hm, hd, hpd]
    calc
      q (P - 1) + (V - P + 1) + c * U ≤ q P + c * (V - P) + c * U :=
        add_le_add_left hcore _
      _ = q0 N := by dsimp [q0, N]; ring
      _ ≤ max first (lin N) := hq0
  have hsecond : q (P - b) + b * (V - P + b) + c * U ≤ max first (lin N) := by
    by_cases hbc : b ≤ c
    · have hcore : q (P - b) + b * (V - P + b) ≤ q P + c * (V - P) := by
        have hm := mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hv)
        nlinarith only [hbbase, hm]
      calc
        q (P - b) + b * (V - P + b) + c * U ≤ q P + c * (V - P) + c * U :=
          add_le_add_left hcore _
        _ = q0 N := by dsimp [q0, N]; ring
        _ ≤ max first (lin N) := hq0
    · have hcb : c * U ≤ b * U :=
        mul_le_mul_of_nonneg_right (lt_of_not_ge hbc).le hU
      calc
        q (P - b) + b * (V - P + b) + c * U ≤
            q (P - b) + b * (V - P + b) + b * U := add_le_add_right hcb _
        _ = qb N := by rw [hbform]; dsimp [qb, N]; ring
        _ ≤ max first (lin N) := hqb
  change capR P V b + c * U ≤ max first (lin N)
  by_cases hle : V ≤ P
  · have heq : V = P := le_antisymm hle hv
    simpa only [capR, heq, ite_eq_left (le_refl P)] using hclique
  · simp only [capR, ite_eq_right hle]
    rcases le_total (q (P - 1) + (V - P + 1))
        (q (P - b) + b * (V - P + b)) with hm | hm
    · rw [max_eq_right hm]
      exact hsecond
    · rw [max_eq_left hm]
      exact hfirst

/-- Direct uniform affine envelope for every natural tail size u.
The exact natural choose/div/parity formula is retained. No specific tail
decomposition, remainder premise, graph theorem or supplied envelope occurs. -/
theorem scalar_affine_envelope (p d v u : ℕ)
    (hpd : d ≤ p) (hd : 2 ≤ d) (hv : p ≤ v)
    (hN : p + d + 1 ≤ v + u) :
    (scalarCap p v : ℝ) +
      (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (u : ℝ) ≤
        (pathFormula (v + u) (p + d + 1) : ℝ) := by
  let a : ℕ := (p + d - 2) / 2
  let b : ℕ := (p - 1) / 2
  let δ : ℕ := (p + d - 2) % 2
  let η : ℕ := (p - 1) % 2
  have hz : p + d = 2 * a + 2 + δ := by dsimp [a, δ]; omega
  have hp : p = 2 * b + 1 + η := by dsimp [b, η]; omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hda : d - 1 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [b, a]; omega
  have hδ : δ = 0 ∨ δ = 1 := by dsimp [δ]; omega
  have hη : η = 0 ∨ η = 1 := by dsimp [η]; omega
  have hzR : (p : ℝ) + (d : ℝ) = 2 * (a : ℝ) + 2 + (δ : ℝ) := by
    exact_mod_cast hz
  have hpR : (p : ℝ) = 2 * (b : ℝ) + 1 + (η : ℝ) := by exact_mod_cast hp
  have hδR : (δ : ℝ) = 0 ∨ (δ : ℝ) = 1 := by
    rcases hδ with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hηR : (η : ℝ) = 0 ∨ (η : ℝ) = 1 := by
    rcases hη with h0 | h1
    · left; exact_mod_cast h0
    · right; exact_mod_cast h1
  have hdaR : (d : ℝ) - 1 ≤ (a : ℝ) := by
    have ht : d ≤ a + 1 := by
      calc
        d = (d - 1) + 1 := by omega
        _ ≤ a + 1 := Nat.add_le_add_right hda 1
    have htR : (d : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast ht
    linarith
  have hx := scalar_affine_real (p : ℝ) (d : ℝ) (v : ℝ) (u : ℝ)
    (a : ℝ) (b : ℝ) (δ : ℝ) (η : ℝ)
    (by exact_mod_cast hpd) (by exact_mod_cast hd) (by exact_mod_cast hv)
    (Nat.cast_nonneg u) (by exact_mod_cast hN)
    (by
      have ht : 0 < a := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) ha
      exact_mod_cast ht) hdaR
    (by exact_mod_cast hba) (Nat.cast_nonneg b) hzR hpR hδR hηR
  have hcap := cap_cast p v (by omega) hv
  have hform := formula_cast p d (v + u) hpd hd hN
  simpa only [Nat.cast_add, hcap, hform] using hx

end ErdosProblems.PathLemmaFourEnvelope

namespace ErdosProblems.PathUpperReduction

open ErdosProblems.PathLemmaFourScalar

/-- The existing arbitrary-tail envelope bounds the all-short density in the
full host regime, without a path-order comparison or a supplied head cap. -/
theorem all_short_density_le_pathFormula (k n : ℕ)
    (hk : 6 ≤ k) (hkn : k ≤ n) :
    let d : ℕ := (k - 2) / 2
    (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (n : ℝ) ≤
      (pathFormula n k : ℝ) := by
  let d : ℕ := (k - 2) / 2
  let p : ℕ := k - d - 1
  let c : ℝ := ((d : ℝ) - 1) / 2 + 1 / (d : ℝ)
  change c * (n : ℝ) ≤ (pathFormula n k : ℝ)
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hdp : d + 1 ≤ p := by dsimp [p, d]; omega
  have hpk : p + d + 1 = k := by dsimp [p, d]; omega
  have hpn : p ≤ n := by omega
  have hsum : p + (n - p) = n := by omega
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpR : (d : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hdp
  have hinv : 1 / (d : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hdR
  have hc : c ≤ ((p : ℝ) - 1) / 2 := by
    dsimp [c]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have hchoose : c * (p : ℝ) ≤ (p.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two ℝ p]
    nlinarith only [hmul]
  have henv := ErdosProblems.PathLemmaFourEnvelope.scalar_affine_envelope
    p d p (n - p) (by omega) hd (le_refl p) (by omega)
  change (ErdosProblems.PathLemmaFourEnvelope.scalarCap p p : ℝ) +
      c * ((n - p : ℕ) : ℝ) ≤
    (pathFormula (p + (n - p)) (p + d + 1) : ℝ) at henv
  simp only [ErdosProblems.PathLemmaFourEnvelope.scalarCap,
    ite_eq_left (le_refl p)] at henv
  rw [hsum, hpk] at henv
  have hsub : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := Nat.cast_sub hpn
  rw [hsub] at henv
  calc
    c * (n : ℝ) = c * (p : ℝ) + c * ((n : ℝ) - (p : ℝ)) := by ring
    _ ≤ (p.choose 2 : ℝ) + c * ((n : ℝ) - (p : ℝ)) :=
      add_le_add hchoose (le_refl _)
    _ ≤ (pathFormula n k : ℝ) := henv

/-- An actual summed all-short charge implies the literal original numerical
upper bound. Deriving this charge from the actual component family is separate. -/
theorem all_short_color_count_le_pathFormula (k n q : ℕ)
    (hk : 6 ≤ k) (hkn : k ≤ n)
    (hcharge : let d : ℕ := (k - 2) / 2
      (q : ℝ) + 2 ≤
        (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (n : ℝ)) :
    q ≤ pathFormula n k := by
  have hdensity := all_short_density_le_pathFormula k n hk hkn
  have hreal : (q : ℝ) ≤ (pathFormula n k : ℝ) := by
    dsimp only at hcharge hdensity
    linarith
  exact_mod_cast hreal

/-- Literal k=5 formula in its full host domain. The separate actual no-edge
branch can use this identity without extending the d>=2 density envelope. -/
theorem pathFormula_five_eq_host (n : ℕ) (hn : 5 ≤ n) :
    pathFormula n 5 = n := by
  have hodd : Odd (5 : ℕ) := ⟨2, by decide⟩
  have hform : pathFormula n 5 = max 4 (n - 2 + 2) := by
    norm_num [pathFormula, hodd, Nat.add_assoc]
  have hsub : n - 2 + 2 = n := by omega
  rw [hform, hsub]
  exact max_eq_right (by omega)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathHighNewStageOne

open SimpleGraph

variable {n : ℕ} {C : Type*}

/-- Join two original rainbow host paths using one fresh literal endpoint edge.
The output preserves both input vertex orders, including singleton paths. -/
theorem rainbow_path_of_original_disjoint_paths_and_fresh_join
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (χ : TopEdgeLabeling (Fin n) C)
    (A : (pathGraph a).Copy (⊤ : SimpleGraph (Fin n)))
    (B : (pathGraph b).Copy (⊤ : SimpleGraph (Fin n)))
    (hA : IsRainbow A.toHom χ) (hB : IsRainbow B.toHom χ)
    (hdis : Disjoint (Set.range fun i : Fin a => A i)
      (Set.range fun j : Fin b => B j))
    (hpal : ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ (B.toHom.mapEdgeSet d))
    (join : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (hjoin : join.val = s(A ⟨a - 1, by omega⟩, B ⟨0, by omega⟩))
    (hfreshA : ∀ e : (pathGraph a).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ join)
    (hfreshB : ∀ d : (pathGraph b).edgeSet,
      χ (B.toHom.mapEdgeSet d) ≠ χ join) :
    ∃ f : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ ∧
      (∀ i : Fin a, f (Fin.castAdd b i) = A i) ∧
      (∀ j : Fin b, f (Fin.natAdd a j) = B j) := by
  let Q : Fin (a + b) → Fin n := Fin.append (fun i => A i) (fun j => B j)
  have hQ : Function.Injective Q := Fin.append_injective_iff.mpr
    ⟨A.injective, B.injective, fun i j heq =>
      (Set.disjoint_left.mp hdis) ⟨i, rfl⟩ ⟨j, heq.symm⟩⟩
  let f : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (SimpleGraph.Embedding.completeGraph (⟨Q, hQ⟩ : Fin (a + b) ↪ Fin n)).toCopy.comp
      (Copy.ofLE (pathGraph (a + b)) (⊤ : SimpleGraph (Fin (a + b))) le_top)
  have hforward : ∀ i j : Fin (a + b), i.val + 1 = j.val →
      (∃ d : (pathGraph a).edgeSet,
        s(Q i, Q j) = (A.toHom.mapEdgeSet d).val) ∨
      s(Q i, Q j) = join.val ∨
      (∃ d : (pathGraph b).edgeSet,
        s(Q i, Q j) = (B.toHom.mapEdgeSet d).val) := by
    intro i j hij
    by_cases hjA : j.val < a
    · have hiA : i.val < a := by omega
      let iA : Fin a := ⟨i.val, hiA⟩
      let jA : Fin a := ⟨j.val, hjA⟩
      have hi : i = Fin.castAdd b iA := Fin.ext rfl
      have hj : j = Fin.castAdd b jA := Fin.ext rfl
      let d : (pathGraph a).edgeSet :=
        ⟨s(iA, jA), pathGraph_adj.mpr (Or.inl hij)⟩
      left
      refine ⟨d, ?_⟩
      change s(Q i, Q j) = s(A iA, A jA)
      simp only [Q, hi, hj, Fin.append_left]
    · by_cases hiA : i.val < a
      · have hi : i = Fin.castAdd b (⟨a - 1, by omega⟩ : Fin a) := by
          apply Fin.ext
          change i.val = a - 1
          omega
        have hj : j = Fin.natAdd a (⟨0, by omega⟩ : Fin b) := by
          apply Fin.ext
          change j.val = a + 0
          omega
        right
        left
        simp only [Q, hi, hj, Fin.append_left, Fin.append_right, hjoin]
      · have hibound := i.isLt
        have hjbound := j.isLt
        let iB : Fin b := ⟨i.val - a, by omega⟩
        let jB : Fin b := ⟨j.val - a, by omega⟩
        have hi : i = Fin.natAdd a iB := by
          apply Fin.ext
          change i.val = a + (i.val - a)
          omega
        have hj : j = Fin.natAdd a jB := by
          apply Fin.ext
          change j.val = a + (j.val - a)
          omega
        have hadj : (pathGraph b).Adj iB jB := by
          apply pathGraph_adj.mpr
          left
          change (i.val - a) + 1 = j.val - a
          omega
        let d : (pathGraph b).edgeSet := ⟨s(iB, jB), hadj⟩
        right
        right
        refine ⟨d, ?_⟩
        change s(Q i, Q j) = s(B iB, B jB)
        simp only [Q, hi, hj, Fin.append_right]
  have hcases : ∀ e : (pathGraph (a + b)).edgeSet,
      (∃ d : (pathGraph a).edgeSet,
        f.toHom.mapEdgeSet e = A.toHom.mapEdgeSet d) ∨
      f.toHom.mapEdgeSet e = join ∨
      (∃ d : (pathGraph b).edgeSet,
        f.toHom.mapEdgeSet e = B.toHom.mapEdgeSet d) := by
    intro e
    obtain ⟨q, hq⟩ := e
    induction q using Sym2.inductionOn with
    | _ i j =>
      have hadj : (pathGraph (a + b)).Adj i j := hq
      have hs :
          (∃ d : (pathGraph a).edgeSet,
            s(Q i, Q j) = (A.toHom.mapEdgeSet d).val) ∨
          s(Q i, Q j) = join.val ∨
          (∃ d : (pathGraph b).edgeSet,
            s(Q i, Q j) = (B.toHom.mapEdgeSet d).val) := by
        rcases pathGraph_adj.mp hadj with h | h
        · exact hforward i j h
        · simpa only [Sym2.eq_swap] using hforward j i h
      rcases hs with ⟨d, hd⟩ | hd | ⟨d, hd⟩
      · exact Or.inl ⟨d, Subtype.ext hd⟩
      · exact Or.inr (Or.inl (Subtype.ext hd))
      · exact Or.inr (Or.inr ⟨d, Subtype.ext hd⟩)
  have hrainbow : IsRainbow f.toHom χ := by
    intro e d heq
    change χ (f.toHom.mapEdgeSet e) = χ (f.toHom.mapEdgeSet d) at heq
    apply f.mapEdgeSet.injective
    change f.toHom.mapEdgeSet e = f.toHom.mapEdgeSet d
    rcases hcases e with ⟨eA, heA⟩ | heJ | ⟨eB, heB⟩ <;>
      rcases hcases d with ⟨dA, hdA⟩ | hdJ | ⟨dB, hdB⟩
    · have h : eA = dA := hA (by simpa only [EdgeLabeling.pullback_apply, heA, hdA] using heq)
      simp only [heA, hdA, h]
    · exact False.elim (hfreshA eA (by simpa only [heA, hdJ] using heq))
    · exact False.elim (hpal eA dB (by simpa only [heA, hdB] using heq))
    · exact False.elim (hfreshA dA (by simpa only [heJ, hdA] using heq.symm))
    · simp only [heJ, hdJ]
    · exact False.elim (hfreshB dB (by simpa only [heJ, hdB] using heq.symm))
    · exact False.elim (hpal dA eB (by simpa only [heB, hdA] using heq.symm))
    · exact False.elim (hfreshB eB (by simpa only [heB, hdJ] using heq))
    · have h : eB = dB := hB (by simpa only [EdgeLabeling.pullback_apply, heB, hdB] using heq)
      simp only [heB, hdB, h]
  refine ⟨f, hrainbow, ?_, ?_⟩
  · intro i
    change Q (Fin.castAdd b i) = A i
    simp only [Q, Fin.append_left]
  · intro j
    change Q (Fin.natAdd a j) = B j
    simp only [Q, Fin.append_right]

end ErdosProblems.PathHighNewStageOne

namespace ErdosProblems.PathHighNewStageOne

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem comp_mapEdgeSet {α β : Type*} {H : SimpleGraph α}
    {J : SimpleGraph β} {G : SimpleGraph (Fin n)}
    (A : H.Copy J) (B : J.Copy G) (e : H.edgeSet) :
    (B.comp A).toHom.mapEdgeSet e = B.toHom.mapEdgeSet (A.toHom.mapEdgeSet e) := by
  apply Subtype.ext
  change Sym2.map (fun x => B (A x)) e.val =
    Sym2.map B (Sym2.map A e.val)
  exact (Sym2.map_map (g := B) (f := A) e.val).symm

omit [DecidableEq C] in
theorem rainbow_comp {α β : Type*} {H : SimpleGraph α}
    {J : SimpleGraph β} (A : H.Copy J)
    (B : J.Copy (⊤ : SimpleGraph (Fin n)))
    (χ : TopEdgeLabeling (Fin n) C) (hB : IsRainbow B.toHom χ) :
    IsRainbow (B.comp A).toHom χ := by
  intro e d heq
  apply A.mapEdgeSet.injective
  apply hB
  change χ (B.toHom.mapEdgeSet (A.toHom.mapEdgeSet e)) =
    χ (B.toHom.mapEdgeSet (A.toHom.mapEdgeSet d))
  simpa only [EdgeLabeling.pullback_apply, comp_mapEdgeSet] using heq

theorem path_one_no_edge (e : (pathGraph 1).edgeSet) : False := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ i j =>
    have h := pathGraph_adj.mp hq
    have hi := i.isLt
    have hj := j.isLt
    omega

def singletonHostCopy (w : Fin n) :
    (pathGraph 1).Copy (⊤ : SimpleGraph (Fin n)) :=
  (SimpleGraph.Embedding.completeGraph
    (⟨fun _ : Fin 1 => w, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin n)).toCopy.comp
    (Copy.ofLE (pathGraph 1) (⊤ : SimpleGraph (Fin 1)) le_top)

omit [DecidableEq C] in
theorem singletonHostCopy_rainbow (χ : TopEdgeLabeling (Fin n) C) (w : Fin n) :
    IsRainbow (singletonHostCopy w).toHom χ := by
  intro e d _
  exact False.elim (path_one_no_edge e)

/-- A literal source-cycle spanning path may start at any prescribed source vertex. -/
theorem source_spanning_path_at {m : ℕ} (hm : 3 ≤ m) (j : Fin m) :
    ∃ A : (pathGraph m).Copy (cycleGraph m), A ⟨0, by omega⟩ = j := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = d + 3 := ⟨m - 3, by omega⟩
  let p := cycleGraph.cycle d
  have hj : j ∈ p.support := by
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨d + 3 - j.val, ?_, ?_⟩
    · rw [cycleGraph.getVert_cycle (by omega)]
      apply Fin.ext
      have hsub : d + 3 - (d + 3 - j.val) = j.val := by omega
      simp only [hsub, Nat.mod_eq_of_lt j.isLt]
    · simp only [p, cycleGraph.length_cycle]
      omega
  let q := p.rotate j hj
  have hcycle : q.IsCycle := (cycleGraph.isCycle_cycle (n := d)).rotate hj
  have hq : q.length = d + 3 := by simp only [q, SimpleGraph.Walk.length_rotate,
    p, cycleGraph.length_cycle]
  have hp : (q.take (d + 2)).IsPath := hcycle.isPath_take (by omega)
  have hlen : (q.take (d + 2)).length = d + 2 := by
    rw [SimpleGraph.Walk.take_length, hq, Nat.min_eq_left (by omega)]
  have hex : ∃ A : (pathGraph ((q.take (d + 2)).length + 1)).Copy
      (cycleGraph (d + 3)), A ⟨0, by omega⟩ = j := by
    refine ⟨hp.pathGraphCopy, ?_⟩
    change (q.take (d + 2)).support[0] = j
    exact SimpleGraph.Walk.support_getElem_zero _
  have hsize : (q.take (d + 2)).length + 1 = d + 3 := by omega
  let P : ℕ → Prop := fun t => ∀ ht : 0 < t,
    ∃ A : (pathGraph t).Copy (cycleGraph (d + 3)), A ⟨0, ht⟩ = j
  have hP : P ((q.take (d + 2)).length + 1) := fun _ => hex
  have hP' : P (d + 3) := Eq.mp (congrArg P hsize) hP
  exact hP' (by omega)

omit [DecidableEq C] in
/-- No rainbow one-vertex extension forces every original outside-cycle color
into the palette of that same original rainbow cycle. -/
theorem outside_cycle_edge_color_mem_palette {m : ℕ} (hm : 3 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (hc : IsRainbow c.toHom χ)
    (hno : ∀ p : (pathGraph (m + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow p.toHom χ)
    (w : Fin n) (hw : w ∉ Set.range c) (j : Fin m)
    (e : HostEdge n) (he : e.val = s(w, c j)) :
    χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
  classical
  by_contra hfresh
  obtain ⟨A, hA0⟩ := source_spanning_path_at hm j
  let B := c.comp A
  let O := singletonHostCopy w
  have hB : IsRainbow B.toHom χ := rainbow_comp A c χ hc
  have hO : IsRainbow O.toHom χ := singletonHostCopy_rainbow χ w
  have hdis : Disjoint (Set.range fun i : Fin 1 => O i)
      (Set.range fun j : Fin m => B j) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨i, hi⟩ ⟨j, hj⟩
    have hwi : O i = w := rfl
    apply hw
    refine ⟨A j, ?_⟩
    exact hj.trans (hi.symm.trans hwi)
  have hjoin : e.val = s(O ⟨1 - 1, by omega⟩, B ⟨0, by omega⟩) := by
    change e.val = s(w, c (A ⟨0, by omega⟩))
    rw [hA0]
    exact he
  have hBfresh : ∀ d : (pathGraph m).edgeSet, χ (B.toHom.mapEdgeSet d) ≠ χ e := by
    intro d h
    apply hfresh
    refine ⟨A.toHom.mapEdgeSet d, ?_⟩
    change χ (c.toHom.mapEdgeSet (A.toHom.mapEdgeSet d)) = χ e
    rw [← comp_mapEdgeSet A c d]
    exact h
  obtain ⟨f, hf, _, _⟩ := rainbow_path_of_original_disjoint_paths_and_fresh_join
    (by omega : 1 ≤ 1) (by omega : 1 ≤ m) χ O B hO hB hdis
    (fun d _ => False.elim (path_one_no_edge d)) e hjoin
    (fun d => False.elim (path_one_no_edge d)) hBfresh
  have hex : ∃ p : (pathGraph (m + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
    exact (Nat.add_comm 1 m) ▸
      (show ∃ p : (pathGraph (1 + m)).Copy (⊤ : SimpleGraph (Fin n)),
        IsRainbow p.toHom χ from ⟨f, hf⟩)
  obtain ⟨p, hp⟩ := hex
  exact hno p hp

/-- A NEW color at an original vertex outside the copy cannot be a copy-edge color. -/
theorem outside_new_color_not_cycle_palette {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (v : Fin n) (hv : v ∉ Set.range c) {a : C} (ha : a ∈ newColors χ v) :
    a ∉ Set.range (EdgeLabeling.pullback χ c.toHom) := by
  rintro ⟨d, hd⟩
  have hmem := newColor_every_edge_incident χ v ha (c.toHom.mapEdgeSet d) hd
  change v ∈ Sym2.map c d.val at hmem
  obtain ⟨z, _, hz⟩ := Sym2.mem_map.mp hmem
  exact hv ⟨z, hz⟩

/-- The checked original NEW-neighbor map remains in the exact cycle complement. -/
theorem outside_new_neighbor {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (hcross : ∀ v : Fin n, v ∉ Set.range c → ∀ j : Fin m,
      ∀ e : HostEdge n, e.val = s(v, c j) →
      χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom))
    (v : Fin n) (hv : v ∉ Set.range c) (a : newColors χ v) :
    newChoiceColorNeighbor χ r v a ∉ Set.range c := by
  rintro ⟨j, hj⟩
  let e : HostEdge n := ⟨(newChoiceIncidenceEdge χ r v a).val,
    SimpleGraph.edgeSet_mono le_top (newChoiceIncidenceEdge χ r v a).property.1⟩
  have he : e.val = s(v, c j) := by
    rw [newChoiceIncidenceEdge_eq_pair χ r v a, hj]
  have hp := hcross v hv j e he
  have hcolor : χ e = a.val := newChoiceIncidenceEdge_color χ r v a
  exact outside_new_color_not_cycle_palette χ c v hv a.property (hcolor ▸ hp)

/-- Every selected edge wholly outside has original color outside the cycle palette. -/
theorem selected_outside_color {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (e : (selectedGraph χ r).edgeSet)
    (hout : ∀ v : Fin n, v ∈ e.val → v ∉ Set.range c) :
    χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ ∉
      Set.range (EdgeLabeling.pullback χ c.toHom) := by
  have hmem : e.val ∈ Set.range (fun a : newColorUnion χ => (r.edge a).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e.property
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp a.property
  have hhost : (⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ : HostEdge n) =
      r.edge a := Subtype.ext ha.symm
  have hcolor : χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ = a.val := by
    rw [hhost]
    exact r.color_eq a
  have hinc : v ∈ e.val := newColor_every_edge_incident χ v hv
    ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ hcolor
  exact hcolor.symm ▸ outside_new_color_not_cycle_palette χ c v (hout v hinc) hv

/-- A maximum path in the actual selected complement is long enough.
Only original NEW-at-endpoint slots are counted; no full-degree restriction is used. -/
theorem exists_original_rainbow_outside_path {m ell : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (hout : ∃ v : Fin n, v ∉ Set.range c)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card)
    (hcross : ∀ v : Fin n, v ∉ Set.range c → ∀ j : Fin m,
      ∀ e : HostEdge n, e.val = s(v, c j) →
      χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom)) :
    ∃ A : (pathGraph (ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow A.toHom χ ∧
      (∀ i, A i ∉ Set.range c) ∧
      (∀ e : (pathGraph (ell + 1)).edgeSet,
        χ (A.toHom.mapEdgeSet e) ∉ Set.range (EdgeLabeling.pullback χ c.toHom)) := by
  classical
  let T : Set (Fin n) := (Set.range c)ᶜ
  let G := selectedGraph χ r
  let D := G.induce T
  obtain ⟨x, hx⟩ := hout
  let : Nonempty T := ⟨⟨x, hx⟩⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length D
  let w : newColors χ v.val → T := fun a =>
    ⟨newChoiceColorNeighbor χ r v.val a,
      outside_new_neighbor χ r c hcross v.val v.property a⟩
  have hadj (a : newColors χ v.val) : D.Adj v (w a) :=
    newChoiceColorNeighbor_adj χ r v.val a
  have hsupp (a : newColors χ v.val) : w a ∈ p.support := by
    by_contra h
    have hlong := hp.concat h (hadj a)
    have hbound := hmax u (w a) (p.concat (hadj a)) hlong
    rw [SimpleGraph.Walk.length_concat] at hbound
    omega
  let P := p.support.toFinset.erase v
  let f : newColors χ v.val → P := fun a =>
    ⟨w a, Finset.mem_erase.mpr
      ⟨(hadj a).ne.symm, List.mem_toFinset.mpr (hsupp a)⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply newChoiceColorNeighbor_injective χ r v.val
    have h := congrArg (fun z : P => z.val.val) hab
    exact h
  have hcard : (newColors χ v.val).card ≤ P.card :=
    Finset.card_le_card_of_injective hf
  have hPcard : P.card = p.length := by
    calc
      P.card = p.support.toFinset.card - 1 :=
        Finset.card_erase_of_mem (List.mem_toFinset.mpr p.end_mem_support)
      _ = p.support.length - 1 := congrArg (fun z : ℕ => z - 1)
        (List.toFinset_card_of_nodup hp.support_nodup)
      _ = p.length := by
        rw [SimpleGraph.Walk.length_support]
        omega
  have hlen : ell ≤ p.length := by
    have hn := hnew v.val
    omega
  have htake : (p.take ell).length = ell := by
    rw [SimpleGraph.Walk.take_length, Nat.min_eq_left hlen]
  have hcopy : ∃ A : (pathGraph (ell + 1)).Copy D, True := by
    have h := (hp.take ell).pathGraphCopy
    have hsize : (p.take ell).length + 1 = ell + 1 := by omega
    exact ⟨hsize ▸ h, trivial⟩
  obtain ⟨A, _⟩ := hcopy
  let B : (pathGraph (ell + 1)).Copy G := (Copy.induce G T).comp A
  let H : (pathGraph (ell + 1)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp B
  refine ⟨H, copy_in_selectedGraph_isRainbow χ r B, ?_, ?_⟩
  · intro i
    exact (A i).property
  · intro e
    let d : G.edgeSet := B.toHom.mapEdgeSet e
    have hcol : χ (H.toHom.mapEdgeSet e) =
        χ ⟨d.val, SimpleGraph.edgeSet_mono le_top d.property⟩ := by
      apply congrArg χ
      apply Subtype.ext
      change Sym2.map (fun i => (A i).val) e.val =
        Sym2.map (fun i => (A i).val) e.val
      rfl
    rw [hcol]
    apply selected_outside_color χ r c d
    intro z hz
    change z ∈ Sym2.map (fun i => (A i).val) e.val at hz
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hz
    exact hi ▸ (A i).property

/-- Two opposite original half-cycle paths have disjoint palettes, so one avoids
any prescribed literal host color. The original cycle need not be selected. -/
theorem exists_original_half_cycle_path_avoiding {ell : ℕ} (hell : 2 ≤ ell)
    (χ : TopEdgeLabeling (Fin n) C)
    (c : (cycleGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)))
    (hc : IsRainbow c.toHom χ) (join : HostEdge n) :
    ∃ B : (pathGraph (ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow B.toHom χ ∧ B ⟨0, by omega⟩ = c 0 ∧
      (∀ i, B i ∈ Set.range c) ∧
      (∀ e : (pathGraph (ell + 1)).edgeSet,
        χ (B.toHom.mapEdgeSet e) ∈ Set.range (EdgeLabeling.pullback χ c.toHom)) ∧
      (∀ e : (pathGraph (ell + 1)).edgeSet, χ (B.toHom.mapEdgeSet e) ≠ χ join) := by
  classical
  let m := 2 * ell + 1
  let F : Fin (ell + 1) → Fin m := fun i => ⟨i.val, by dsimp [m]; omega⟩
  let R : Fin (ell + 1) → Fin m := fun i =>
    ⟨if i.val = 0 then 0 else m - i.val, by
      have hi := i.isLt
      dsimp [m]
      split_ifs <;> omega⟩
  have hF : Function.Injective F := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin m => z.val) h)
  have hR : Function.Injective R := by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun z : Fin m => z.val) h
    have hi := i.isLt
    have hj := j.isLt
    change (if i.val = 0 then 0 else m - i.val) =
      (if j.val = 0 then 0 else m - j.val) at hv
    dsimp [m] at hv
    split_ifs at hv <;> omega
  have hRF : ∀ i j : Fin (ell + 1), i.val + 1 = j.val →
      (cycleGraph m).Adj (R i) (R j) := by
    intro i j hij
    by_cases hi0 : i.val = 0
    · have hj1 : j.val = 1 := by omega
      have hlt : R i < R j := by
        change (R i).val < (R j).val
        simp only [R, hi0, hj1, ite_eq_left]
        dsimp [m]
        omega
      rw [cycleGraph_adj']
      left
      rw [Fin.coe_sub_iff_lt.mpr hlt]
      simp only [R, hi0, hj1, ite_eq_left]
      dsimp [m]
      omega
    · have hj0 : j.val ≠ 0 := by omega
      apply pathGraph_le_cycleGraph
      apply pathGraph_adj.mpr
      right
      simp only [R, hi0, hj0]
      dsimp [m]
      have hi := i.isLt
      have hj := j.isLt
      omega
  let L : (pathGraph (ell + 1)).Copy (cycleGraph m) :=
    { toHom :=
        { toFun := F
          map_rel' := by
            intro i j h
            apply pathGraph_le_cycleGraph
            apply pathGraph_adj.mpr
            change i.val + 1 = j.val ∨ j.val + 1 = i.val
            exact pathGraph_adj.mp h }
      injective' := hF }
  let Q : (pathGraph (ell + 1)).Copy (cycleGraph m) :=
    { toHom :=
        { toFun := R
          map_rel' := by
            intro i j h
            rcases pathGraph_adj.mp h with h | h
            · exact hRF i j h
            · exact (hRF j i h).symm }
      injective' := hR }
  have hmeet : ∀ i j : Fin (ell + 1), F i = R j →
      i.val = 0 ∧ j.val = 0 := by
    intro i j h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    have hj := j.isLt
    by_cases hj0 : j.val = 0
    · simp only [F, R, hj0, ite_eq_left] at hv
      exact ⟨hv, hj0⟩
    · simp only [F, R, hj0] at hv
      dsimp [m] at hv
      omega
  have hsourceDis : ∀ e d : (pathGraph (ell + 1)).edgeSet,
      L.toHom.mapEdgeSet e ≠ Q.toHom.mapEdgeSet d := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    induction x using Sym2.inductionOn with
    | _ i j =>
      induction y using Sym2.inductionOn with
      | _ u v =>
        have hv := congrArg Subtype.val h
        change s(F i, F j) = s(R u, R v) at hv
        have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := pathGraph_adj.mp hx
        rcases Sym2.eq_iff.mp hv with h | h
        · have hi0 : i.val = 0 := (hmeet i u h.1).1
          have hj0 : j.val = 0 := (hmeet j v h.2).1
          rcases hadj with hstep | hstep <;> omega
        · have hi0 : i.val = 0 := (hmeet i v h.1).1
          have hj0 : j.val = 0 := (hmeet j u h.2).1
          rcases hadj with hstep | hstep <;> omega
  let BL := c.comp L
  let BR := c.comp Q
  have hBL : IsRainbow BL.toHom χ := rainbow_comp L c χ hc
  have hBR : IsRainbow BR.toHom χ := rainbow_comp Q c χ hc
  have hpal : ∀ e d : (pathGraph (ell + 1)).edgeSet,
      χ (BL.toHom.mapEdgeSet e) ≠ χ (BR.toHom.mapEdgeSet d) := by
    intro e d h
    apply hsourceDis e d
    apply hc
    change χ (c.toHom.mapEdgeSet (L.toHom.mapEdgeSet e)) =
      χ (c.toHom.mapEdgeSet (Q.toHom.mapEdgeSet d))
    simpa only [BL, BR, comp_mapEdgeSet] using h
  have hBL0 : BL ⟨0, by omega⟩ = c 0 := by
    change c (F ⟨0, by omega⟩) = c 0
    apply congrArg c
    exact Fin.ext rfl
  have hBR0 : BR ⟨0, by omega⟩ = c 0 := by
    change c (R ⟨0, by omega⟩) = c 0
    apply congrArg c
    apply Fin.ext
    simp only [R, Fin.val_zero, ite_eq_left]
  have hBLpal (e : (pathGraph (ell + 1)).edgeSet) :
      χ (BL.toHom.mapEdgeSet e) ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
    refine ⟨L.toHom.mapEdgeSet e, ?_⟩
    change χ (c.toHom.mapEdgeSet (L.toHom.mapEdgeSet e)) = χ (BL.toHom.mapEdgeSet e)
    rw [comp_mapEdgeSet]
  have hBRpal (e : (pathGraph (ell + 1)).edgeSet) :
      χ (BR.toHom.mapEdgeSet e) ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
    refine ⟨Q.toHom.mapEdgeSet e, ?_⟩
    change χ (c.toHom.mapEdgeSet (Q.toHom.mapEdgeSet e)) = χ (BR.toHom.mapEdgeSet e)
    rw [comp_mapEdgeSet]
  by_cases hleft : ∀ e : (pathGraph (ell + 1)).edgeSet,
      χ (BL.toHom.mapEdgeSet e) ≠ χ join
  · exact ⟨BL, hBL, hBL0, fun i => ⟨L i, rfl⟩, hBLpal, hleft⟩
  · push Not at hleft
    obtain ⟨e, he⟩ := hleft
    refine ⟨BR, hBR, hBR0, fun i => ⟨Q i, rfl⟩, hBRpal, ?_⟩
    intro d hd
    exact hpal e d (he.trans hd.symm)

/-- Exact original first stage: high NEW and no even rainbow path exclude
the preceding odd rainbow cycle. No intermediate palette or path is supplied. -/
theorem no_rainbow_odd_cycle_of_high_new_and_no_even_path {ell : ℕ}
    (hell : 2 ≤ ell) (hn : 2 * ell + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card)
    (hnoP : ∀ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow p.toHom χ) :
    ∀ c : (cycleGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow c.toHom χ := by
  classical
  intro c hc
  have hout : ∃ v : Fin n, v ∉ Set.range c := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective c := fun v => h v
    have hcard := Fintype.card_le_of_surjective c hsurj
    simp only [Fintype.card_fin] at hcard
    omega
  have hcross : ∀ v : Fin n, v ∉ Set.range c → ∀ j : Fin (2 * ell + 1),
      ∀ e : HostEdge n, e.val = s(v, c j) →
      χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
    intro v hv j e he
    exact outside_cycle_edge_color_mem_palette (by omega) χ c hc
      hnoP v hv j e he
  let r := canonicalChoice χ
  obtain ⟨A, hA, houtA, hfreshA⟩ :=
    exists_original_rainbow_outside_path χ r c hout hnew hcross
  let w := A ⟨ell, by omega⟩
  have hw : w ∉ Set.range c := houtA _
  have hneq : w ≠ c 0 := by
    intro h
    exact hw ⟨0, h.symm⟩
  let join : HostEdge n := ⟨s(w, c 0), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    exact hneq⟩
  have hjoinpal : χ join ∈ Set.range (EdgeLabeling.pullback χ c.toHom) :=
    hcross w hw 0 join rfl
  obtain ⟨B, hB, hB0, hinB, hBpal, hfreshB⟩ :=
    exists_original_half_cycle_path_avoiding hell χ c hc join
  have hdis : Disjoint (Set.range fun i : Fin (ell + 1) => A i)
      (Set.range fun j : Fin (ell + 1) => B j) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨i, hi⟩ ⟨j, hj⟩
    apply houtA i
    have hab : B j = A i := hj.trans hi.symm
    rw [← hab]
    exact hinB j
  have hpal : ∀ e d : (pathGraph (ell + 1)).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ (B.toHom.mapEdgeSet d) := by
    intro e d h
    exact hfreshA e (h.symm ▸ hBpal d)
  have hj : join.val = s(A ⟨ell + 1 - 1, by omega⟩, B ⟨0, by omega⟩) := by
    have hindex : (⟨ell + 1 - 1, by omega⟩ : Fin (ell + 1)) = ⟨ell, by omega⟩ := by
      apply Fin.ext
      change ell + 1 - 1 = ell
      omega
    change s(A ⟨ell, by omega⟩, c 0) =
      s(A ⟨ell + 1 - 1, by omega⟩, B ⟨0, by omega⟩)
    rw [hindex, hB0]
  have hAfresh : ∀ e : (pathGraph (ell + 1)).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ join := by
    intro e h
    exact hfreshA e (h.symm ▸ hjoinpal)
  obtain ⟨f, hf, _, _⟩ := rainbow_path_of_original_disjoint_paths_and_fresh_join
    (by omega) (by omega) χ A B hA hB hdis hpal join hj hAfresh hfreshB
  have hex : ∃ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
    have hsize : (ell + 1) + (ell + 1) = 2 * ell + 2 := by omega
    exact hsize ▸
      (show ∃ p : (pathGraph ((ell + 1) + (ell + 1))).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow p.toHom χ from ⟨f, hf⟩)
  obtain ⟨p, hp⟩ := hex
  exact hnoP p hp

end ErdosProblems.PathHighNewStageOne

section

universe u

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

/-- The two endpoint reachability sets after one edge deletion cover its old
component. This coverage does not require the edge to be a bridge. -/
theorem reachable_delete_edge_either_endpoint
    {V : Type u} (H : SimpleGraph V) (a b : V) {z : V}
    (haz : H.Reachable a z) :
    (H.deleteEdges {s(a, b)}).Reachable a z ∨
      (H.deleteEdges {s(a, b)}).Reachable b z := by
  let D := H.deleteEdges {s(a, b)}
  have hstep : ∀ x y, H.Adj x y →
      (D.Reachable a x ∨ D.Reachable b x) →
      (D.Reachable a y ∨ D.Reachable b y) := by
    intro x y hxy hx
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (SimpleGraph.Reachable.refl _)
      · exact Or.inl (SimpleGraph.Reachable.refl _)
    · have hdxy : D.Adj x y := SimpleGraph.deleteEdges_adj.mpr
        ⟨hxy, by simpa only [Set.mem_singleton_iff] using he⟩
      rcases hx with ha | hb
      · exact Or.inl (ha.trans hdxy.reachable)
      · exact Or.inr (hb.trans hdxy.reachable)
  have hwalk : ∀ {x y} (p : H.Walk x y),
      (D.Reachable a x ∨ D.Reachable b x) →
      (D.Reachable a y ∨ D.Reachable b y) := by
    intro x y p
    induction p with
    | nil => exact fun hx => hx
    | cons hxy p ih =>
        intro hx
        exact ih (hstep _ _ hxy hx)
  obtain ⟨p⟩ := haz
  exact hwalk p (Or.inl (SimpleGraph.Reachable.refl a))

/-- A walk in an old component different from the edge endpoints' component
survives the deletion. Actual adjacency joins the two old endpoints. -/
theorem reachable_delete_edge_of_other_component
    {V : Type u} (H : SimpleGraph V) {a b x y : V}
    (hab : H.Adj a b) (hxa : ¬ H.Reachable x a)
    (hxy : H.Reachable x y) :
    (H.deleteEdges {s(a, b)}).Reachable x y := by
  let D := H.deleteEdges {s(a, b)}
  have hstep : ∀ u v, H.Reachable x u → H.Adj u v → D.Reachable u v := by
    intro u v hxu huv
    have he : s(u, v) ≠ s(a, b) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxa hxu
      · exact hxa (hxu.trans hab.symm.reachable)
    exact (SimpleGraph.deleteEdges_adj.mpr
      ⟨huv, by simpa only [Set.mem_singleton_iff] using he⟩).reachable
  have hwalk : ∀ {u v} (p : H.Walk u v),
      H.Reachable x u → D.Reachable u v := by
    intro u v p
    induction p with
    | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
    | cons huv p ih =>
        intro hxu
        exact (hstep _ _ hxu huv).trans (ih (hxu.trans huv.reachable))
  obtain ⟨p⟩ := hxy
  exact hwalk p (SimpleGraph.Reachable.refl x)

theorem component_count_delete_bridge_pair
    {V : Type u} [Finite V] (H : SimpleGraph V) {a b : V}
    (hab : H.Adj a b) (hbridge : H.IsBridge s(a, b)) :
    Nat.card (H.deleteEdges {s(a, b)}).ConnectedComponent =
      Nat.card H.ConnectedComponent + 1 := by
  classical
  let D := H.deleteEdges {s(a, b)}
  let φ : D.ConnectedComponent → H.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map
      (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le (G := H) {s(a, b)}))
  let C₀ := H.connectedComponentMk a
  have hnot : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  have hcover : ∀ c : D.ConnectedComponent,
      φ c = C₀ → c = D.connectedComponentMk a ∨ c = D.connectedComponentMk b := by
    intro c
    refine c.ind ?_
    intro z hz
    change H.connectedComponentMk z = H.connectedComponentMk a at hz
    have haz : H.Reachable a z := (SimpleGraph.ConnectedComponent.exact hz).symm
    rcases reachable_delete_edge_either_endpoint H a b haz with ha | hb
    · exact Or.inl (SimpleGraph.ConnectedComponent.sound ha.symm)
    · exact Or.inr (SimpleGraph.ConnectedComponent.sound hb.symm)
  let ca : {c : D.ConnectedComponent // φ c = C₀} :=
    ⟨D.connectedComponentMk a, rfl⟩
  let cb : {c : D.ConnectedComponent // φ c = C₀} :=
    ⟨D.connectedComponentMk b, SimpleGraph.ConnectedComponent.sound hab.symm.reachable⟩
  have hcab : ca ≠ cb := by
    intro heq
    apply hnot
    apply SimpleGraph.ConnectedComponent.exact
    exact congrArg (fun q : {c : D.ConnectedComponent // φ c = C₀} => q.val) heq
  have hcard₀ : Nat.card {c : D.ConnectedComponent // φ c = C₀} = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨ca, cb, hcab, ?_⟩
    apply Set.ext
    intro q
    constructor
    · intro _
      trivial
    · intro _
      change q = ca ∨ q = cb
      rcases hcover q.val q.property with ha | hb
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr (Subtype.ext hb)
  have hsurj : Function.Surjective φ :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE
      (SimpleGraph.deleteEdges_le (G := H) {s(a, b)})
  have hcard_other : ∀ C : H.ConnectedComponent, C ≠ C₀ →
      Nat.card {c : D.ConnectedComponent // φ c = C} = 1 := by
    intro C hC
    have hsame : ∀ c d : D.ConnectedComponent, φ c = C → φ d = C → c = d := by
      intro c d
      refine c.ind ?_
      intro x
      refine d.ind ?_
      intro y hx hy
      change H.connectedComponentMk x = C at hx
      change H.connectedComponentMk y = C at hy
      have hxy : H.Reachable x y :=
        SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
      have hxa : ¬ H.Reachable x a := by
        intro hxa
        exact hC (hx.symm.trans (SimpleGraph.ConnectedComponent.sound hxa))
      exact SimpleGraph.ConnectedComponent.sound
        (reachable_delete_edge_of_other_component H hab hxa hxy)
    obtain ⟨c, hc⟩ := hsurj C
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨c, hc⟩, ?_⟩
    intro d
    exact Subtype.ext (hsame d.val c d.property hc)
  have hcards : ∀ C : H.ConnectedComponent,
      Nat.card {c : D.ConnectedComponent // φ c = C} = if C = C₀ then 2 else 1 := by
    intro C
    by_cases hC : C = C₀
    · subst C
      rw [ite_eq_left rfl]
      exact hcard₀
    · rw [ite_eq_right hC]
      exact hcard_other C hC
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  calc
    Nat.card D.ConnectedComponent =
        Nat.card (Σ C : H.ConnectedComponent, {c : D.ConnectedComponent // φ c = C}) :=
      Nat.card_congr ((Equiv.sigmaFiberEquiv φ).symm)
    _ = ∑ C : H.ConnectedComponent,
        Nat.card {c : D.ConnectedComponent // φ c = C} := Nat.card_sigma
    _ = ∑ C : H.ConnectedComponent, ((if C = C₀ then 1 else 0) + 1) := by
      apply Finset.sum_congr rfl
      intro C _
      rw [hcards C]
      by_cases hC : C = C₀
      · simp only [ite_eq_left hC]
      · simp only [ite_eq_right hC]
    _ = (∑ C : H.ConnectedComponent, if C = C₀ then 1 else 0) +
        (∑ _C : H.ConnectedComponent, 1) := Finset.sum_add_distrib
    _ = Nat.card H.ConnectedComponent + 1 := by
      simp [Nat.card_eq_fintype_card, Nat.add_comm]

/-- One actual bridge deletion increases the number of components by one.
The old graph is allowed to be disconnected. -/
theorem connected_component_count_delete_bridge
    {V : Type u} [Finite V] (H : SimpleGraph V) (e : Sym2 V)
    (he : e ∈ H.edgeSet) (hbridge : H.IsBridge e) :
    Nat.card (H.deleteEdges {e}).ConnectedComponent =
      Nat.card H.ConnectedComponent + 1 := by
  obtain ⟨a, b⟩ := e
  exact component_count_delete_bridge_pair H ((H.mem_edgeSet).mp he) hbridge

/-- Delete a finite set of distinct actual ORIGINAL bridges of one connected
graph. No connectedness is asserted for its intermediate deleted graphs. -/
theorem connected_component_count_delete_original_bridges
    {V : Type u} [Finite V] (G : SimpleGraph V) (hG : G.Connected)
    (A : Finset (Sym2 V))
    (hAedge : (A : Set (Sym2 V)) ⊆ G.edgeSet)
    (hAbridge : ∀ e ∈ A, G.IsBridge e) :
    Nat.card (G.deleteEdges (A : Set (Sym2 V))).ConnectedComponent = A.card + 1 := by
  classical
  revert hAedge hAbridge
  induction A using Finset.induction_on with
  | empty =>
      intro _ _
      rw [Finset.coe_empty, SimpleGraph.deleteEdges_empty, Finset.card_empty, Nat.zero_add]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨hG.preconnected.subsingleton_connectedComponent,
          Nonempty.map G.connectedComponentMk hG.nonempty⟩
  | @insert e A he ih =>
      intro hAedge hAbridge
      have hAedge' : (A : Set (Sym2 V)) ⊆ G.edgeSet :=
        fun _ hx => hAedge (Finset.mem_insert_of_mem hx)
      have hAbridge' : ∀ f ∈ A, G.IsBridge f :=
        fun f hf => hAbridge f (Finset.mem_insert_of_mem hf)
      have heedge : e ∈ (G.deleteEdges (A : Set (Sym2 V))).edgeSet := by
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨hAedge (Finset.mem_insert_self e A), he⟩
      have hebridge : (G.deleteEdges (A : Set (Sym2 V))).IsBridge e :=
        SimpleGraph.IsBridge.anti
          (SimpleGraph.deleteEdges_le (G := G) (A : Set (Sym2 V)))
          (hAbridge e (Finset.mem_insert_self e A))
      have hcount := connected_component_count_delete_bridge
        (G.deleteEdges (A : Set (Sym2 V))) e heedge hebridge
      have hdelete :
          (G.deleteEdges (A : Set (Sym2 V))).deleteEdges {e} =
            G.deleteEdges ((insert e A : Finset (Sym2 V)) : Set (Sym2 V)) := by
        rw [SimpleGraph.deleteEdges_deleteEdges, Finset.coe_insert]
        congr 1
        ext f
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
        exact or_comm
      rw [← hdelete, hcount, ih hAedge' hAbridge', Finset.card_insert_of_notMem he]

end ErdosProblems.PathUpperReduction

end

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

universe w

/-- The current graph's deletion has exactly the original bridge cut's
reachability relation when every other current edge respects that cut. -/
theorem bridge_cut_component_transfer
    {V : Type w} (R D : SimpleGraph V) {u v : V}
    (_hR : R.Connected) (_hRb : R.Adj u v)
    (hbR : R.IsBridge s(u, v))
    (hD : D.Connected) (_hDb : D.Adj u v)
    (hrespect : ∀ {a b : V}, D.Adj a b →
      s(a, b) ≠ s(u, v) →
      (R.deleteEdges {s(u, v)}).Reachable a b) :
    ∀ a b : V,
      (D.deleteEdges {s(u, v)}).Reachable a b ↔
      (R.deleteEdges {s(u, v)}).Reachable a b := by
  classical
  let R₀ := R.deleteEdges {s(u, v)}
  let D₀ := D.deleteEdges {s(u, v)}
  have hnotRuv : ¬ R₀.Reachable u v := SimpleGraph.isBridge_iff.mp hbR
  have hforward : ∀ {a b : V}, D₀.Reachable a b → R₀.Reachable a b := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b _c hab _p ih =>
      have hadj : D.Adj a b := (SimpleGraph.deleteEdges_adj.mp hab).1
      have hne : s(a, b) ≠ s(u, v) := by
        simpa using (SimpleGraph.deleteEdges_adj.mp hab).2
      exact (hrespect hadj hne).trans ih
  have hcoverWalk : ∀ {a b : V}, (p : D.Walk a b) →
      (D₀.Reachable u b ∨ D₀.Reachable v b) →
      (D₀.Reachable u a ∨ D₀.Reachable v a) := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b _c hab _p ih =>
      intro h
      by_cases he : s(a, b) = s(u, v)
      · rcases Sym2.eq_iff.mp he with ⟨ha, _⟩ | ⟨ha, _⟩
        · left
          rw [ha]
        · right
          rw [ha]
      · have hstep : D₀.Adj a b :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using he⟩
        rcases ih h with hu | hv
        · exact Or.inl (hu.trans hstep.symm.reachable)
        · exact Or.inr (hv.trans hstep.symm.reachable)
  have hcover : ∀ a : V, D₀.Reachable u a ∨ D₀.Reachable v a := by
    intro a
    obtain ⟨p⟩ := hD.preconnected a u
    exact hcoverWalk p (Or.inl (SimpleGraph.Reachable.refl u))
  intro a b
  constructor
  · exact hforward
  · intro hab
    rcases hcover a with hau | hva
    · rcases hcover b with hub | hvb
      · exact hau.symm.trans hub
      · exfalso
        exact hnotRuv ((hforward hau).trans (hab.trans (hforward hvb).symm))
    · rcases hcover b with hub | hvb
      · exfalso
        exact hnotRuv ((hforward hub).trans (hab.symm.trans (hforward hva).symm))
      · exact hva.symm.trans hvb

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

universe w

/-- A distinct actual supergraph edge across the original bridge cut makes
the retained original pair nonbridge. No finite carrier or current/supergraph
bridge, deletion equivalence, alternate walk or extra connectivity premise
is assumed. -/
theorem not_isBridge_of_crossing_extra_edge
    {V : Type w} (R D Q : SimpleGraph V) {u v a b : V}
    (hR : R.Connected) (hRb : R.Adj u v)
    (hbR : R.IsBridge s(u, v))
    (hD : D.Connected) (hDb : D.Adj u v)
    (hrespect : ∀ {x y : V}, D.Adj x y →
      s(x, y) ≠ s(u, v) →
      (R.deleteEdges {s(u, v)}).Reachable x y)
    (hDQ : D ≤ Q) (habQ : Q.Adj a b)
    (hne : s(a, b) ≠ s(u, v))
    (hcross : ¬ (R.deleteEdges {s(u, v)}).Reachable a b) :
    ¬ Q.IsBridge s(u, v) := by
  intro hbQ
  have hQ : Q.Connected := SimpleGraph.Connected.mono hDQ hD
  have hQb : Q.Adj u v := hDQ hDb
  have hrespectQ : ∀ {x y : V}, D.Adj x y →
      s(x, y) ≠ s(u, v) →
      (Q.deleteEdges {s(u, v)}).Reachable x y := by
    intro x y hxy hxyne
    have hadj : (Q.deleteEdges {s(u, v)}).Adj x y :=
      SimpleGraph.deleteEdges_adj.mpr
        ⟨hDQ hxy, by simpa only [Set.mem_singleton_iff] using hxyne⟩
    exact hadj.reachable
  have hcutR := bridge_cut_component_transfer R D hR hRb hbR hD hDb hrespect
  have hcutQ := bridge_cut_component_transfer Q D hQ hQb hbQ hD hDb hrespectQ
  have hsurviving : (Q.deleteEdges {s(u, v)}).Adj a b :=
    SimpleGraph.deleteEdges_adj.mpr
      ⟨habQ, by simpa only [Set.mem_singleton_iff] using hne⟩
  exact hcross ((hcutR a b).mp ((hcutQ a b).mpr hsurviving.reachable))

end ErdosProblems.PathUpperReduction

section

universe u

open SimpleGraph

namespace ErdosProblems.PathUpperReduction

/-- A bridge used by a trail separates the endpoints of that trail. -/
theorem bridge_on_trail_separates_endpoints
    {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (hp : p.IsTrail) {e : Sym2 V}
    (he : e ∈ p.edges) (hbridge : G.IsBridge e) :
    ¬ (G.deleteEdges {e}).Reachable a b := by
  classical
  cases e with
  | h x y =>
    have hxy : ¬ (G.deleteEdges {s(x, y)}).Reachable x y :=
      SimpleGraph.isBridge_iff.mp hbridge
    intro hab
    by_cases hay : (G.deleteEdges {s(x, y)}).Reachable a y
    · have hax : ¬ (G.deleteEdges {s(x, y)}).Reachable a x := by
        intro hax
        exact hxy (hax.symm.trans hay)
      have hbx : ¬ (G.deleteEdges {s(x, y)}).Reachable b x := by
        intro hbx
        exact hxy (hbx.symm.trans (hab.symm.trans hay))
      have hswap : s(y, x) = s(x, y) := Sym2.eq_swap
      have hax' : ¬ (G.deleteEdges {s(y, x)}).Reachable a x := by
        simpa only [hswap] using hax
      have hbx' : ¬ (G.deleteEdges {s(y, x)}).Reachable b x := by
        simpa only [hswap] using hbx
      have hnot : s(y, x) ∉ p.edges :=
        hp.not_mem_edges_of_not_reachable (x := y) (y := x) hax' hbx'
      exact hnot (by simpa only [hswap] using he)
    · have hby : ¬ (G.deleteEdges {s(x, y)}).Reachable b y := by
        intro hby
        exact hay (hab.trans hby)
      exact hp.not_mem_edges_of_not_reachable hay hby he

/-- If deleting original bridges disconnects two vertices of a connected graph,
one of those original bridges already disconnects the same two vertices. -/
theorem exists_crossed_bridge_cut
    {V : Type u} (R : SimpleGraph V) (hR : R.Connected)
    (S : Set (Sym2 V)) (hbridges : ∀ e ∈ S, R.IsBridge e) {a b : V}
    (hab : ¬ (R.deleteEdges S).Reachable a b) :
    ∃ e ∈ S, ¬ (R.deleteEdges {e}).Reachable a b := by
  obtain ⟨p, hp⟩ := hR.exists_isPath a b
  obtain ⟨e, heS, hep⟩ := p.exists_mem_edges_of_not_reachable_deleteEdges hab
  exact ⟨e, heS, bridge_on_trail_separates_endpoints R p hp.isTrail hep (hbridges e heS)⟩

end ErdosProblems.PathUpperReduction

end

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Surjectivity gives a selected host edge of every used color. -/
noncomputable def choiceOfSurjective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) : RepresentativeChoice χ where
  edge := Function.surjInv hχ
  color_eq := Function.surjInv_eq hχ

set_option linter.style.haveILetI false in
/-- Among all same-color representatives, one has a globally largest
connected component. The condition `0<n` supplies a component vertex. -/
theorem exists_globallyLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n) :
    ∃ (r : RepresentativeChoice χ) (x : Fin n), GloballyLargestComponent χ r x := by
  classical
  letI : Fintype (HostEdge n) :=
    SimpleGraph.fintypeEdgeSet (⊤ : SimpleGraph (Fin n))
  have hinj : Function.Injective (fun r : RepresentativeChoice χ => r.edge) := by
    intro r s h
    cases r with
    | mk re rp =>
      cases s with
      | mk se sp =>
        cases h
        rfl
  letI : Finite (RepresentativeChoice χ) := Finite.of_injective _ hinj
  letI : Fintype (RepresentativeChoice χ × Fin n) := Fintype.ofFinite _
  let x₀ : Fin n := ⟨0, hn⟩
  let r₀ := choiceOfSurjective χ hχ
  obtain ⟨⟨r, x⟩, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (RepresentativeChoice χ × Fin n))
      (fun p => ((selectedGraph χ p.1).connectedComponentMk p.2).supp.ncard)
      ⟨(r₀, x₀), Finset.mem_univ _⟩
  exact ⟨r, x, fun r' z => hmax (r', z) (Finset.mem_univ _)⟩

/-- The first unconditional choice reduction in Yuan's upper proof: for any
surjective host coloring, choose one edge per color and a largest component;
every host edge leaving it has the color of a selected bridge *inside* it. -/
theorem exists_representative_with_cross_edge_bridge_colors
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n) :
    ∃ (r : RepresentativeChoice χ) (x : Fin n),
      ∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        (selectedGraph χ r).Reachable x u →
        ¬ (selectedGraph χ r).Reachable x y →
        ∃ a b : Fin n,
          (r.edge (χ e)).val = s(a, b) ∧
          a ∈ (selectedGraph χ r).connectedComponentMk x ∧
          b ∈ (selectedGraph χ r).connectedComponentMk x ∧
          (selectedGraph χ r).IsBridge s(a, b) := by
  obtain ⟨r, x, hmax⟩ := exists_globallyLargestComponent χ hχ hn
  exact ⟨r, x, fun e u y he hu hy =>
    cross_edge_color_is_component_bridge χ r x hmax e u y he hu hy⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- A globally largest component among all full same-color representatives
is the whole selected graph above the disconnected actual-bridge threshold. -/
theorem selectedGraph_connected_of_global_maximum_and_dense
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x)
    (hdense : (n - 2).choose 2 + 2 ≤ q) :
    (selectedGraph χ r).Connected := by
  classical
  by_contra hdis
  have hyexists : ∃ y : Fin n, ¬ (selectedGraph χ r).Reachable x y := by
    by_contra! h
    exact hdis ((SimpleGraph.connected_iff_exists_forall_reachable (selectedGraph χ r)).mpr ⟨x, h⟩)
  obtain ⟨y, hy⟩ := hyexists
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hy (SimpleGraph.Reachable.refl x)
  let e : HostEdge n :=
    ⟨s(x, y), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
      ((top_adj x y).mpr hxy)⟩
  obtain ⟨a, b, howner, _, _, hbridge⟩ :=
    cross_edge_color_is_component_bridge χ r x hmax e x y rfl
      (SimpleGraph.Reachable.refl x) hy
  have hselected : (r.edge (χ e)).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet χ r]
    exact ⟨χ e, rfl⟩
  rw [howner] at hselected
  have hGdense : (n - 2).choose 2 + 2 ≤ (selectedGraph χ r).edgeFinset.card := by
    rw [selectedGraph_card_edgeFinset χ r]
    exact hdense
  have hGdenseCanonical := hGdense
  have hInstances : selectedGraph_edgeSet_fintype χ r =
      (selectedGraph χ r).fintypeEdgeSet := Subsingleton.elim _ _
  rw [hInstances] at hGdenseCanonical
  exact ErdosProblems.PathUpperDenseDisconnectedBridgeBound.actual_edge_not_bridge_of_dense_disconnected
      (selectedGraph χ r) hdis hGdenseCanonical s(a, b) hselected hbridge

/-- Surjectivity and a nonempty host supply a connected full representative
at the same original-palette density threshold. -/
theorem exists_connected_representative_of_dense_palette
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n)
    (hdense : (n - 2).choose 2 + 2 ≤ q) :
    ∃ r : RepresentativeChoice χ, (selectedGraph χ r).Connected := by
  obtain ⟨r, x, hmax⟩ := exists_globallyLargestComponent χ hχ hn
  exact ⟨r, selectedGraph_connected_of_global_maximum_and_dense χ r x hmax hdense⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

def componentSupport (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n) : Set (Fin n) :=
  ((selectedGraph χ r).connectedComponentMk x).supp

/-- Both endpoints of an unordered edge lie in the specified vertex set. -/
def EdgeInside (X : Set (Fin n)) (f : Sym2 (Fin n)) : Prop :=
  ∀ v ∈ f, v ∈ X

/-- Actual unordered selected host edges wholly inside `X`, counted once. -/
noncomputable def internalSelectedEdges (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Finset.univ.image (fun c : Fin q => (r.edge c).val)).filter (EdgeInside X)

theorem mem_componentSupport (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x v : Fin n) :
    v ∈ componentSupport χ r x ↔ (selectedGraph χ r).Reachable x v := by
  change (selectedGraph χ r).connectedComponentMk v =
      (selectedGraph χ r).connectedComponentMk x ↔ _
  exact SimpleGraph.ConnectedComponent.eq.trans SimpleGraph.reachable_comm

theorem mem_internalSelectedEdges (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) (f : Sym2 (Fin n)) :
    f ∈ internalSelectedEdges χ r X ↔
      f ∈ (selectedGraph χ r).edgeSet ∧ EdgeInside X f := by
  classical
  rw [selectedGraph_edgeSet χ r]
  simp [internalSelectedEdges]

/-- Maximum component vertex count, then maximum internal edge count among
all components of all same-color choices with that vertex count. -/
def LexLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n) : Prop :=
  GloballyLargestComponent χ r x ∧
    ∀ (r' : RepresentativeChoice χ) (z : Fin n),
      (componentSupport χ r' z).ncard = (componentSupport χ r x).ncard →
      (internalSelectedEdges χ r' (componentSupport χ r' z)).card ≤
        (internalSelectedEdges χ r (componentSupport χ r x)).card

/-- Global vertex maximality makes the retained component's vertex set exact. -/
theorem componentSupport_replace_of_old_not_inside
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x) (e : HostEdge n)
    (hnot : ¬ EdgeInside (componentSupport χ r x) (r.edge (χ e)).val) :
    componentSupport χ (r.replace e) x = componentSupport χ r x := by
  have hretain : ∀ v, (selectedGraph χ r).Reachable x v →
      ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
    intro v hv
    by_contra hdisconnect
    obtain ⟨a, b, hab, ha, hb⟩ :=
      edge_endpoints_reachable_of_delete_disconnects
        (selectedGraph χ r) (r.edge (χ e)).val hv hdisconnect
    apply hnot
    rw [hab]
    intro w hw
    rcases Sym2.mem_iff.mp hw with hwa | hwb
    · rw [hwa]
      exact (mem_componentSupport χ r x a).mpr ha
    · rw [hwb]
      exact (mem_componentSupport χ r x b).mpr hb
  have hsub : componentSupport χ r x ⊆ componentSupport χ (r.replace e) x := by
    intro v hv
    exact (mem_componentSupport χ (r.replace e) x v).mpr
      ((hretain v ((mem_componentSupport χ r x v).mp hv)).mono
        (delete_selectedEdge_le_replace χ r e))
  exact (Set.eq_of_subset_of_ncard_le hsub (hmax (r.replace e) x)).symm

/-- If the old selected same-color edge is noninternal, replacing it by an
interior host edge inserts exactly that literal edge into the internal set. -/
theorem internalSelectedEdges_replace_of_old_not_inside
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) (e : HostEdge n)
    (he : EdgeInside X e.val)
    (hnot : ¬ EdgeInside X (r.edge (χ e)).val) :
    internalSelectedEdges χ (r.replace e) X =
      insert e.val (internalSelectedEdges χ r X) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨hselected, hfinside⟩ :=
      (mem_internalSelectedEdges χ (r.replace e) X f).mp hf
    rw [selectedGraph_edgeSet] at hselected
    obtain ⟨c, hc⟩ := hselected
    change ((r.replace e).edge c).val = f at hc
    by_cases hcolor : c = χ e
    · have hfe : f = e.val := by
        rw [hcolor, r.replace_edge_same e] at hc
        exact hc.symm
      exact Finset.mem_insert.mpr (Or.inl hfe)
    · have hold : (r.edge c).val = f := by
        simpa only [r.replace_edge_other e hcolor] using hc
      apply Finset.mem_insert_of_mem
      apply (mem_internalSelectedEdges χ r X f).mpr
      refine ⟨?_, hfinside⟩
      rw [selectedGraph_edgeSet]
      exact ⟨c, hold⟩
  · intro hf
    rcases Finset.mem_insert.mp hf with hfe | hf
    · subst f
      exact (mem_internalSelectedEdges χ (r.replace e) X e.val).mpr
        ⟨replacedEdge_mem χ r e, he⟩
    · obtain ⟨hselected, hfinside⟩ := (mem_internalSelectedEdges χ r X f).mp hf
      rw [selectedGraph_edgeSet] at hselected
      obtain ⟨c, hc⟩ := hselected
      change (r.edge c).val = f at hc
      have hcolor : c ≠ χ e := by
        intro hcγ
        subst c
        apply hnot
        rw [hc]
        exact hfinside
      apply (mem_internalSelectedEdges χ (r.replace e) X f).mpr
      refine ⟨?_, hfinside⟩
      rw [selectedGraph_edgeSet]
      refine ⟨c, ?_⟩
      simpa only [r.replace_edge_other e hcolor] using hc

/-- The insertion above is fresh, since the full original-color choice is
injective and the old edge of this original color is noninternal. -/
theorem internalSelectedEdges_card_replace_of_old_not_inside
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) (e : HostEdge n)
    (he : EdgeInside X e.val)
    (hnot : ¬ EdgeInside X (r.edge (χ e)).val) :
    (internalSelectedEdges χ (r.replace e) X).card =
      (internalSelectedEdges χ r X).card + 1 := by
  classical
  have hnew : e.val ∉ internalSelectedEdges χ r X := by
    intro hmem
    have hselected := ((mem_internalSelectedEdges χ r X e.val).mp hmem).1
    rw [selectedGraph_edgeSet] at hselected
    obtain ⟨c, hc⟩ := hselected
    change (r.edge c).val = e.val at hc
    have hedge : r.edge c = e := Subtype.ext hc
    have hcolor : c = χ e := by
      calc
        c = χ (r.edge c) := (r.color_eq c).symm
        _ = χ e := congrArg χ hedge
    subst c
    apply hnot
    rw [hc]
    exact he
  rw [internalSelectedEdges_replace_of_old_not_inside χ r X e he hnot,
    Finset.card_insert_of_notMem hnew]

/-- Every original host color used inside the lexicographically chosen
component is selected on an edge wholly inside that same component. -/
theorem interior_color_selected_inside_of_lexLargestComponent
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hlex : LexLargestComponent χ r x)
    (e : HostEdge n) (he : EdgeInside (componentSupport χ r x) e.val) :
    EdgeInside (componentSupport χ r x) (r.edge (χ e)).val := by
  by_contra hnot
  have hsupport := componentSupport_replace_of_old_not_inside χ r x hlex.1 e hnot
  have hsize : (componentSupport χ (r.replace e) x).ncard =
      (componentSupport χ r x).ncard := congrArg Set.ncard hsupport
  have htie := hlex.2 (r.replace e) x hsize
  rw [hsupport] at htie
  have hcard := internalSelectedEdges_card_replace_of_old_not_inside
    χ r (componentSupport χ r x) e he hnot
  have hlt : (internalSelectedEdges χ r (componentSupport χ r x)).card <
      (internalSelectedEdges χ (r.replace e) (componentSupport χ r x)).card := by
    rw [hcard]
    exact Nat.lt_succ_self _
  exact (Nat.not_lt_of_ge htie) hlt

set_option linter.style.haveILetI false in
/-- Finite same-color choices supply both maxima. Surjectivity and `0<n`
are only used to produce an initial choice and a component vertex. -/
theorem exists_lexLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n) :
    ∃ (r : RepresentativeChoice χ) (x : Fin n), LexLargestComponent χ r x := by
  classical
  obtain ⟨r₀, x₀, hsize⟩ := exists_globallyLargestComponent χ hχ hn
  letI : Fintype (HostEdge n) :=
    SimpleGraph.fintypeEdgeSet (⊤ : SimpleGraph (Fin n))
  have hinj : Function.Injective (fun r : RepresentativeChoice χ => r.edge) := by
    intro r s h
    cases r with
    | mk re rp =>
      cases s with
      | mk se sp =>
        cases h
        rfl
  letI : Finite (RepresentativeChoice χ) := Finite.of_injective _ hinj
  letI : Fintype (RepresentativeChoice χ × Fin n) := Fintype.ofFinite _
  let S : Finset (RepresentativeChoice χ × Fin n) :=
    Finset.univ.filter (fun p => (componentSupport χ p.1 p.2).ncard =
      (componentSupport χ r₀ x₀).ncard)
  have hS : S.Nonempty := by
    refine ⟨(r₀, x₀), ?_⟩
    simp [S]
  obtain ⟨⟨r, x⟩, hr, hmax⟩ := Finset.exists_max_image S
    (fun p => (internalSelectedEdges χ p.1 (componentSupport χ p.1 p.2)).card) hS
  have hchosen : (componentSupport χ r x).ncard =
      (componentSupport χ r₀ x₀).ncard := (Finset.mem_filter.mp hr).2
  refine ⟨r, x, ?_, ?_⟩
  · intro r' z
    change (componentSupport χ r' z).ncard ≤ (componentSupport χ r x).ncard
    rw [hchosen]
    exact hsize r' z
  · intro r' z heq
    apply hmax (r', z)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.trans hchosen⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Original selected slots of removed colors are outside the remaining
vertices; every other original selected slot is wholly inside them. -/
structure ResidualSlotPartition
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) : Prop where
  removed_outside : ∀ c ∈ U, EdgeInside Wᶜ (r.edge c).val
  eligible_inside : ∀ c, c ∉ U → EdgeInside W (r.edge c).val

/-- A full original-color choice with the removed prefix slots frozen.
Only eligible slots may change, and their endpoints remain in `W`. -/
structure OriginalResidualChoice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) where
  choice : RepresentativeChoice χ
  prefix_eq : ∀ c ∈ U, choice.edge c = r.edge c
  eligible_inside : ∀ c, c ∉ U → EdgeInside W (choice.edge c).val

/-- Size maximum, then internal-edge maximum, over exactly the choices
preserving this original prefix and the remaining-vertex boundary. -/
def ResidualLexMaximum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) : Prop :=
  (∀ (s : OriginalResidualChoice χ r U W) (z : Fin n), z ∈ W →
    (componentSupport χ s.choice z).ncard ≤
      (componentSupport χ r x).ncard) ∧
  ∀ (s : OriginalResidualChoice χ r U W) (z : Fin n), z ∈ W →
    (componentSupport χ s.choice z).ncard =
      (componentSupport χ r x).ncard →
    (internalSelectedEdges χ s.choice (componentSupport χ s.choice z)).card ≤
      (internalSelectedEdges χ r (componentSupport χ r x)).card

/-- A literal eligible replacement preserves every frozen original slot
and the whole remaining-vertex boundary. -/
def originalResidualReplace
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (e : HostEdge n) (hcolor : χ e ∉ U) (hinside : EdgeInside W e.val) :
    OriginalResidualChoice χ r U W where
  choice := r.replace e
  prefix_eq := by
    intro c hc
    have hne : c ≠ χ e := by
      intro heq
      exact hcolor (heq ▸ hc)
    exact r.replace_edge_other e hne
  eligible_inside := by
    intro c hc
    by_cases heq : c = χ e
    · rw [heq, r.replace_edge_same e]
      exact hinside
    · rw [r.replace_edge_other e heq]
      exact hpartition.eligible_inside c hc

/-- Every eligible original color appearing wholly inside this WHOLE
original component has its literal original selected slot inside the same
component. This is the first input for an entire eligible interior choice. -/
theorem eligible_inside_color_selected_inside_of_residualLexMaximum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (hcolor : χ e ∉ U)
    (he : EdgeInside (componentSupport χ r x) e.val) :
    EdgeInside (componentSupport χ r x) (r.edge (χ e)).val := by
  by_contra hnot
  have hx : x ∈ W := hcomponent
    ((mem_componentSupport χ r x x).mpr (SimpleGraph.Reachable.refl x))
  have heW : EdgeInside W e.val := by
    intro v hv
    exact hcomponent (he v hv)
  let s : OriginalResidualChoice χ r U W :=
    originalResidualReplace χ r U W hpartition e hcolor heW
  have hretain : ∀ v, (selectedGraph χ r).Reachable x v →
      ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
    intro v hv
    by_contra hdisconnect
    obtain ⟨a, b, hab, ha, hb⟩ :=
      edge_endpoints_reachable_of_delete_disconnects
        (selectedGraph χ r) (r.edge (χ e)).val hv hdisconnect
    apply hnot
    rw [hab]
    intro w hw
    rcases Sym2.mem_iff.mp hw with hwa | hwb
    · rw [hwa]
      exact (mem_componentSupport χ r x a).mpr ha
    · rw [hwb]
      exact (mem_componentSupport χ r x b).mpr hb
  have hsub : componentSupport χ r x ⊆ componentSupport χ (r.replace e) x := by
    intro v hv
    exact (mem_componentSupport χ (r.replace e) x v).mpr
      ((hretain v ((mem_componentSupport χ r x v).mp hv)).mono
        (delete_selectedEdge_le_replace χ r e))
  have hsizele : (componentSupport χ (r.replace e) x).ncard ≤
      (componentSupport χ r x).ncard := hmax.1 s x hx
  have hsupport : componentSupport χ (r.replace e) x = componentSupport χ r x :=
    (Set.eq_of_subset_of_ncard_le hsub hsizele).symm
  have hsize : (componentSupport χ s.choice x).ncard =
      (componentSupport χ r x).ncard := congrArg Set.ncard hsupport
  have htie := hmax.2 s x hx hsize
  have hsupportS : componentSupport χ s.choice x = componentSupport χ r x := hsupport
  rw [hsupportS] at htie
  have hcard := internalSelectedEdges_card_replace_of_old_not_inside
    χ r (componentSupport χ r x) e he hnot
  have hlt : (internalSelectedEdges χ r (componentSupport χ r x)).card <
      (internalSelectedEdges χ (r.replace e) (componentSupport χ r x)).card := by
    rw [hcard]
    exact Nat.lt_succ_self _
  exact (Nat.not_lt_of_ge htie) hlt

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Original colors outside U occurring on literal host edges inside X. -/
noncomputable def eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) :
    Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun c =>
    c ∉ U ∧ ∃ e : HostEdge n, EdgeInside X e.val ∧ χ e = c)

theorem mem_eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (X : Set (Fin n)) (c : Fin q) :
    c ∈ eligibleInteriorColors χ U X ↔
      c ∉ U ∧ ∃ e : HostEdge n, EdgeInside X e.val ∧ χ e = c := by
  classical
  simp [eligibleInteriorColors]

/-- A literal original inside host edge for every ENTIRE eligible color. -/
structure EligibleInteriorRepresentativeChoice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) where
  edge : {c : Fin q // c ∈ eligibleInteriorColors χ U X} → HostEdge n
  color_eq : ∀ c, χ (edge c) = c.val
  inside : ∀ c, EdgeInside X (edge c).val

def eligibleInteriorSelectedGraph
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    (Set.range fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val)

/-- Every actual selected internal slot has eligible original color;
removed slots avoid W and cannot meet the whole X contained in W. -/
theorem selected_internal_color_mem_eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (c : Fin q) (hinside : EdgeInside (componentSupport χ r x) (r.edge c).val) :
    c ∈ eligibleInteriorColors χ U (componentSupport χ r x) := by
  have hnot : c ∉ U := by
    intro hc
    obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective ((r.edge c).val)
    have ha : a ∈ (r.edge c).val := by
      rw [← hab]
      exact Sym2.mem_mk_left a b
    exact (hpartition.removed_outside c hc a ha) (hcomponent (hinside a ha))
  exact (mem_eligibleInteriorColors χ U (componentSupport χ r x) c).mpr
    ⟨hnot, r.edge c, hinside, r.color_eq c⟩

/-- Every original eligible inside color retains its actual original owner
inside the SAME whole component by the public residual exchange theorem. -/
theorem selected_edge_inside_of_eligibleInterior_color
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (c : Fin q) (hc : c ∈ eligibleInteriorColors χ U (componentSupport χ r x)) :
    EdgeInside (componentSupport χ r x) (r.edge c).val := by
  obtain ⟨hnot, e, he, hcolor⟩ :=
    (mem_eligibleInteriorColors χ U (componentSupport χ r x) c).mp hc
  have hecolor : χ e ∉ U := by simpa only [hcolor] using hnot
  simpa only [hcolor] using
    eligible_inside_color_selected_inside_of_residualLexMaximum
      χ r U W hpartition x hcomponent hmax e hecolor he

/-- The actual original slots supply a connected choice of the ENTIRE
eligible palette, with exact original induced graph and owner coverage. -/
theorem exists_connected_eligible_interior_choice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ∃ s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x),
      (∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U (componentSupport χ r x)},
        s.edge c = r.edge c.val) ∧
      (eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
          (componentSupport χ r x) =
        (selectedGraph χ r).induce (componentSupport χ r x) ∧
      ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
        (componentSupport χ r x)).Connected ∧
      ∀ c : Fin q,
        c ∈ eligibleInteriorColors χ U (componentSupport χ r x) ↔
          EdgeInside (componentSupport χ r x) (r.edge c).val := by
  let X := componentSupport χ r x
  let s : EligibleInteriorRepresentativeChoice χ U X :=
    { edge := fun c => r.edge c.val
      color_eq := fun c => r.color_eq c.val
      inside := fun c => selected_edge_inside_of_eligibleInterior_color
        χ r U W hpartition x hcomponent hmax c.val c.property }
  have hgraph : (eligibleInteriorSelectedGraph χ U X s).induce X =
      (selectedGraph χ r).induce X := by
    ext a b
    change
      (s(a.val, b.val) ∈ Set.range
        (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} =>
          (r.edge c.val).val) ∧ a.val ≠ b.val) ↔
      (s(a.val, b.val) ∈ Set.range (fun c : Fin q => (r.edge c).val) ∧
        a.val ≠ b.val)
    constructor
    · rintro ⟨⟨c, hc⟩, hne⟩
      exact ⟨⟨c.val, hc⟩, hne⟩
    · rintro ⟨⟨c, hc⟩, hne⟩
      have hval : (r.edge c).val = s(a.val, b.val) := hc
      have hinside : EdgeInside X (r.edge c).val := by
        rw [hval]
        intro z hz
        rcases Sym2.mem_iff.mp hz with hza | hzb
        · rw [hza]
          exact a.property
        · rw [hzb]
          exact b.property
      have hcolor : c ∈ eligibleInteriorColors χ U X :=
        selected_internal_color_mem_eligibleInteriorColors
          χ r U W hpartition x hcomponent c hinside
      exact ⟨⟨⟨c, hcolor⟩, hc⟩, hne⟩
  have hconn : ((selectedGraph χ r).induce X).Connected :=
    ((selectedGraph χ r).connectedComponentMk x).connected_toSimpleGraph
  refine ⟨s, ?_, hgraph, ?_, ?_⟩
  · intro c
    rfl
  · rw [hgraph]
    exact hconn
  · intro c
    exact ⟨selected_edge_inside_of_eligibleInterior_color
        χ r U W hpartition x hcomponent hmax c,
      selected_internal_color_mem_eligibleInteriorColors
        χ r U W hpartition x hcomponent c⟩

/-- Replace ALL eligible palette slots and keep EVERY other original slot. -/
noncomputable def EligibleInteriorRepresentativeChoice.extend
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ) :
    RepresentativeChoice χ := by
  classical
  refine
    { edge := fun c => if hc : c ∈ eligibleInteriorColors χ U X then
        s.edge ⟨c, hc⟩ else r.edge c
      color_eq := ?_ }
  intro c
  by_cases hc : c ∈ eligibleInteriorColors χ U X
  · simp [hc, s.color_eq]
  · simp [hc, r.color_eq]

theorem EligibleInteriorRepresentativeChoice.extend_edge_eligible
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ)
    (c : {c : Fin q // c ∈ eligibleInteriorColors χ U X}) :
    (s.extend r).edge c.val = s.edge c := by
  classical
  simp [EligibleInteriorRepresentativeChoice.extend, c.property]

theorem EligibleInteriorRepresentativeChoice.extend_edge_noneligible
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ)
    {c : Fin q} (hc : c ∉ eligibleInteriorColors χ U X) :
    (s.extend r).edge c = r.edge c := by
  classical
  simp [EligibleInteriorRepresentativeChoice.extend, hc]

/-- Every valid entire eligible choice extends inside the exact original
U-prefix/W family BEFORE any extremal/connectedness application. -/
noncomputable def EligibleInteriorRepresentativeChoice.asOriginalResidualChoice
    {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x)) :
    OriginalResidualChoice χ r U W where
  choice := s.extend r
  prefix_eq := by
    intro c hc
    have hnot : c ∉ eligibleInteriorColors χ U (componentSupport χ r x) := by
      intro hmem
      exact ((mem_eligibleInteriorColors χ U (componentSupport χ r x) c).mp hmem).1 hc
    exact s.extend_edge_noneligible r hnot
  eligible_inside := by
    intro c hc
    by_cases hmem : c ∈ eligibleInteriorColors χ U (componentSupport χ r x)
    · rw [s.extend_edge_eligible r ⟨c, hmem⟩]
      intro v hv
      exact hcomponent (s.inside ⟨c, hmem⟩ v hv)
    · rw [s.extend_edge_noneligible r hmem]
      exact hpartition.eligible_inside c hc

theorem selected_edge_outside_of_noneligibleInterior_color
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (c : Fin q) (hc : c ∉ eligibleInteriorColors χ U (componentSupport χ r x)) :
    EdgeInside (componentSupport χ r x)ᶜ (r.edge c).val := by
  intro v hv hvX
  obtain ⟨w, hedge⟩ := Sym2.mem_iff_exists.mp hv
  have hselected : (r.edge c).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, rfl⟩
  have hadj : (selectedGraph χ r).Adj v w := by
    rw [hedge] at hselected
    exact hselected
  have hwX : w ∈ componentSupport χ r x :=
    ((selectedGraph χ r).connectedComponentMk x).mem_supp_of_adj_mem_supp hvX hadj
  have hinside : EdgeInside (componentSupport χ r x) (r.edge c).val := by
    rw [hedge]
    intro z hz
    rcases Sym2.mem_iff.mp hz with hza | hzb
    · rw [hza]
      exact hvX
    · rw [hzb]
      exact hwX
  exact hc (selected_internal_color_mem_eligibleInteriorColors
    χ r U W hpartition x hcomponent c hinside)

theorem eligibleInteriorSelectedGraph_le_extend
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) :
    eligibleInteriorSelectedGraph χ U X s ≤ selectedGraph χ (s.extend r) := by
  intro a b hab
  change s(a, b) ∈ Set.range
    (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
      a ≠ b at hab
  obtain ⟨c, hc⟩ := hab.1
  have hnew : s(a, b) ∈ (selectedGraph χ (s.extend r)).edgeSet := by
    rw [selectedGraph_edgeSet]
    refine ⟨c.val, ?_⟩
    simpa only [s.extend_edge_eligible r c] using hc
  exact hnew

/-- A SUPPLIED CONNECTED entire eligible choice extends in the exact
original residual family with literal palette/other slots and SAME whole X. -/
theorem connected_eligible_choice_has_anchored_residual_extension
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x))
    (hconn : ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
      (componentSupport χ r x)).Connected) :
    ∃ t : OriginalResidualChoice χ r U W,
      (∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U (componentSupport χ r x)},
        t.choice.edge c.val = s.edge c) ∧
      (∀ c : Fin q, c ∉ eligibleInteriorColors χ U (componentSupport χ r x) →
        t.choice.edge c = r.edge c) ∧
      componentSupport χ t.choice x = componentSupport χ r x := by
  let X := componentSupport χ r x
  let G' := selectedGraph χ (s.extend r)
  have hx : x ∈ X := (mem_componentSupport χ r x x).mpr (SimpleGraph.Reachable.refl x)
  have hclosed : ∀ a b, a ∈ X → G'.Adj a b → b ∈ X := by
    intro a b ha hab
    have hmem : s(a, b) ∈ (selectedGraph χ (s.extend r)).edgeSet := hab
    rw [selectedGraph_edgeSet] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hval : ((s.extend r).edge c).val = s(a, b) := hc
    by_cases hcolor : c ∈ eligibleInteriorColors χ U X
    · have hinside : EdgeInside X ((s.extend r).edge c).val := by
        rw [s.extend_edge_eligible r ⟨c, hcolor⟩]
        exact s.inside ⟨c, hcolor⟩
      apply hinside b
      rw [hval]
      exact Sym2.mem_mk_right a b
    · have hedge : (s.extend r).edge c = r.edge c := s.extend_edge_noneligible r hcolor
      have hout := selected_edge_outside_of_noneligibleInterior_color
        χ r U W hpartition x hcomponent c hcolor
      have hold : (r.edge c).val = s(a, b) := by
        rw [← hedge]
        exact hval
      have hnot : a ∉ X := hout a (by rw [hold]; exact Sym2.mem_mk_left a b)
      exact False.elim (hnot ha)
  have hwalk : ∀ a b (p : G'.Walk a b), a ∈ X → b ∈ X := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | cons hab p ih => exact fun ha => ih (hclosed _ _ ha hab)
  let φ : ((eligibleInteriorSelectedGraph χ U X s).induce X) →g G' :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        exact (eligibleInteriorSelectedGraph_le_extend χ r U X s) hab }
  have hsupport : componentSupport χ (s.extend r) x = X := by
    ext v
    constructor
    · intro hv
      obtain ⟨p⟩ := (mem_componentSupport χ (s.extend r) x v).mp hv
      exact hwalk x v p hx
    · intro hv
      obtain ⟨p⟩ := hconn (⟨x, hx⟩ : X) (⟨v, hv⟩ : X)
      exact (mem_componentSupport χ (s.extend r) x v).mpr (p.map φ).reachable
  refine ⟨s.asOriginalResidualChoice r U W hpartition x hcomponent, ?_, ?_, hsupport⟩
  · exact s.extend_edge_eligible r
  · intro c hc
    exact s.extend_edge_noneligible r hc

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Every admissible original-prefix choice inherits the literal U/W partition. -/
theorem OriginalResidualChoice.slotPartition
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {r : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)}
    (t : OriginalResidualChoice χ r U W)
    (hpartition : ResidualSlotPartition χ r U W) :
    ResidualSlotPartition χ t.choice U W where
  removed_outside := by
    intro c hc
    rw [t.prefix_eq c hc]
    exact hpartition.removed_outside c hc
  eligible_inside := t.eligible_inside

/-- Relative residual replacements still fix the SAME original prefix slots. -/
def OriginalResidualChoice.compose
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {r : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)}
    (t : OriginalResidualChoice χ r U W)
    (s : OriginalResidualChoice χ t.choice U W) :
    OriginalResidualChoice χ r U W where
  choice := s.choice
  prefix_eq := by
    intro c hc
    exact (s.prefix_eq c hc).trans (t.prefix_eq c hc)
  eligible_inside := s.eligible_inside

/-- An admissible SAME-X extension inherits the SIZE comparison over the exact
relative original-prefix family. No unrestricted global maximum is inferred. -/
theorem OriginalResidualChoice.sizeMaximum_of_componentSupport_eq
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {r : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)}
    (t : OriginalResidualChoice χ r U W) (x : Fin n)
    (hmax : ResidualLexMaximum χ r U W x)
    (hsupport : componentSupport χ t.choice x = componentSupport χ r x) :
    ∀ (s : OriginalResidualChoice χ t.choice U W) (z : Fin n), z ∈ W →
      (componentSupport χ s.choice z).ncard ≤
        (componentSupport χ t.choice x).ncard := by
  intro s z hz
  have hle := hmax.1 (t.compose s) z hz
  rw [hsupport]
  exact hle

/-- An ORIGINAL eligible X-to-(W∖X) edge has its selected color on a literal
bridge inside the SAME actual component, under just the residual SIZE maximum. -/
theorem eligible_cross_edge_color_is_component_bridge
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hsize : ∀ (t : OriginalResidualChoice χ r U W) (z : Fin n), z ∈ W →
      (componentSupport χ t.choice z).ncard ≤
        (componentSupport χ r x).ncard)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U) :
    ∃ a b : Fin n,
      (r.edge (χ e)).val = s(a, b) ∧
      a ∈ componentSupport χ r x ∧ b ∈ componentSupport χ r x ∧
      (selectedGraph χ r).IsBridge s(a, b) := by
  classical
  have hxW : x ∈ W := hcomponent
    ((mem_componentSupport χ r x x).mpr (SimpleGraph.Reachable.refl x))
  have heW : EdgeInside W e.val := by
    rw [he]
    intro v hv
    rcases Sym2.mem_iff.mp hv with hva | hvy
    · rw [hva]
      exact hcomponent hu
    · rw [hvy]
      exact hyW
  let t : OriginalResidualChoice χ r U W :=
    originalResidualReplace χ r U W hpartition e hcolor heW
  have hureach : (selectedGraph χ r).Reachable x u :=
    (mem_componentSupport χ r x u).mp hu
  have hynot : ¬ (selectedGraph χ r).Reachable x y := by
    intro hreach
    exact hy ((mem_componentSupport χ r x y).mpr hreach)
  have hcuts : ∃ v, (selectedGraph χ r).Reachable x v ∧
      ¬ ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
    by_contra h
    push Not at h
    have hlt := replacement_grows_component χ r e x u y he hureach hynot h
    have hle := hsize t x hxW
    exact (Nat.not_lt_of_ge hle) hlt
  obtain ⟨v, hv, hnot⟩ := hcuts
  obtain ⟨a, b, hab, ha, hb⟩ :=
    edge_endpoints_reachable_of_delete_disconnects
      (selectedGraph χ r) (r.edge (χ e)).val hv hnot
  have hbridge : (selectedGraph χ r).IsBridge (r.edge (χ e)).val := by
    by_contra hnb
    exact hnot (reachable_deleteEdge_of_not_bridge
      (selectedGraph χ r) (r.edge (χ e)).val hnb hv)
  exact ⟨a, b, hab, (mem_componentSupport χ r x a).mpr ha,
    (mem_componentSupport χ r x b).mpr hb, hab ▸ hbridge⟩

/-- Every eligible outgoing original color belongs to the ENTIRE eligible
inside palette; neither properness nor nonempty I is used as a witness. -/
theorem eligible_cross_edge_color_mem_eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U) :
    χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x) := by
  obtain ⟨a, b, hab, ha, hb, _hbridge⟩ :=
    eligible_cross_edge_color_is_component_bridge
      χ r U W hpartition x hcomponent hmax.1 e u y he hu hyW hy hcolor
  have hinside : EdgeInside (componentSupport χ r x) (r.edge (χ e)).val := by
    rw [hab]
    intro v hv
    rcases Sym2.mem_iff.mp hv with hva | hvb
    · rw [hva]
      exact ha
    · rw [hvb]
      exact hb
  exact (mem_eligibleInteriorColors χ U (componentSupport χ r x) (χ e)).mpr
    ⟨hcolor, r.edge (χ e), hinside, r.color_eq (χ e)⟩

/-- Literal ORIGINAL eligible colors whose supplied owner is an actual induced bridge. -/
def eligibleInteriorBridgeColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) : Set (Fin q) :=
  {c | ∃ (hc : c ∈ eligibleInteriorColors χ U X) (a b : X),
    (s.edge ⟨c, hc⟩).val = s(a.val, b.val) ∧
    χ (s.edge ⟨c, hc⟩) = c ∧
    ((eligibleInteriorSelectedGraph χ U X s).induce X).Adj a b ∧
    ((eligibleInteriorSelectedGraph χ U X s).induce X).IsBridge s(a, b)}

/-- Every eligible outgoing ORIGINAL color is an induced bridge color in EVERY
SUPPLIED CONNECTED ENTIRE eligible-I choice on the SAME actual whole X. -/
theorem eligible_cross_edge_color_mem_bridgeColors_of_connected_choice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U)
    (s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x))
    (hconn : ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
      (componentSupport χ r x)).Connected) :
    χ e ∈ eligibleInteriorBridgeColors χ U (componentSupport χ r x) s := by
  let X := componentSupport χ r x
  have hc : χ e ∈ eligibleInteriorColors χ U X :=
    eligible_cross_edge_color_mem_eligibleInteriorColors
      χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
  obtain ⟨t, hslots, _hothers, hsupport⟩ :=
    connected_eligible_choice_has_anchored_residual_extension
      χ r U W hpartition x hcomponent s hconn
  have hpartitionT := t.slotPartition hpartition
  have hcomponentT : componentSupport χ t.choice x ⊆ W := by
    rw [hsupport]
    exact hcomponent
  have huT : u ∈ componentSupport χ t.choice x := by
    rw [hsupport]
    exact hu
  have hyT : y ∉ componentSupport χ t.choice x := by
    rw [hsupport]
    exact hy
  have hsizeT := t.sizeMaximum_of_componentSupport_eq x hmax hsupport
  obtain ⟨a, b, hab, ha, hb, hbridge⟩ :=
    eligible_cross_edge_color_is_component_bridge χ t.choice U W
      hpartitionT x hcomponentT hsizeT e u y he huT hyW hyT hcolor
  have haX : a ∈ X := by rw [hsupport] at ha; exact ha
  have hbX : b ∈ X := by rw [hsupport] at hb; exact hb
  have hliteral : (s.edge ⟨χ e, hc⟩).val = s(a, b) := by
    rw [← hslots ⟨χ e, hc⟩]
    exact hab
  have hfulladj : (selectedGraph χ t.choice).Adj a b := by
    have hmem : s(a, b) ∈ (selectedGraph χ t.choice).edgeSet := by
      rw [selectedGraph_edgeSet]
      exact ⟨χ e, hab⟩
    exact hmem
  have hle : eligibleInteriorSelectedGraph χ U X s ≤ selectedGraph χ t.choice := by
    intro z w hzw
    change s(z, w) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
        z ≠ w at hzw
    obtain ⟨c, hslot⟩ := hzw.1
    have hmem : s(z, w) ∈ (selectedGraph χ t.choice).edgeSet := by
      rw [selectedGraph_edgeSet]
      refine ⟨c.val, ?_⟩
      change (t.choice.edge c.val).val = s(z, w)
      rw [hslots c]
      exact hslot
    exact hmem
  have hinterioradj : (eligibleInteriorSelectedGraph χ U X s).Adj a b := by
    change s(a, b) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
        a ≠ b
    exact ⟨⟨⟨χ e, hc⟩, hliteral⟩, hfulladj.ne⟩
  have hinteriorbridge : (eligibleInteriorSelectedGraph χ U X s).IsBridge s(a, b) :=
    SimpleGraph.IsBridge.anti hle hbridge
  let aX : X := ⟨a, haX⟩
  let bX : X := ⟨b, hbX⟩
  have hinducedbridge :
      ((eligibleInteriorSelectedGraph χ U X s).induce X).IsBridge s(aX, bX) :=
    ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge.isBridge_comap_of_injective
      (eligibleInteriorSelectedGraph χ U X s) (fun z : X => z.val)
      Subtype.val_injective hinteriorbridge
  exact ⟨hc, aX, bX, hliteral, s.color_eq ⟨χ e, hc⟩,
    hinterioradj, hinducedbridge⟩

/-- Full intersection over EVERY CURRENT CONNECTED entire eligible choice. -/
noncomputable def commonEligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) :
    Finset (Fin q) := by
  classical
  exact (eligibleInteriorColors χ U X).filter (fun c =>
    ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      ((eligibleInteriorSelectedGraph χ U X s).induce X).Connected →
        c ∈ eligibleInteriorBridgeColors χ U X s)

/-- One ACTUAL eligible outgoing witness; properness alone does not imply it. -/
def EligibleResidualOutgoing
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (W X : Set (Fin n)) : Prop :=
  ∃ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) ∧
    u ∈ X ∧ y ∈ W ∧ y ∉ X ∧ χ e ∉ U

/-- All eligible outgoing original colors lie in the FULL common bridge intersection. -/
theorem eligible_cross_edge_color_mem_commonEligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U) :
    χ e ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨eligible_cross_edge_color_mem_eligibleInteriorColors
    χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor, ?_⟩
  intro s hs
  exact eligible_cross_edge_color_mem_bridgeColors_of_connected_choice
    χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor s hs

/-- An actual eligible outgoing edge supplies a nonempty FULL common seed. -/
theorem commonEligibleInteriorColors_nonempty_of_eligibleOutgoing
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (hout : EligibleResidualOutgoing χ U W (componentSupport χ r x)) :
    (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty := by
  obtain ⟨e, u, y, he, hu, hyW, hy, hcolor⟩ := hout
  exact ⟨χ e, eligible_cross_edge_color_mem_commonEligibleInteriorColors
    χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor⟩

/-- Residual outgoing package: derive one connected ENTIRE eligible choice;
cover every eligible outgoing color in the full common seed; keep the exact
empty-outgoing branch and singleton/empty-I control explicit. -/
theorem eligible_residual_outgoing_common_bridge_package
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    (∃ s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x),
      ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
        (componentSupport χ r x)).Connected) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
      χ e ∉ U →
      χ e ∈ commonEligibleInteriorColors χ U (componentSupport χ r x)) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ r x) →
      (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty) ∧
    (¬ EligibleResidualOutgoing χ U W (componentSupport χ r x) →
      ∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
        χ e ∈ U) ∧
    (eligibleInteriorColors χ U (componentSupport χ r x) = ∅ →
      ¬ EligibleResidualOutgoing χ U W (componentSupport χ r x)) := by
  classical
  obtain ⟨s, _hslots, _hgraph, hs, _howners⟩ :=
    exists_connected_eligible_interior_choice χ r U W hpartition x hcomponent hmax
  refine ⟨⟨s, hs⟩, ?_, ?_, ?_, ?_⟩
  · intro e u y he hu hyW hy hcolor
    exact eligible_cross_edge_color_mem_commonEligibleInteriorColors
      χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
  · exact commonEligibleInteriorColors_nonempty_of_eligibleOutgoing
      χ r U W hpartition x hcomponent hmax
  · intro hnone e u y he hu hyW hy
    by_contra hcolor
    exact hnone ⟨e, u, y, he, hu, hyW, hy, hcolor⟩
  · intro hempty hout
    obtain ⟨e, u, y, he, hu, hyW, hy, hcolor⟩ := hout
    have hc := eligible_cross_edge_color_mem_eligibleInteriorColors
      χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
    rw [hempty] at hc
    exact Finset.notMem_empty (χ e) hc

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- A same-original-color interior replacement retains the deletion of the
current induced nonbridge and supplies a connected next interior choice. -/
theorem exists_connected_eligible_interior_choice_of_nonbridge_replace
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X)
    (hconn : ((eligibleInteriorSelectedGraph χ U X s).induce X).Connected)
    (f : HostEdge n) (hf : EdgeInside X f.val)
    (hc : χ f ∈ eligibleInteriorColors χ U X)
    (a b : X) (hold : (s.edge ⟨χ f, hc⟩).val = s(a.val, b.val))
    (hnb : ¬ ((eligibleInteriorSelectedGraph χ U X s).induce X).IsBridge s(a, b)) :
    ∃ t : EligibleInteriorRepresentativeChoice χ U X,
      t.edge ⟨χ f, hc⟩ = f ∧
      (∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U X},
        c.val ≠ χ f → t.edge c = s.edge c) ∧
      ((eligibleInteriorSelectedGraph χ U X s).induce X).deleteEdges {s(a, b)} ≤
        (eligibleInteriorSelectedGraph χ U X t).induce X ∧
      ((eligibleInteriorSelectedGraph χ U X t).induce X).Connected := by
  classical
  let F : RepresentativeChoice χ := (s.extend r).replace f
  have hsame : F.edge (χ f) = f := (s.extend r).replace_edge_same f
  have hother : ∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U X},
      c.val ≠ χ f → F.edge c.val = s.edge c := by
    intro c hne
    change ((s.extend r).replace f).edge c.val = s.edge c
    rw [(s.extend r).replace_edge_other f hne]
    exact s.extend_edge_eligible r c
  let t : EligibleInteriorRepresentativeChoice χ U X :=
    { edge := fun c => F.edge c.val
      color_eq := fun c => F.color_eq c.val
      inside := by
        intro c
        by_cases he : c.val = χ f
        · rw [he, hsame]
          exact hf
        · rw [hother c he]
          exact s.inside c }
  have hle : ((eligibleInteriorSelectedGraph χ U X s).induce X).deleteEdges {s(a, b)} ≤
      (eligibleInteriorSelectedGraph χ U X t).induce X := by
    intro z w hzw
    have hcurrent : (eligibleInteriorSelectedGraph χ U X s).Adj z.val w.val :=
      (SimpleGraph.deleteEdges_adj.mp hzw).1
    have hdeleted : s(z, w) ≠ s(a, b) := by
      simpa using (SimpleGraph.deleteEdges_adj.mp hzw).2
    change s(z.val, w.val) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
      z.val ≠ w.val at hcurrent
    obtain ⟨c, hedge⟩ := hcurrent.1
    change (s.edge c).val = s(z.val, w.val) at hedge
    have hne : c.val ≠ χ f := by
      intro he
      have hcEq : c = ⟨χ f, hc⟩ := Subtype.ext he
      apply hdeleted
      apply Sym2.map.injective (f := fun x : X => x.val) Subtype.val_injective
      change s(z.val, w.val) = s(a.val, b.val)
      calc
        s(z.val, w.val) = (s.edge c).val := hedge.symm
        _ = (s.edge ⟨χ f, hc⟩).val := by rw [hcEq]
        _ = s(a.val, b.val) := hold
    change s(z.val, w.val) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (t.edge c).val) ∧
      z.val ≠ w.val
    refine ⟨⟨c, ?_⟩, hcurrent.2⟩
    change (F.edge c.val).val = s(z.val, w.val)
    rw [hother c hne]
    exact hedge
  have hdelete :
      (((eligibleInteriorSelectedGraph χ U X s).induce X).deleteEdges {s(a, b)}).Connected :=
    SimpleGraph.Preconnected.connected_deleteEdges_of_not_isBridge hconn.preconnected hnb
  refine ⟨t, ?_, ?_, hle, SimpleGraph.Connected.mono hle hdelete⟩
  · exact hsame
  · intro c hne
    exact hother c hne

/-- ALL eligible choices keep EVERY removed original prefix slot unchanged.
This is available before any current-graph or residual maximum use. -/
theorem EligibleInteriorRepresentativeChoice.extend_prefix_eq
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ)
    (c : Fin q) (hc : c ∈ U) :
    (s.extend r).edge c = r.edge c := by
  have hnot : c ∉ eligibleInteriorColors χ U X := by
    intro hmem
    exact ((mem_eligibleInteriorColors χ U X c).mp hmem).1 hc
  exact s.extend_edge_noneligible r hnot

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The entire ORIGINAL eligible inside palette (outside U), with literal original color values. -/
abbrev EligibleInteriorColor (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) :=
  {c : Fin q // c ∈ eligibleInteriorColors χ U X}

/-- The supplied choice's graph on the unchanged subtype vertex carrier. -/
abbrev EligibleInteriorGraph (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) :=
  (eligibleInteriorSelectedGraph χ U X s).induce X

/-- Always delete slots of the SAME original choice; endpoint orientation is immaterial. -/
def EligibleInteriorColorDeletion (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (A : Set (EligibleInteriorColor χ U X)) :
    Set (Sym2 X) :=
  {e | ∃ c ∈ A, ∃ a b : X,
    (s₀.edge c).val = s(a.val, b.val) ∧ e = s(a, b)}

/-- Bridge status of the literal original interior slot, for either endpoint orientation. -/
def OriginalEligibleInteriorBridge (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (c : EligibleInteriorColor χ U X) : Prop :=
  ∀ a b : X, (s₀.edge c).val = s(a.val, b.val) →
    (EligibleInteriorGraph χ U X s₀).IsBridge s(a, b)

/-- Current nonbridge and original lower-rank slots/cuts used in the strict descent. -/
structure EligibleInteriorRankState
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (ρ : EligibleInteriorColor χ U X → ℕ)
    (s : EligibleInteriorRepresentativeChoice χ U X)
    (c : EligibleInteriorColor χ U X) (a b : X) (j : ℕ) : Prop where
  connected : (EligibleInteriorGraph χ U X s).Connected
  rank_eq : ρ c = j
  original_slot : s.edge c = s₀.edge c
  current_slot : (s.edge c).val = s(a.val, b.val)
  nonbridge : ¬ (EligibleInteriorGraph χ U X s).IsBridge s(a, b)
  agrees_le : ∀ d, ρ d ≤ j → s.edge d = s₀.edge d
  lower_cuts : ∀ d, ρ d < j → ∀ u v : X,
    (s₀.edge d).val = s(u.val, v.val) →
    (EligibleInteriorGraph χ U X s₀).IsBridge s(u, v) ∧
    ∀ x y : X, (EligibleInteriorGraph χ U X s).Adj x y →
      s(x, y) ≠ s(u, v) →
      ((EligibleInteriorGraph χ U X s₀).deleteEdges {s(u, v)}).Reachable x y

/-- A same-original-color witness crossing original lower-rank deletion yields
a connected next state at strictly smaller rank, preserving ALL lower cuts. -/
theorem exists_eligible_interior_rank_state_of_birth_witness
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (r : RepresentativeChoice χ)
    (X : Set (Fin n)) (s₀ : EligibleInteriorRepresentativeChoice χ U X)
    (hR : (EligibleInteriorGraph χ U X s₀).Connected)
    (ρ : EligibleInteriorColor χ U X → ℕ)
    (s : EligibleInteriorRepresentativeChoice χ U X)
    (c : EligibleInteriorColor χ U X) (a b : X) (j : ℕ)
    (hstate : EligibleInteriorRankState χ U X s₀ ρ s c a b j)
    (f : HostEdge n) (hf : EdgeInside X f.val) (hfc : χ f = c.val)
    (z w : X) (hfv : f.val = s(z.val, w.val))
    (hbirth : ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
      (EligibleInteriorColorDeletion χ U X s₀ {d | ρ d < j})).Reachable z w) :
    ∃ (t : EligibleInteriorRepresentativeChoice χ U X) (d : EligibleInteriorColor χ U X) (u v : X),
      ρ d < j ∧ EligibleInteriorRankState χ U X s₀ ρ t d u v (ρ d) := by
  classical
  let R := EligibleInteriorGraph χ U X s₀
  let Q := EligibleInteriorGraph χ U X s
  let S := EligibleInteriorColorDeletion χ U X s₀ {d | ρ d < j}
  have hbridgeS : ∀ e ∈ S, R.IsBridge e := by
    intro e he
    change ∃ d : EligibleInteriorColor χ U X, ρ d < j ∧ ∃ u v : X,
      (s₀.edge d).val = s(u.val, v.val) ∧ e = s(u, v) at he
    rcases he with ⟨d, hd, u, v, hslot, rfl⟩
    exact (hstate.lower_cuts d hd u v hslot).1
  let E : Finset (EligibleInteriorColor χ U X) := Finset.univ.filter (fun d =>
    ρ d < j ∧ ∃ u v : X, (s₀.edge d).val = s(u.val, v.val) ∧
      ¬ (R.deleteEdges {s(u, v)}).Reachable z w)
  have hmemE : ∀ d : EligibleInteriorColor χ U X, d ∈ E ↔
      ρ d < j ∧ ∃ u v : X, (s₀.edge d).val = s(u.val, v.val) ∧
        ¬ (R.deleteEdges {s(u, v)}).Reachable z w := by
    intro d
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
  have hEne : E.Nonempty := by
    obtain ⟨e, heS, hcross⟩ := exists_crossed_bridge_cut R hR S hbridgeS hbirth
    change ∃ d : EligibleInteriorColor χ U X, ρ d < j ∧ ∃ u v : X,
      (s₀.edge d).val = s(u.val, v.val) ∧ e = s(u, v) at heS
    rcases heS with ⟨d, hd, u, v, hslot, rfl⟩
    exact ⟨d, (hmemE d).mpr ⟨hd, u, v, hslot, hcross⟩⟩
  obtain ⟨d, hdE, hmin⟩ := Finset.exists_min_image E ρ hEne
  rcases (hmemE d).mp hdE with ⟨hdj, u, v, horiginal, hcross⟩
  have hlabel_ne : ∀ e : EligibleInteriorColor χ U X, ρ e < j → e.val ≠ χ f := by
    intro e he hlabel
    have hec : e = c := Subtype.ext (hlabel.trans hfc)
    have hbad : j < j := by simpa only [hec, hstate.rank_eq] using he
    exact (Nat.lt_irrefl j) hbad
  have hfRespectsLower : ∀ e : EligibleInteriorColor χ U X, ρ e < ρ d → ∀ x y : X,
      (s₀.edge e).val = s(x.val, y.val) →
      (R.deleteEdges {s(x, y)}).Reachable z w := by
    intro e he x y hslot
    by_contra hnot
    have heE : e ∈ E := (hmemE e).mpr
      ⟨Nat.lt_trans he hdj, x, y, hslot, hnot⟩
    exact (Nat.lt_irrefl (ρ d)) (Nat.lt_of_le_of_lt (hmin e heE) he)
  have hslotAdj : ∀ (p : EligibleInteriorRepresentativeChoice χ U X) (e : EligibleInteriorColor χ U X)
      (x y : X), (p.edge e).val = s(x.val, y.val) →
      (EligibleInteriorGraph χ U X p).Adj x y := by
    intro p e x y hslot
    have hhost : (⊤ : SimpleGraph (Fin n)).Adj x.val y.val := by
      have hmem : (p.edge e).val ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
        (p.edge e).property
      rw [hslot] at hmem
      exact hmem
    change s(x.val, y.val) ∈ Set.range
      (fun e : EligibleInteriorColor χ U X => (p.edge e).val) ∧ x.val ≠ y.val
    exact ⟨⟨e, hslot⟩, hhost.ne⟩
  have hcF : χ f ∈ eligibleInteriorColors χ U X := by
    rw [hfc]
    exact c.property
  have hcolorC : (⟨χ f, hcF⟩ : EligibleInteriorColor χ U X) = c := Subtype.ext hfc
  have hcurrent : (s.edge ⟨χ f, hcF⟩).val = s(a.val, b.val) := by
    rw [hcolorC]
    exact hstate.current_slot
  obtain ⟨t, hsame, hother, hle, htconn⟩ :=
    exists_connected_eligible_interior_choice_of_nonbridge_replace χ U r X s hstate.connected
      f hf hcF a b hcurrent hstate.nonbridge
  have hdOriginal : s.edge d = s₀.edge d := hstate.agrees_le d (Nat.le_of_lt hdj)
  have htOriginal : t.edge d = s₀.edge d :=
    (hother d (hlabel_ne d hdj)).trans hdOriginal
  let D := Q.deleteEdges {s(a, b)}
  have hD : D.Connected :=
    SimpleGraph.Preconnected.connected_deleteEdges_of_not_isBridge
      hstate.connected.preconnected hstate.nonbridge
  have hDbefore : Q.Adj u v := hslotAdj s d u v (by rw [hdOriginal]; exact horiginal)
  have hpair_ne : s(u, v) ≠ s(a, b) := by
    intro hpair
    have hvalues : s(u.val, v.val) = s(a.val, b.val) :=
      congrArg (Sym2.map (fun x : X => x.val)) hpair
    have hedge : s.edge d = s.edge c := Subtype.ext (by
      calc
        (s.edge d).val = (s₀.edge d).val := congrArg Subtype.val hdOriginal
        _ = s(u.val, v.val) := horiginal
        _ = s(a.val, b.val) := hvalues
        _ = (s.edge c).val := hstate.current_slot.symm)
    apply hlabel_ne d hdj
    calc
      d.val = χ (s.edge d) := (s.color_eq d).symm
      _ = χ (s.edge c) := congrArg χ hedge
      _ = c.val := s.color_eq c
      _ = χ f := hfc.symm
  have hDb : D.Adj u v := SimpleGraph.deleteEdges_adj.mpr
    ⟨hDbefore, by simpa only [Set.mem_singleton_iff] using hpair_ne⟩
  have hrespectD : ∀ {x y : X}, D.Adj x y → s(x, y) ≠ s(u, v) →
      (R.deleteEdges {s(u, v)}).Reachable x y := by
    intro x y hxy hne
    exact (hstate.lower_cuts d hdj u v horiginal).2 x y
      (SimpleGraph.deleteEdges_adj.mp hxy).1 hne
  have hf_ne : s(z, w) ≠ s(u, v) := by
    intro hpair
    have hvalues : s(z.val, w.val) = s(u.val, v.val) :=
      congrArg (Sym2.map (fun x : X => x.val)) hpair
    have hedge : f = s₀.edge d := Subtype.ext (hfv.trans (hvalues.trans horiginal.symm))
    apply hlabel_ne d hdj
    calc
      d.val = χ (s₀.edge d) := (s₀.color_eq d).symm
      _ = χ f := by rw [← hedge]
  have hfNext : (EligibleInteriorGraph χ U X t).Adj z w :=
    hslotAdj t ⟨χ f, hcF⟩ z w (by rw [hsame]; exact hfv)
  have hnextnb : ¬ (EligibleInteriorGraph χ U X t).IsBridge s(u, v) :=
    not_isBridge_of_crossing_extra_edge R D (EligibleInteriorGraph χ U X t)
      (u := u) (v := v) (a := z) (b := w) hR
      (hslotAdj s₀ d u v horiginal) (hstate.lower_cuts d hdj u v horiginal).1
      hD hDb hrespectD hle hfNext hf_ne hcross
  refine ⟨t, d, u, v, hdj, ?_⟩
  refine
    { connected := htconn
      rank_eq := rfl
      original_slot := htOriginal
      current_slot := by rw [htOriginal]; exact horiginal
      nonbridge := hnextnb
      agrees_le := ?_
      lower_cuts := ?_ }
  · intro e he
    have hej : ρ e < j := Nat.lt_of_le_of_lt he hdj
    exact (hother e (hlabel_ne e hej)).trans (hstate.agrees_le e (Nat.le_of_lt hej))
  · intro e he x y hslot
    have hej : ρ e < j := Nat.lt_trans he hdj
    refine ⟨(hstate.lower_cuts e hej x y hslot).1, ?_⟩
    intro p q hpq hneq
    change s(p.val, q.val) ∈ Set.range
      (fun k : EligibleInteriorColor χ U X => (t.edge k).val) ∧ p.val ≠ q.val at hpq
    obtain ⟨k, hk⟩ := hpq.1
    change (t.edge k).val = s(p.val, q.val) at hk
    by_cases hkc : k.val = χ f
    · have hkEq : k = (⟨χ f, hcF⟩ : EligibleInteriorColor χ U X) := Subtype.ext hkc
      have hnew : f.val = s(p.val, q.val) := by
        calc
          f.val = (t.edge ⟨χ f, hcF⟩).val := congrArg Subtype.val hsame.symm
          _ = (t.edge k).val := by rw [hkEq]
          _ = s(p.val, q.val) := hk
      have hpair : s(p, q) = s(z, w) := by
        apply Sym2.map.injective (f := fun x : X => x.val) Subtype.val_injective
        change s(p.val, q.val) = s(z.val, w.val)
        exact hnew.symm.trans hfv
      rcases Sym2.eq_iff.mp hpair with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · rw [hp, hq]
        exact hfRespectsLower e he x y hslot
      · rw [hp, hq]
        exact (hfRespectsLower e he x y hslot).symm
    · have hretained : t.edge k = s.edge k := hother k hkc
      have hQslot : (s.edge k).val = s(p.val, q.val) := by
        rw [← hretained]
        exact hk
      exact (hstate.lower_cuts e hej x y hslot).2 p q
        (hslotAdj s k p q hQslot) hneq

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Add every ELIGIBLE ORIGINAL color of an ORIGINAL inside-X edge crossing the deletion
of the SAME ORIGINAL selected slots in A. No current representative is used. -/
noncomputable def eligibleInteriorClosureNext
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (A : Finset (EligibleInteriorColor χ U X)) :
    Finset (EligibleInteriorColor χ U X) := by
  classical
  exact A ∪ Finset.univ.filter (fun c =>
    ∃ f : HostEdge n, EdgeInside X f.val ∧ χ f = c.val ∧
      ∃ z w : X, f.val = s(z.val, w.val) ∧
        ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
          (EligibleInteriorColorDeletion χ U X s₀ (A : Set (EligibleInteriorColor χ U X)))).Reachable z w)

/-- The literal finite-palette recurrence, starting from the supplied seed. -/
noncomputable def eligibleInteriorClosureStages
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X)) :
    ℕ → Finset (EligibleInteriorColor χ U X)
  | 0 => S₀
  | i + 1 => eligibleInteriorClosureNext χ U X s₀ (eligibleInteriorClosureStages χ U X s₀ S₀ i)

theorem eligibleInteriorClosureStages_mono
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X)) :
    Monotone (eligibleInteriorClosureStages χ U X s₀ S₀) := by
  classical
  intro i j hij
  exact Nat.le_induction (m := i)
    (P := fun k _ => eligibleInteriorClosureStages χ U X s₀ S₀ i ⊆
      eligibleInteriorClosureStages χ U X s₀ S₀ k)
    (by intro c hc; exact hc)
    (fun k _ ih c hc => by
      change c ∈ eligibleInteriorClosureStages χ U X s₀ S₀ k ∪ Finset.univ.filter _
      exact Finset.mem_union.mpr (Or.inl (ih hc)))
    j hij

/-- Derived recurrence/rank facts needed by the original-slot descent caller.
The witness assertion excludes the outside sentinel N+1. -/
structure EligibleInteriorCumulativeBirthRank
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X))
    (N : ℕ) (ρ : EligibleInteriorColor χ U X → ℕ) : Prop where
  cumulative_monotone : Monotone (eligibleInteriorClosureStages χ U X s₀ S₀)
  seed_subset : ∀ i, S₀ ⊆ eligibleInteriorClosureStages χ U X s₀ S₀ i
  bounded : ∀ c, ρ c ≤ N + 1
  zero_iff : ∀ c, ρ c = 0 ↔ c ∈ S₀
  mem_iff : ∀ c j, j ≤ N →
    (ρ c ≤ j ↔ c ∈ eligibleInteriorClosureStages χ U X s₀ S₀ j)
  outside_iff : ∀ c, ρ c = N + 1 ↔ c ∉ eligibleInteriorClosureStages χ U X s₀ S₀ N
  lower_eq : ∀ j, 0 < j → j ≤ N + 1 →
    {c : EligibleInteriorColor χ U X | ρ c < j} =
      (eligibleInteriorClosureStages χ U X s₀ S₀ (j - 1) : Set (EligibleInteriorColor χ U X))
  birth_witness : ∀ c, 0 < ρ c → ρ c ≤ N →
    ∃ f : HostEdge n, EdgeInside X f.val ∧ χ f = c.val ∧
      ∃ z w : X, f.val = s(z.val, w.val) ∧
        ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
          (EligibleInteriorColorDeletion χ U X s₀ {d | ρ d < ρ c})).Reachable z w

/-- Construct least membership ranks through N, assign outside colors N+1,
and derive every positive birth witness directly from the actual recurrence. -/
theorem exists_original_eligible_interior_cumulative_birth_rank
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X) (S₀ : Finset (EligibleInteriorColor χ U X))
    (N : ℕ) :
    ∃ ρ : EligibleInteriorColor χ U X → ℕ, EligibleInteriorCumulativeBirthRank χ U X s₀ S₀ N ρ := by
  classical
  let A := eligibleInteriorClosureStages χ U X s₀ S₀
  let ρ : EligibleInteriorColor χ U X → ℕ := fun c =>
    if hc : c ∈ A N then
      Nat.find (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩)
    else N + 1
  have hmono : Monotone A := eligibleInteriorClosureStages_mono χ U X s₀ S₀
  have hmem : ∀ c j, j ≤ N → (ρ c ≤ j ↔ c ∈ A j) := by
    intro c j hj
    by_cases hc : c ∈ A N
    · have hρ : ρ c = Nat.find (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) := by
        simp only [ρ, dite_eq_left hc]
      rw [hρ]
      constructor
      · intro hle
        exact hmono hle (Nat.find_spec (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩))
      · intro hborn
        exact Nat.find_min' (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) hborn
    · have hρ : ρ c = N + 1 := by simp only [ρ, dite_eq_right hc]
      constructor
      · intro hle
        omega
      · intro hborn
        exact False.elim (hc (hmono hj hborn))
  have hlower : ∀ j, 0 < j → j ≤ N + 1 →
      {c : EligibleInteriorColor χ U X | ρ c < j} =
        (A (j - 1) : Set (EligibleInteriorColor χ U X)) := by
    intro j hj hNj
    ext c
    change ρ c < j ↔ c ∈ A (j - 1)
    have hpre : j - 1 ≤ N := by omega
    constructor
    · intro hc
      exact (hmem c (j - 1) hpre).mp (by omega)
    · intro hc
      have hle := (hmem c (j - 1) hpre).mpr hc
      omega
  refine ⟨ρ, ?_⟩
  refine
    { cumulative_monotone := hmono
      seed_subset := ?_
      bounded := ?_
      zero_iff := ?_
      mem_iff := hmem
      outside_iff := ?_
      lower_eq := hlower
      birth_witness := ?_ }
  · intro i
    exact hmono (Nat.zero_le i)
  · intro c
    by_cases hc : c ∈ A N
    · have hρ : ρ c = Nat.find (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) := by
        simp only [ρ, dite_eq_left hc]
      have hle := Nat.find_min' (show ∃ i : ℕ, c ∈ A i from ⟨N, hc⟩) hc
      omega
    · simpa only [ρ, dite_eq_right hc] using (Nat.le_refl (N + 1))
  · intro c
    have hzero := hmem c 0 (Nat.zero_le N)
    change ρ c ≤ 0 ↔ c ∈ S₀ at hzero
    constructor
    · intro hc
      exact hzero.mp (by omega)
    · intro hc
      have hle := hzero.mpr hc
      omega
  · intro c
    constructor
    · intro hsent hc
      have hle := (hmem c N (Nat.le_refl N)).mpr hc
      omega
    · intro hc
      have hcA : c ∉ A N := hc
      simp only [ρ, dite_eq_right hcA]
  · intro c hpos hNc
    have hcA : c ∈ A (ρ c) := (hmem c (ρ c) hNc).mp (Nat.le_refl (ρ c))
    have hpre : ρ c - 1 ≤ N := by omega
    have hcNot : c ∉ A (ρ c - 1) := by
      intro hc
      have hle := (hmem c (ρ c - 1) hpre).mpr hc
      omega
    have hsucc : ρ c = (ρ c - 1) + 1 := by omega
    rw [hsucc] at hcA
    change c ∈ A (ρ c - 1) ∪ Finset.univ.filter _ at hcA
    rcases Finset.mem_union.mp hcA with hcOld | hcNew
    · exact False.elim (hcNot hcOld)
    · have hw := (Finset.mem_filter.mp hcNew).2
      rcases hw with ⟨f, hf, hfc, z, w, hfv, hcross⟩
      refine ⟨f, hf, hfc, z, w, hfv, ?_⟩
      rw [hlower (ρ c) hpos (by omega)]
      exact hcross

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem no_eligible_interior_rank_state_of_cumulative_birth
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (r : RepresentativeChoice χ)
    (X : Set (Fin n)) (s₀ : EligibleInteriorRepresentativeChoice χ U X)
    (hR : (EligibleInteriorGraph χ U X s₀).Connected)
    (S₀ : Finset (EligibleInteriorColor χ U X))
    (hcommon : ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      (EligibleInteriorGraph χ U X s).Connected →
      ∀ c ∈ S₀, OriginalEligibleInteriorBridge χ U X s c)
    (N : ℕ) (ρ : EligibleInteriorColor χ U X → ℕ)
    (hrank : EligibleInteriorCumulativeBirthRank χ U X s₀ S₀ N ρ) :
    ∀ j, j ≤ N → ∀ (s : EligibleInteriorRepresentativeChoice χ U X)
      (c : EligibleInteriorColor χ U X) (a b : X),
      EligibleInteriorRankState χ U X s₀ ρ s c a b j → False := by
  classical
  intro j
  refine Nat.strong_induction_on j ?_
  intro k ih hk s c a b hstate
  by_cases hk0 : k = 0
  · have hc0 : ρ c = 0 := hstate.rank_eq.trans hk0
    have hcS₀ : c ∈ S₀ := (hrank.zero_iff c).mp hc0
    exact hstate.nonbridge
      (hcommon s hstate.connected c hcS₀ a b hstate.current_slot)
  · have hpos : 0 < ρ c := by
      have heq := hstate.rank_eq
      omega
    have hNc : ρ c ≤ N := by
      have heq := hstate.rank_eq
      omega
    obtain ⟨f, hf, hfc, z, w, hfv, hbirth⟩ := hrank.birth_witness c hpos hNc
    have hbirthk : ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
        (EligibleInteriorColorDeletion χ U X s₀ {d | ρ d < k})).Reachable z w := by
      simpa only [hstate.rank_eq] using hbirth
    obtain ⟨t, d, u, v, hdk, hnext⟩ :=
      exists_eligible_interior_rank_state_of_birth_witness
        χ U r X s₀ hR ρ s c a b k hstate f hf hfc z w hfv hbirthk
    exact ih (ρ d) hdk (by omega) t d u v hnext

theorem original_eligible_interior_bridges_of_cumulative_birth
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (r : RepresentativeChoice χ)
    (X : Set (Fin n)) (s₀ : EligibleInteriorRepresentativeChoice χ U X)
    (hR : (EligibleInteriorGraph χ U X s₀).Connected)
    (S₀ : Finset (EligibleInteriorColor χ U X))
    (hcommon : ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      (EligibleInteriorGraph χ U X s).Connected →
      ∀ c ∈ S₀, OriginalEligibleInteriorBridge χ U X s c)
    (N : ℕ) (ρ : EligibleInteriorColor χ U X → ℕ)
    (hrank : EligibleInteriorCumulativeBirthRank χ U X s₀ S₀ N ρ) :
    ∀ j, j ≤ N → ∀ c : EligibleInteriorColor χ U X, ρ c = j →
      OriginalEligibleInteriorBridge χ U X s₀ c := by
  classical
  intro j
  refine Nat.strong_induction_on j ?_
  intro k ih hk c hck a b hslot
  by_contra hnb
  have hstate : EligibleInteriorRankState χ U X s₀ ρ s₀ c a b k := by
    refine
      { connected := hR
        rank_eq := hck
        original_slot := rfl
        current_slot := hslot
        nonbridge := hnb
        agrees_le := by intro d _; rfl
        lower_cuts := ?_ }
    intro d hdk u v hdslot
    have hdN : ρ d ≤ N := by omega
    have hbridge : (EligibleInteriorGraph χ U X s₀).IsBridge s(u, v) :=
      ih (ρ d) hdk hdN d rfl u v hdslot
    refine ⟨hbridge, ?_⟩
    intro x y hxy hne
    have hdel : ((EligibleInteriorGraph χ U X s₀).deleteEdges {s(u, v)}).Adj x y :=
      (SimpleGraph.deleteEdges_adj).mpr
        ⟨hxy, by simpa only [Set.mem_singleton_iff] using hne⟩
    exact hdel.reachable
  exact no_eligible_interior_rank_state_of_cumulative_birth
    χ U r X s₀ hR S₀ hcommon N ρ hrank k hk s₀ c a b hstate

/-- A nonempty ORIGINAL eligible seed common to EVERY current connected choice
has an INITIAL-original-slot bridge-color closure covering ALL ELIGIBLE inside crossing colors.
No rank, birth witness, exchange, descended state or closure premise is supplied. -/
theorem exists_original_eligible_interior_bridge_color_closure
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n))
    (s₀ : EligibleInteriorRepresentativeChoice χ U X)
    (hR : (EligibleInteriorGraph χ U X s₀).Connected)
    (S₀ : Finset (EligibleInteriorColor χ U X)) (hne : S₀.Nonempty)
    (hcommon : ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      (EligibleInteriorGraph χ U X s).Connected →
      ∀ c ∈ S₀, OriginalEligibleInteriorBridge χ U X s c) :
    ∃ A : Finset (EligibleInteriorColor χ U X),
      S₀ ⊆ A ∧ A.Nonempty ∧
      (∀ c ∈ A, OriginalEligibleInteriorBridge χ U X s₀ c) ∧
      ∀ (f : HostEdge n), EdgeInside X f.val → χ f ∉ U →
        ∀ z w : X, f.val = s(z.val, w.val) →
        ¬ ((EligibleInteriorGraph χ U X s₀).deleteEdges
          (EligibleInteriorColorDeletion χ U X s₀ (A : Set (EligibleInteriorColor χ U X)))).Reachable z w →
        ∃ hc : χ f ∈ eligibleInteriorColors χ U X, ⟨χ f, hc⟩ ∈ A := by
  classical
  let C := EligibleInteriorColor χ U X
  let A := eligibleInteriorClosureStages χ U X s₀ S₀
  obtain ⟨_ρ₀, hzeroRank⟩ := exists_original_eligible_interior_cumulative_birth_rank χ U X s₀ S₀ 0
  have hmono : Monotone A := hzeroRank.cumulative_monotone
  let τ : C → ℕ := fun c =>
    if hex : ∃ i : ℕ, c ∈ A i then Nat.find hex else 0
  obtain ⟨c₀, hc₀⟩ := hne
  have huniv : (Finset.univ : Finset C).Nonempty := ⟨c₀, Finset.mem_univ c₀⟩
  obtain ⟨d, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset C) τ huniv
  let N := τ d
  have htop : ∀ i, A i ⊆ A N := by
    intro i c hc
    have hex : ∃ k : ℕ, c ∈ A k := ⟨i, hc⟩
    have hτ : τ c = Nat.find hex := by simp only [τ, dite_eq_left hex]
    have hborn : c ∈ A (τ c) := by
      rw [hτ]
      exact Nat.find_spec hex
    exact hmono (hmax c (Finset.mem_univ c)) hborn
  have hfixed : A (N + 1) = A N := by
    ext c
    constructor
    · intro hc
      exact htop (N + 1) hc
    · intro hc
      exact hmono (Nat.le_succ N) hc
  obtain ⟨ρ, hrank⟩ := exists_original_eligible_interior_cumulative_birth_rank χ U X s₀ S₀ N
  have hbridges : ∀ c ∈ A N, OriginalEligibleInteriorBridge χ U X s₀ c := by
    intro c hc
    have hcN : ρ c ≤ N := (hrank.mem_iff c N (Nat.le_refl N)).mpr hc
    exact original_eligible_interior_bridges_of_cumulative_birth
      χ U r X s₀ hR S₀ hcommon N ρ hrank (ρ c) hcN c rfl
  refine ⟨A N, hrank.seed_subset N, ⟨c₀, hrank.seed_subset N hc₀⟩, hbridges, ?_⟩
  intro f hf hcolor z w hfv hcross
  have hc : χ f ∈ eligibleInteriorColors χ U X :=
    (mem_eligibleInteriorColors χ U X (χ f)).mpr ⟨hcolor, f, hf, rfl⟩
  let c : C := ⟨χ f, hc⟩
  have hnext : c ∈ A (N + 1) := by
    change c ∈ A N ∪ Finset.univ.filter _
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ c, f, hf, rfl, z, w, hfv, hcross⟩))
  refine ⟨hc, ?_⟩
  change c ∈ A N
  rw [hfixed] at hnext
  exact hnext

theorem originalEligibleBridge_of_palette_member
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) (c : EligibleInteriorColor χ U X)
    (hc : c.val ∈ eligibleInteriorBridgeColors χ U X s) :
    OriginalEligibleInteriorBridge χ U X s c := by
  change ∃ (hc' : c.val ∈ eligibleInteriorColors χ U X) (u v : X),
    (s.edge ⟨c.val, hc'⟩).val = s(u.val, v.val) ∧
    χ (s.edge ⟨c.val, hc'⟩) = c.val ∧
    (EligibleInteriorGraph χ U X s).Adj u v ∧
    (EligibleInteriorGraph χ U X s).IsBridge s(u, v) at hc
  rcases hc with ⟨hc', u, v, hslot, _hcolor, _hadj, hbridge⟩
  have howner : (⟨c.val, hc'⟩ : EligibleInteriorColor χ U X) = c := Subtype.ext rfl
  rw [howner] at hslot
  intro a b hab
  have hvalues : s(a.val, b.val) = s(u.val, v.val) := hab.symm.trans hslot
  have hpairs : s(a, b) = s(u, v) :=
    Sym2.map.injective (f := fun z : X => z.val) Subtype.val_injective
      (by simpa only [Sym2.map_mk] using hvalues)
  rw [hpairs]
  exact hbridge

/-- Actual residual FULL-common-seed caller. Before closure, every CURRENT
CONNECTED ENTIRE eligible choice is admitted in the exact original U/W family
with its literal slots and SAME-X. Derive INITIAL-original-slot bridge closure
retaining ALL full common colors and covering ALL ELIGIBLE inside crossing
colors. No rank, recurrence/birth/state/fixed-point/closure premise is supplied. -/
theorem exists_original_residual_eligible_bridge_closure_with_full_common_seed
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (s₀ : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x))
    (hR : (EligibleInteriorGraph χ U (componentSupport χ r x) s₀).Connected)
    (hneFull : (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty) :
    (∀ s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x),
      (EligibleInteriorGraph χ U (componentSupport χ r x) s).Connected →
      ∃ t : OriginalResidualChoice χ r U W,
        (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
          t.choice.edge c.val = s.edge c) ∧
        (∀ c : Fin q, c ∉ eligibleInteriorColors χ U (componentSupport χ r x) →
          t.choice.edge c = r.edge c) ∧
        componentSupport χ t.choice x = componentSupport χ r x) ∧
    ∃ A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)),
      (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
        c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
      A.Nonempty ∧
      (∀ c ∈ A, OriginalEligibleInteriorBridge χ U (componentSupport χ r x) s₀ c) ∧
      ∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
        ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
        ¬ ((EligibleInteriorGraph χ U (componentSupport χ r x) s₀).deleteEdges
          (EligibleInteriorColorDeletion χ U (componentSupport χ r x) s₀
            (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))))).Reachable z w →
        ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x),
          ⟨χ f, hc⟩ ∈ A := by
  classical
  let X := componentSupport χ r x
  let C := EligibleInteriorColor χ U X
  have hfamily : ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      (EligibleInteriorGraph χ U X s).Connected →
      ∃ t : OriginalResidualChoice χ r U W,
        (∀ c : C, t.choice.edge c.val = s.edge c) ∧
        (∀ c : Fin q, c ∉ eligibleInteriorColors χ U X → t.choice.edge c = r.edge c) ∧
        componentSupport χ t.choice x = X := by
    intro s hs
    exact connected_eligible_choice_has_anchored_residual_extension
      χ r U W hpartition x hcomponent s hs
  let S₀ : Finset C := Finset.univ.filter (fun c =>
    c.val ∈ commonEligibleInteriorColors χ U X)
  have hne : S₀.Nonempty := by
    obtain ⟨c, hc⟩ := hneFull
    have hcI : c ∈ eligibleInteriorColors χ U X := (Finset.mem_filter.mp hc).1
    let cI : C := ⟨c, hcI⟩
    exact ⟨cI, Finset.mem_filter.mpr ⟨Finset.mem_univ cI, hc⟩⟩
  have hcommon : ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      (EligibleInteriorGraph χ U X s).Connected →
      ∀ c ∈ S₀, OriginalEligibleInteriorBridge χ U X s c := by
    intro s hs c hc
    have hcFull : c.val ∈ commonEligibleInteriorColors χ U X :=
      (Finset.mem_filter.mp hc).2
    have hevery : ∀ t : EligibleInteriorRepresentativeChoice χ U X,
        (EligibleInteriorGraph χ U X t).Connected →
        c.val ∈ eligibleInteriorBridgeColors χ U X t :=
      (Finset.mem_filter.mp hcFull).2
    exact originalEligibleBridge_of_palette_member χ U X s c (hevery s hs)
  obtain ⟨A, hseed, hneA, hbridges, hcover⟩ :=
    exists_original_eligible_interior_bridge_color_closure
      χ U r X s₀ hR S₀ hne hcommon
  refine ⟨hfamily, A, ?_, hneA, hbridges, hcover⟩
  intro c hcFull
  exact hseed (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcFull⟩)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Zero deletion of a connected actual graph leaves exactly one component,
including the singleton/empty eligible-palette stage. -/
theorem connected_component_count_delete_empty
    {V : Type*} (G : SimpleGraph V) (hG : G.Connected) :
    Nat.card (G.deleteEdges (∅ : Set (Sym2 V))).ConnectedComponent = 1 := by
  rw [deleteEdges_empty]
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hG.preconnected.subsingleton_connectedComponent,
      Nonempty.map G.connectedComponentMk hG.nonempty⟩

/-- Literal ORIGINAL r-slot deletion on the actual subtype carrier. -/
def OriginalResidualColorDeletion
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (X : Set (Fin n))
    (A : Set (EligibleInteriorColor χ U X)) : Set (Sym2 X) :=
  {b | ∃ c ∈ A, Sym2.map (fun z : X => z.val) b = (r.edge c.val).val}

/-- A selected original slot meeting W cannot have a removed color. -/
theorem selected_slot_color_not_removed_of_endpoint_in_remaining
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (c : Fin q) (v : Fin n) (hv : v ∈ (r.edge c).val) (hvW : v ∈ W) :
    c ∉ U := by
  intro hc
  exact (hpartition.removed_outside c hc v hv) hvW

/-- Actual-stage palette, allowing zero cuts. FULL-common colors are retained;
ALL eligible original inside crossing colors and ALL outgoing colors are
covered by A, with removed U colors allowed only at the outgoing boundary. -/
theorem exists_original_residual_stage_palette
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ((selectedGraph χ r).induce (componentSupport χ r x)).Connected ∧
    ∃ A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)),
      (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
        c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
      (∀ c ∈ A, ∀ a b : componentSupport χ r x,
        (r.edge c.val).val = s(a.val, b.val) →
        ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge s(a, b)) ∧
      (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
        ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
        ¬ (((selectedGraph χ r).induce (componentSupport χ r x)).deleteEdges
          (OriginalResidualColorDeletion χ r U (componentSupport χ r x)
            (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))))).Reachable z w →
        ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
      (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
        χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
          ⟨χ e, hc⟩ ∈ A) ∧
      ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → A.Nonempty) ∧
      (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → A = ∅) ∧
      (EligibleResidualOutgoing χ U W (componentSupport χ r x) → A.Nonempty) := by
  classical
  let X := componentSupport χ r x
  let C := EligibleInteriorColor χ U X
  let R := (selectedGraph χ r).induce X
  obtain ⟨s₀, hslots, hgraph, hconn, _howners⟩ :=
    exists_connected_eligible_interior_choice χ r U W hpartition x hcomponent hmax
  have hRconn : R.Connected := by
    change ((selectedGraph χ r).induce X).Connected
    rw [← hgraph]
    exact hconn
  have hdelete : ∀ A : Finset C,
      EligibleInteriorColorDeletion χ U X s₀ (A : Set C) =
        OriginalResidualColorDeletion χ r U X (A : Set C) := by
    intro A
    ext e
    change
      (∃ c ∈ (A : Set C), ∃ a b : X,
        (s₀.edge c).val = s(a.val, b.val) ∧ e = s(a, b)) ↔
      ∃ c ∈ (A : Set C),
        Sym2.map (fun z : X => z.val) e = (r.edge c.val).val
    constructor
    · rintro ⟨c, hc, a, b, hslot, rfl⟩
      refine ⟨c, hc, ?_⟩
      rw [Sym2.map_mk, ← hslots c]
      exact hslot.symm
    · rintro ⟨c, hc, hmap⟩
      obtain ⟨a, b⟩ := e
      have hslot : (s₀.edge c).val = s(a.val, b.val) := by
        rw [hslots c]
        simpa only [Sym2.map_mk] using hmap.symm
      exact ⟨c, hc, a, b, hslot, rfl⟩
  obtain ⟨A, hseed, hbridges, hcover, hne, hempty⟩ :
      ∃ A : Finset C,
        (∀ c : C, c.val ∈ commonEligibleInteriorColors χ U X → c ∈ A) ∧
        (∀ c ∈ A, ∀ a b : X, (r.edge c.val).val = s(a.val, b.val) → R.IsBridge s(a, b)) ∧
        (∀ (f : HostEdge n), EdgeInside X f.val → χ f ∉ U →
          ∀ z w : X, f.val = s(z.val, w.val) →
          ¬ (R.deleteEdges (OriginalResidualColorDeletion χ r U X (A : Set C))).Reachable z w →
          ∃ hc : χ f ∈ eligibleInteriorColors χ U X, ⟨χ f, hc⟩ ∈ A) ∧
        ((commonEligibleInteriorColors χ U X).Nonempty → A.Nonempty) ∧
        (¬ (commonEligibleInteriorColors χ U X).Nonempty → A = ∅) := by
    by_cases hfull : (commonEligibleInteriorColors χ U X).Nonempty
    · obtain ⟨_hfamily, A, hseed, hne, hbridges, hcover⟩ :=
        exists_original_residual_eligible_bridge_closure_with_full_common_seed
          χ r U W hpartition x hcomponent s₀ hconn hfull
      refine ⟨A, hseed, ?_, ?_, fun _ => hne, ?_⟩
      · intro c hc a b hslot
        have hs : (s₀.edge c).val = s(a.val, b.val) := by
          rw [hslots c]
          exact hslot
        have hb := hbridges c hc a b hs
        change ((eligibleInteriorSelectedGraph χ U X s₀).induce X).IsBridge s(a, b) at hb
        rw [hgraph] at hb
        exact hb
      · intro f hf hcolor z w hfv hcross
        apply hcover f hf hcolor z w hfv
        change ¬ (((eligibleInteriorSelectedGraph χ U X s₀).induce X).deleteEdges _).Reachable z w
        rw [hgraph, hdelete A]
        exact hcross
      · intro hnone
        exact False.elim (hnone hfull)
    · refine ⟨∅, ?_, ?_, ?_, ?_, fun _ => rfl⟩
      · intro c hc
        exact False.elim (hfull ⟨c.val, hc⟩)
      · intro c hc
        exact False.elim (Finset.notMem_empty c hc)
      · intro f hf hcolor z w hfv hcross
        have hD : OriginalResidualColorDeletion χ r U X (↑(∅ : Finset C)) = ∅ := by
          ext e
          simp [OriginalResidualColorDeletion]
        have hcross' : ¬ R.Reachable z w := by
          simpa only [hD, deleteEdges_empty] using hcross
        exact False.elim (hcross' (hRconn z w))
      · intro hfull'
        exact False.elim (hfull hfull')
  refine ⟨hRconn, A, hseed, hbridges, hcover, ?_, hne, hempty, ?_⟩
  · intro e u y he hu hyW hy
    by_cases hcolor : χ e ∈ U
    · exact Or.inl hcolor
    · have hcFull := eligible_cross_edge_color_mem_commonEligibleInteriorColors
        χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
      have hcI : χ e ∈ eligibleInteriorColors χ U X := (Finset.mem_filter.mp hcFull).1
      exact Or.inr ⟨hcI, hseed ⟨χ e, hcI⟩ hcFull⟩
  · intro hout
    exact hne (commonEligibleInteriorColors_nonempty_of_eligibleOutgoing
      χ r U W hpartition x hcomponent hmax hout)

/-- Finite actual ORIGINAL bridge-owner set with exact edge/color count.
The exact retained-component count is a separate generic finite graph input;
it is not smuggled into this palette/bridge theorem. -/
theorem exists_original_residual_stage_bridge_edges
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ((selectedGraph χ r).induce (componentSupport χ r x)).Connected ∧
    ∃ (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
      (B : Finset (Sym2 (componentSupport χ r x))),
      B.card = A.card ∧
      (B : Set (Sym2 (componentSupport χ r x))) =
        OriginalResidualColorDeletion χ r U (componentSupport χ r x)
          (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))) ∧
      (B : Set (Sym2 (componentSupport χ r x))) ⊆
        ((selectedGraph χ r).induce (componentSupport χ r x)).edgeSet ∧
      (∀ b ∈ B, ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge b) ∧
      (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
        c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
      (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
        ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
        ¬ (((selectedGraph χ r).induce (componentSupport χ r x)).deleteEdges (B : Set _)).Reachable z w →
        ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
      (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
        χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
          ⟨χ e, hc⟩ ∈ A) ∧
      ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B.Nonempty) ∧
      (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B = ∅) ∧
      (EligibleResidualOutgoing χ U W (componentSupport χ r x) → B.Nonempty) := by
  classical
  let X := componentSupport χ r x
  let C := EligibleInteriorColor χ U X
  let R := (selectedGraph χ r).induce X
  obtain ⟨hRconn, A, hseed, hbridges, hcover, hout, hne, hempty, houtne⟩ :=
    exists_original_residual_stage_palette χ r U W hpartition x hcomponent hmax
  have howners : ∀ c : C, ∃ b : Sym2 X,
      Sym2.map (fun z : X => z.val) b = (r.edge c.val).val := by
    intro c
    have hi := selected_edge_inside_of_eligibleInterior_color
      χ r U W hpartition x hcomponent hmax c.val c.property
    obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective ((r.edge c.val).val)
    have ha : a ∈ X := hi a (by rw [← hab]; exact Sym2.mem_mk_left a b)
    have hb : b ∈ X := hi b (by rw [← hab]; exact Sym2.mem_mk_right a b)
    refine ⟨s((⟨a, ha⟩ : X), (⟨b, hb⟩ : X)), ?_⟩
    change s(a, b) = (r.edge c.val).val at hab
    simpa only [Sym2.map_mk] using hab
  choose owner howner using howners
  have hinj : Function.Injective owner := by
    intro c d hcd
    have hval : (r.edge c.val).val = (r.edge d.val).val := by
      rw [← howner c, ← howner d, hcd]
    have hedge : r.edge c.val = r.edge d.val := Subtype.ext hval
    exact Subtype.ext ((r.color_eq c.val).symm.trans
      ((congrArg χ hedge).trans (r.color_eq d.val)))
  let B : Finset (Sym2 X) := A.image owner
  have hBcard : B.card = A.card := Finset.card_image_of_injective A hinj
  have hBmem : ∀ e : Sym2 X, e ∈ B ↔
      ∃ c ∈ A, Sym2.map (fun z : X => z.val) e = (r.edge c.val).val := by
    intro e
    constructor
    · intro he
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp he
      exact ⟨c, hc, hce ▸ howner c⟩
    · rintro ⟨c, hc, hmap⟩
      have hce : owner c = e :=
        Sym2.map.injective (f := fun z : X => z.val) Subtype.val_injective
          ((howner c).trans hmap.symm)
      exact Finset.mem_image.mpr ⟨c, hc, hce⟩
  have hBcoe : (B : Set (Sym2 X)) = OriginalResidualColorDeletion χ r U X (A : Set C) := by
    ext e
    exact hBmem e
  have hBsubset : (B : Set (Sym2 X)) ⊆ R.edgeSet := by
    intro e he
    obtain ⟨a, b⟩ := e
    obtain ⟨c, _hc, hmap⟩ := (hBmem s(a, b)).mp he
    have hslot : (r.edge c.val).val = s(a.val, b.val) := by
      simpa only [Sym2.map_mk] using hmap.symm
    have hselected : s(a.val, b.val) ∈ (selectedGraph χ r).edgeSet := by
      rw [selectedGraph_edgeSet]
      exact ⟨c.val, hslot⟩
    exact hselected
  have hBbridges : ∀ e ∈ B, R.IsBridge e := by
    intro e he
    obtain ⟨a, b⟩ := e
    obtain ⟨c, hc, hmap⟩ := (hBmem s(a, b)).mp he
    have hslot : (r.edge c.val).val = s(a.val, b.val) := by
      simpa only [Sym2.map_mk] using hmap.symm
    exact hbridges c hc a b hslot
  have hBne : A.Nonempty → B.Nonempty := by
    rintro ⟨c, hc⟩
    exact ⟨owner c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  refine ⟨hRconn, A, B, hBcard, hBcoe, hBsubset, hBbridges, hseed, ?_, hout, ?_, ?_, ?_⟩
  · intro f hf hcolor z w hfv hcross
    apply hcover f hf hcolor z w hfv
    rw [← hBcoe]
    exact hcross
  · intro hfull
    exact hBne (hne hfull)
  · intro hnone
    change A.image owner = ∅
    rw [hempty hnone]
    exact Finset.image_empty owner
  · intro hout'
    exact hBne (houtne hout')

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- Actual original induced graph after literal original bridge-owner cuts. -/
def OriginalResidualRetainedGraph
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Set (Fin n)) (B : Finset (Sym2 X)) : SimpleGraph X :=
  ((selectedGraph χ r).induce X).deleteEdges (B : Set (Sym2 X))

/-- Literal host support of an ACTUAL component on the unchanged subtype X. -/
def originalResidualHostPiece
    {X : Set (Fin n)} {D : SimpleGraph X} (C : D.ConnectedComponent) : Set (Fin n) :=
  Subtype.val '' C.supp

/-- Derive actual support partition, connectivity, positive sizes and total size.
The generic vertex sum is reused from PathFiveComponentSums, not reproved. -/
theorem original_residual_actual_component_piece_facts
    (X : Set (Fin n)) (D : SimpleGraph X) :
    letI : DecidablePred (fun v : Fin n => v ∈ X) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ X) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = X ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) = Nat.card X ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) = Nat.card X := by
  classical
  let : DecidablePred (fun v : Fin n => v ∈ X) := Classical.decPred _
  let : DecidableRel D.Adj := Classical.decRel _
  have hpositive : ∀ C : D.ConnectedComponent, 0 < Nat.card C.supp := by
    intro C
    obtain ⟨w, hw⟩ := C.nonempty_supp
    let : Nonempty C.supp := ⟨⟨w, hw⟩⟩
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hsum : (∑ C : D.ConnectedComponent, Nat.card C.supp) = Nat.card X := by
    have h := ErdosProblems.AntiRamseyPathFiveComponents.vertex_card_eq_sum_component_card D
    simpa only [← Nat.card_eq_fintype_card] using h.symm
  have hhost : ∀ C : D.ConnectedComponent,
      Nat.card (originalResidualHostPiece C) = Nat.card C.supp := by
    intro C
    exact Nat.card_image_of_injective Subtype.val_injective C.supp
  refine ⟨?_, ?_, ?_, ?_, ?_, hpositive, hsum, hhost, ?_, ?_⟩
  · intro C v hv
    obtain ⟨w, _hw, rfl⟩ := hv
    exact w.property
  · intro C
    obtain ⟨w, hw⟩ := C.nonempty_supp
    exact ⟨w.val, w, hw, rfl⟩
  · intro C E hCE
    apply Set.disjoint_left.mpr
    intro v hvC hvE
    obtain ⟨c, hc, hcv⟩ := hvC
    obtain ⟨e, he, hev⟩ := hvE
    have hce : c = e := Subtype.ext (hcv.trans hev.symm)
    exact (Set.disjoint_left.mp (D.pairwise_disjoint_supp_connectedComponent hCE))
      hc (hce.symm ▸ he)
  · ext v
    constructor
    · intro hv
      obtain ⟨C, hvC⟩ := Set.mem_iUnion.mp hv
      obtain ⟨w, _hw, rfl⟩ := hvC
      exact w.property
    · intro hv
      let w : X := ⟨v, hv⟩
      apply Set.mem_iUnion.mpr
      refine ⟨D.connectedComponentMk w, w, ?_, rfl⟩
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  · intro C
    exact C.connected_toSimpleGraph
  · intro C
    rw [hhost C]
    exact hpositive C
  · calc
      (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
          ∑ C : D.ConnectedComponent, Nat.card C.supp := by
        apply Finset.sum_congr rfl
        intro C _
        exact hhost C
      _ = Nat.card X := hsum

/-- One actual stage returns its original palette/bridges and ACTUAL retained
pieces, with exact count, positive sizes and unchanged whole-component total. -/
theorem exists_original_residual_actual_retained_pieces
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ∃ (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
      (B : Finset (Sym2 (componentSupport χ r x))),
    let D := OriginalResidualRetainedGraph χ r (componentSupport χ r x) B
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ r x) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    B.card = A.card ∧
    (B : Set (Sym2 (componentSupport χ r x))) =
      OriginalResidualColorDeletion χ r U (componentSupport χ r x)
        (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))) ∧
    (B : Set (Sym2 (componentSupport χ r x))) ⊆
      ((selectedGraph χ r).induce (componentSupport χ r x)).edgeSet ∧
    (∀ b ∈ B, ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge b) ∧
    (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
      c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
    (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
      ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
      ¬ D.Reachable z w →
      ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
      χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
        ⟨χ e, hc⟩ ∈ A) ∧
    ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B.Nonempty) ∧
    (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B = ∅) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ r x) → B.Nonempty) ∧
    Nat.card D.ConnectedComponent = B.card + 1 ∧
    Nat.card D.ConnectedComponent = A.card + 1 ∧
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = componentSupport χ r x ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card (componentSupport χ r x) := by
  classical
  let X := componentSupport χ r x
  let R := (selectedGraph χ r).induce X
  obtain ⟨hR, A, B, hBA, hBset, hBedges, hBbridges, hseed, hcover, hout, hne, hempty, houtne⟩ :=
    exists_original_residual_stage_bridge_edges χ r U W hpartition x hcomponent hmax
  let D := OriginalResidualRetainedGraph χ r X B
  let : DecidablePred (fun v : Fin n => v ∈ X) := Classical.decPred _
  let : DecidableRel D.Adj := Classical.decRel _
  have hcountB : Nat.card D.ConnectedComponent = B.card + 1 :=
    connected_component_count_delete_original_bridges R hR B hBedges hBbridges
  have hcountA : Nat.card D.ConnectedComponent = A.card + 1 := by
    rw [hcountB, hBA]
  obtain ⟨hsubset, hnonempty, hdisjoint, hwhole, hconnected, hpositive, hsum,
      hhost, hhostpositive, hhostsum⟩ :=
    original_residual_actual_component_piece_facts X D
  exact ⟨A, B, hBA, hBset, hBedges, hBbridges, hseed, hcover, hout,
    hne, hempty, houtne, hcountB, hcountA, hsubset, hnonempty, hdisjoint,
    hwhole, hconnected, hpositive, hsum, hhost, hhostpositive, hhostsum⟩

theorem original_owner_of_selected_edge
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (e : HostEdge n) (he : e.val ∈ (selectedGraph χ r).edgeSet) :
    e = r.edge (χ e) := by
  rw [selectedGraph_edgeSet] at he
  obtain ⟨c, hc⟩ := he
  have howner : e = r.edge c := Subtype.ext hc.symm
  have hcolor : χ e = c := (congrArg χ howner).trans (r.color_eq c)
  rw [hcolor]
  exact howner

/-- Every literal original retained edge avoids U and ALL stage cut colors.
The exact B-to-original-slot equality is derived by the public stage caller. -/
theorem original_retained_edge_color_outside_removed_and_cut
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (X : Set (Fin n)) (hXW : X ⊆ W)
    (A : Finset (EligibleInteriorColor χ U X)) (B : Finset (Sym2 X))
    (hBset : (B : Set (Sym2 X)) = OriginalResidualColorDeletion χ r U X (A : Set _))
    (u v : X) (huv : (OriginalResidualRetainedGraph χ r X B).Adj u v)
    (e : HostEdge n) (hval : e.val = s(u.val, v.val)) :
    χ e ∉ U ∧ χ e ∉ A.image (fun c => c.val) := by
  classical
  have hdeleted := SimpleGraph.deleteEdges_adj.mp huv
  have he : e.val ∈ (selectedGraph χ r).edgeSet := by
    rw [hval]
    exact hdeleted.1
  have howner := original_owner_of_selected_edge χ r e he
  have hu : u.val ∈ (r.edge (χ e)).val := by
    rw [← howner, hval]
    exact Sym2.mem_mk_left _ _
  refine ⟨selected_slot_color_not_removed_of_endpoint_in_remaining
    χ r U W hpartition (χ e) u.val hu (hXW u.property), ?_⟩
  intro hcolor
  obtain ⟨c, hcA, hce⟩ := Finset.mem_image.mp hcolor
  have hmap : Sym2.map (fun z : X => z.val) s(u, v) = (r.edge c.val).val := by
    rw [Sym2.map_mk, ← hval, hce, ← howner]
  have hBmem : s(u, v) ∈ (B : Set (Sym2 X)) := by
    rw [hBset]
    exact ⟨c, hcA, hmap⟩
  exact hdeleted.2 hBmem

/-- Every selected original later edge wholly outside the WHOLE X avoids U
and ALL stage A colors. A owners remain wholly in X, not just in two paths. -/
theorem original_later_selected_edge_color_outside_removed_and_cut
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
    (e : HostEdge n) (he : e.val ∈ (selectedGraph χ r).edgeSet)
    (hlater : EdgeInside (W \ componentSupport χ r x) e.val) :
    χ e ∉ U ∧ χ e ∉ A.image (fun c => c.val) := by
  classical
  let X := componentSupport χ r x
  have howner := original_owner_of_selected_edge χ r e he
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.val
  have hu : u ∈ e.val := by
    rw [← huv]
    exact Sym2.mem_mk_left _ _
  have huW : u ∈ W := (hlater u hu).1
  have huNotX : u ∉ X := (hlater u hu).2
  have huOwner : u ∈ (r.edge (χ e)).val := by rw [← howner]; exact hu
  refine ⟨selected_slot_color_not_removed_of_endpoint_in_remaining
    χ r U W hpartition (χ e) u huOwner huW, ?_⟩
  intro hcolor
  obtain ⟨c, _hcA, hce⟩ := Finset.mem_image.mp hcolor
  have hinside := selected_edge_inside_of_eligibleInterior_color
    χ r U W hpartition x hcomponent hmax c.val c.property
  have huSlot : u ∈ (r.edge c.val).val := by
    rw [hce, ← howner]
    exact hu
  exact huNotX (hinside u huSlot)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Exactly the original colors whose selected owner is inside this WHOLE
actual component; this is not the unfiltered host interior palette. -/
def residualSelectedComponentColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (x : Fin n) : Set (Fin q) :=
  {c | EdgeInside (componentSupport χ r x) (r.edge c).val}

theorem reachable_stays_in_of_adj_closed
    (G : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hstep : ∀ a b, a ∈ X → G.Adj a b → b ∈ X)
    {a b : Fin n} (ha : a ∈ X) (hab : G.Reachable a b) : b ∈ X := by
  have hwalk : ∀ {u v : Fin n}, G.Walk u v → u ∈ X → v ∈ X := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | cons huv p ih =>
      intro hu
      exact ih (hstep _ _ hu huv)
  obtain ⟨p⟩ := hab
  exact hwalk p ha

theorem reachable_transfer_on_adj_closed
    (G H : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hclosed : ∀ a b, a ∈ X → G.Adj a b → b ∈ X)
    (hstep : ∀ a b, a ∈ X → G.Adj a b → H.Adj a b)
    {a b : Fin n} (ha : a ∈ X) (hab : G.Reachable a b) :
    H.Reachable a b := by
  have hwalk : ∀ {u v : Fin n}, G.Walk u v → u ∈ X → H.Reachable u v := by
    intro u v p
    induction p with
    | nil =>
      intro _hu
      exact SimpleGraph.Reachable.refl _
    | cons huv p ih =>
      intro hu
      exact (hstep _ _ hu huv).reachable.trans (ih (hclosed _ _ hu huv))
  obtain ⟨p⟩ := hab
  exact hwalk p ha

/-- Admissible original full choices inherit the exact original boundary. -/
theorem residualSlotPartition_of_admissibleChoice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (s : OriginalResidualChoice χ r U W) :
    ResidualSlotPartition χ s.choice U W := by
  refine ⟨?_, s.eligible_inside⟩
  intro c hc
  rw [s.prefix_eq c hc]
  exact hpartition.removed_outside c hc

/-- A whole actual component rooted in the remaining vertices stays there. -/
theorem componentSupport_subset_of_residualSlotPartition
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hx : x ∈ W) :
    componentSupport χ r x ⊆ W := by
  have hstep : ∀ a b, a ∈ W → (selectedGraph χ r).Adj a b → b ∈ W := by
    intro a b ha hab
    have hmem : s(a, b) ∈ (selectedGraph χ r).edgeSet := hab
    rw [selectedGraph_edgeSet χ r] at hmem
    obtain ⟨c, hc⟩ := hmem
    change (r.edge c).val = s(a, b) at hc
    have haOwner : a ∈ (r.edge c).val := by
      rw [hc]
      exact Sym2.mem_mk_left a b
    have hbOwner : b ∈ (r.edge c).val := by
      rw [hc]
      exact Sym2.mem_mk_right a b
    by_cases hremoved : c ∈ U
    · exact ((hpartition.removed_outside c hremoved a haOwner) ha).elim
    · exact hpartition.eligible_inside c hremoved b hbOwner
  intro v hv
  exact reachable_stays_in_of_adj_closed (selectedGraph χ r) W hstep hx
    ((mem_componentSupport χ r x v).mp hv)

/-- Two finite scalar maxima give the exact residual maximum, with an
ACTUAL admissible chosen full representative; no maximum is a premise. -/
theorem exists_residualLexMaximum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W) (hW : W.Nonempty) :
    ∃ (s : OriginalResidualChoice χ r U W) (x : Fin n),
      x ∈ W ∧ ResidualLexMaximum χ s.choice U W x ∧
      ResidualSlotPartition χ s.choice U W := by
  classical
  let : Fintype (HostEdge n) :=
    SimpleGraph.fintypeEdgeSet (⊤ : SimpleGraph (Fin n))
  have hchoiceInj : Function.Injective (fun a : RepresentativeChoice χ => a.edge) := by
    intro a b hab
    cases a with
    | mk ae ap =>
      cases b with
      | mk be bp =>
        cases hab
        rfl
  have : Finite (RepresentativeChoice χ) := Finite.of_injective _ hchoiceInj
  have hadmissibleInj :
      Function.Injective (fun s : OriginalResidualChoice χ r U W => s.choice) := by
    intro a b hab
    cases a with
    | mk ac ap ae =>
      cases b with
      | mk bc bp be =>
        cases hab
        rfl
  have : Finite (OriginalResidualChoice χ r U W) :=
    Finite.of_injective _ hadmissibleInj
  let : Fintype (OriginalResidualChoice χ r U W × Fin n) := Fintype.ofFinite _
  let S : Finset (OriginalResidualChoice χ r U W × Fin n) :=
    Finset.univ.filter (fun p => p.2 ∈ W)
  let s₀ : OriginalResidualChoice χ r U W :=
    { choice := r
      prefix_eq := fun _ _ => rfl
      eligible_inside := hpartition.eligible_inside }
  obtain ⟨x₀, hx₀⟩ := hW
  have hS : S.Nonempty :=
    ⟨(s₀, x₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩⟩
  obtain ⟨⟨sSize, xSize⟩, hsizeMem, hsizeMax⟩ :=
    Finset.exists_max_image S
      (fun p => (componentSupport χ p.1.choice p.2).ncard) hS
  let T : Finset (OriginalResidualChoice χ r U W × Fin n) :=
    S.filter (fun p => (componentSupport χ p.1.choice p.2).ncard =
      (componentSupport χ sSize.choice xSize).ncard)
  have hT : T.Nonempty :=
    ⟨(sSize, xSize), Finset.mem_filter.mpr ⟨hsizeMem, rfl⟩⟩
  obtain ⟨⟨s, x⟩, hsT, hedgeMax⟩ :=
    Finset.exists_max_image T
      (fun p => (internalSelectedEdges χ p.1.choice
        (componentSupport χ p.1.choice p.2)).card) hT
  have hsS : (s, x) ∈ S := (Finset.mem_filter.mp hsT).1
  have hx : x ∈ W := (Finset.mem_filter.mp hsS).2
  have hchosenSize : (componentSupport χ s.choice x).ncard =
      (componentSupport χ sSize.choice xSize).ncard := (Finset.mem_filter.mp hsT).2
  have hmax : ResidualLexMaximum χ s.choice U W x := by
    constructor
    · intro t z hz
      let tOld : OriginalResidualChoice χ r U W :=
        { choice := t.choice
          prefix_eq := fun c hc => (t.prefix_eq c hc).trans (s.prefix_eq c hc)
          eligible_inside := t.eligible_inside }
      have htS : (tOld, z) ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      change (componentSupport χ t.choice z).ncard ≤
        (componentSupport χ s.choice x).ncard
      rw [hchosenSize]
      exact hsizeMax (tOld, z) htS
    · intro t z hz hsize
      let tOld : OriginalResidualChoice χ r U W :=
        { choice := t.choice
          prefix_eq := fun c hc => (t.prefix_eq c hc).trans (s.prefix_eq c hc)
          eligible_inside := t.eligible_inside }
      have htT : (tOld, z) ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩,
          hsize.trans hchosenSize⟩
      exact hedgeMax (tOld, z) htT
  exact ⟨s, x, hx, hmax, residualSlotPartition_of_admissibleChoice
    χ r U W hpartition s⟩

theorem selected_owner_inside_component_of_endpoint
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (x : Fin n) (c : Fin q) (a : Fin n)
    (ha : a ∈ componentSupport χ r x) (haOwner : a ∈ (r.edge c).val) :
    EdgeInside (componentSupport χ r x) (r.edge c).val := by
  obtain ⟨⟨u, v⟩, hpair⟩ := Sym2.mk_surjective ((r.edge c).val)
  change s(u, v) = (r.edge c).val at hpair
  have hadj : (selectedGraph χ r).Adj u v := by
    have hmem : s(u, v) ∈ (selectedGraph χ r).edgeSet := by
      rw [selectedGraph_edgeSet χ r]
      exact ⟨c, hpair.symm⟩
    exact hmem
  have haPair : a = u ∨ a = v := Sym2.mem_iff.mp (by
    rw [hpair]
    exact haOwner)
  have hu : u ∈ componentSupport χ r x := by
    rcases haPair with hau | hav
    · exact hau ▸ ha
    · exact (mem_componentSupport χ r x u).mpr
        (((mem_componentSupport χ r x v).mp (hav ▸ ha)).trans hadj.symm.reachable)
  have hv : v ∈ componentSupport χ r x :=
    (mem_componentSupport χ r x v).mpr
      (((mem_componentSupport χ r x u).mp hu).trans hadj.reachable)
  intro w hw
  rw [← hpair] at hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact hu
  · exact hv

/-- Freezing WHOLE component owners preserves the next partition and its
literal graph for EVERY next admissible choice, including an empty palette. -/
theorem residual_component_freeze_invariants
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hx : x ∈ W) :
    let X := componentSupport χ r x
    let P := residualSelectedComponentColors χ r x
    X ⊆ W ∧ Disjoint P U ∧
    ResidualSlotPartition χ r (U ∪ P) (W \ X) ∧
    (W \ X).ncard < W.ncard ∧
    ∀ t : OriginalResidualChoice χ r (U ∪ P) (W \ X),
      (∃ old : OriginalResidualChoice χ r U W, old.choice = t.choice) ∧
      componentSupport χ t.choice x = X ∧
      (selectedGraph χ t.choice).induce X = (selectedGraph χ r).induce X ∧
      internalSelectedEdges χ t.choice X = internalSelectedEdges χ r X ∧
      ∀ c ∈ P, t.choice.edge c = r.edge c := by
  let X := componentSupport χ r x
  let P := residualSelectedComponentColors χ r x
  have hX : X ⊆ W :=
    componentSupport_subset_of_residualSlotPartition χ r U W hpartition x hx
  have hxX : x ∈ X := (mem_componentSupport χ r x x).mpr
    (SimpleGraph.Reachable.refl x)
  have hdisjoint : Disjoint P U := by
    apply Set.disjoint_left.mpr
    intro c hcP hcU
    obtain ⟨⟨a, b⟩, hpair⟩ := Sym2.mk_surjective ((r.edge c).val)
    have haOwner : a ∈ (r.edge c).val := by
      rw [← hpair]
      exact Sym2.mem_mk_left a b
    exact (hpartition.removed_outside c hcU a haOwner) (hX (hcP a haOwner))
  have hnext : ResidualSlotPartition χ r (U ∪ P) (W \ X) := by
    constructor
    · intro c hc v hv hvNext
      rcases hc with hcU | hcP
      · exact (hpartition.removed_outside c hcU v hv) hvNext.1
      · exact hvNext.2 (hcP v hv)
    · intro c hc v hv
      have hcU : c ∉ U := fun hcU => hc (Or.inl hcU)
      have hcP : c ∉ P := fun hcP => hc (Or.inr hcP)
      refine ⟨hpartition.eligible_inside c hcU v hv, ?_⟩
      intro hvX
      exact hcP (selected_owner_inside_component_of_endpoint χ r x c v hvX hv)
  have hdecrease : (W \ X).ncard < W.ncard := by
    have hsub : W \ X ⊆ W := fun _ hv => hv.1
    have hnot : x ∉ W \ X := fun hxNext => hxNext.2 hxX
    exact Set.ncard_lt_ncard (hsub.ssubset_of_mem_notMem hx hnot) (Set.toFinite W)
  refine ⟨hX, hdisjoint, hnext, hdecrease, ?_⟩
  intro t
  have hnested : ∃ old : OriginalResidualChoice χ r U W, old.choice = t.choice := by
    refine ⟨{ choice := t.choice
              prefix_eq := fun c hc => t.prefix_eq c (Or.inl hc)
              eligible_inside := ?_ }, rfl⟩
    intro c hc
    by_cases hcP : c ∈ P
    · rw [t.prefix_eq c (Or.inr hcP)]
      exact fun v hv => hX (hcP v hv)
    · have hcNext : c ∉ U ∪ P := by
        intro hcUnion
        rcases hcUnion with hcU | hcP'
        · exact hc hcU
        · exact hcP hcP'
      exact fun v hv => (t.eligible_inside c hcNext v hv).1
  have hslots : ∀ c ∈ P, t.choice.edge c = r.edge c :=
    fun c hc => t.prefix_eq c (Or.inr hc)
  have hlocal : ∀ a b, a ∈ X →
      ((selectedGraph χ t.choice).Adj a b ↔ (selectedGraph χ r).Adj a b) := by
    intro a b haX
    constructor
    · intro hab
      have hmem : s(a, b) ∈ (selectedGraph χ t.choice).edgeSet := hab
      rw [selectedGraph_edgeSet χ t.choice] at hmem
      obtain ⟨c, hc⟩ := hmem
      change (t.choice.edge c).val = s(a, b) at hc
      by_cases hfixed : c ∈ U ∪ P
      · have hval : (r.edge c).val = s(a, b) := by
          rw [← t.prefix_eq c hfixed]
          exact hc
        have hmemOld : s(a, b) ∈ (selectedGraph χ r).edgeSet := by
          rw [selectedGraph_edgeSet χ r]
          exact ⟨c, hval⟩
        exact hmemOld
      · have haOwner : a ∈ (t.choice.edge c).val := by
          rw [hc]
          exact Sym2.mem_mk_left a b
        exact ((t.eligible_inside c hfixed a haOwner).2 haX).elim
    · intro hab
      have hmem : s(a, b) ∈ (selectedGraph χ r).edgeSet := hab
      rw [selectedGraph_edgeSet χ r] at hmem
      obtain ⟨c, hc⟩ := hmem
      change (r.edge c).val = s(a, b) at hc
      have haOwner : a ∈ (r.edge c).val := by
        rw [hc]
        exact Sym2.mem_mk_left a b
      have hcP : c ∈ P :=
        selected_owner_inside_component_of_endpoint χ r x c a haX haOwner
      have hmemNew : s(a, b) ∈ (selectedGraph χ t.choice).edgeSet := by
        rw [selectedGraph_edgeSet χ t.choice]
        refine ⟨c, ?_⟩
        change (t.choice.edge c).val = s(a, b)
        rw [hslots c hcP]
        exact hc
      exact hmemNew
  have hclosedOld : ∀ a b, a ∈ X → (selectedGraph χ r).Adj a b → b ∈ X := by
    intro a b ha hab
    exact (mem_componentSupport χ r x b).mpr
      (((mem_componentSupport χ r x a).mp ha).trans hab.reachable)
  have hclosedNew : ∀ a b, a ∈ X →
      (selectedGraph χ t.choice).Adj a b → b ∈ X :=
    fun a b ha hab => hclosedOld a b ha ((hlocal a b ha).mp hab)
  have hsupport : componentSupport χ t.choice x = X := by
    ext v
    constructor
    · intro hv
      exact reachable_stays_in_of_adj_closed (selectedGraph χ t.choice) X
        hclosedNew hxX ((mem_componentSupport χ t.choice x v).mp hv)
    · intro hv
      apply (mem_componentSupport χ t.choice x v).mpr
      exact reachable_transfer_on_adj_closed (selectedGraph χ r)
        (selectedGraph χ t.choice) X hclosedOld
        (fun a b ha hab => (hlocal a b ha).mpr hab) hxX
        ((mem_componentSupport χ r x v).mp hv)
  have hgraph : (selectedGraph χ t.choice).induce X =
      (selectedGraph χ r).induce X := by
    ext a b
    exact hlocal a.val b.val a.property
  have hinternal : internalSelectedEdges χ t.choice X = internalSelectedEdges χ r X := by
    classical
    ext f
    obtain ⟨a, b⟩ := f
    rw [mem_internalSelectedEdges χ t.choice X s(a, b),
      mem_internalSelectedEdges χ r X s(a, b)]
    constructor
    · rintro ⟨hab, hinside⟩
      exact ⟨(hlocal a b (hinside a (Sym2.mem_mk_left a b))).mp hab, hinside⟩
    · rintro ⟨hab, hinside⟩
      exact ⟨(hlocal a b (hinside a (Sym2.mem_mk_left a b))).mpr hab, hinside⟩
  exact ⟨hnested, hsupport, hgraph, hinternal, hslots⟩

/-- ONE complete greedy stage for the original full-color residual family.
Every next admissible choice nests into the ORIGINAL input stage, while the
chosen whole component's literal graph/support/slots remain fixed. -/
theorem exists_residual_greedy_stage
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W) (hW : W.Nonempty) :
    ∃ (s : OriginalResidualChoice χ r U W) (x : Fin n),
      x ∈ W ∧ ResidualLexMaximum χ s.choice U W x ∧
      ResidualSlotPartition χ s.choice U W ∧
      let X := componentSupport χ s.choice x
      let P := residualSelectedComponentColors χ s.choice x
      X ⊆ W ∧ Disjoint P U ∧
      ResidualSlotPartition χ s.choice (U ∪ P) (W \ X) ∧
      (W \ X).ncard < W.ncard ∧
      ∀ t : OriginalResidualChoice χ s.choice (U ∪ P) (W \ X),
        (∃ old : OriginalResidualChoice χ r U W, old.choice = t.choice) ∧
        componentSupport χ t.choice x = X ∧
        (selectedGraph χ t.choice).induce X = (selectedGraph χ s.choice).induce X ∧
        internalSelectedEdges χ t.choice X = internalSelectedEdges χ s.choice X ∧
        ∀ c ∈ P, t.choice.edge c = s.choice.edge c := by
  obtain ⟨s, x, hx, hmax, hpartitionS⟩ :=
    exists_residualLexMaximum χ r U W hpartition hW
  obtain ⟨hX, hdisjoint, hnext, hdecrease, hforall⟩ :=
    residual_component_freeze_invariants χ s.choice U W hpartitionS x hx
  refine ⟨s, x, hx, hmax, hpartitionS, hX, hdisjoint, hnext, hdecrease, ?_⟩
  intro t
  obtain ⟨⟨old, hold⟩, hsupport, hgraph, hinternal, hslots⟩ := hforall t
  let originalOld : OriginalResidualChoice χ r U W :=
    { choice := old.choice
      prefix_eq := fun c hc => (old.prefix_eq c hc).trans (s.prefix_eq c hc)
      eligible_inside := old.eligible_inside }
  exact ⟨⟨originalOld, hold⟩, hsupport, hgraph, hinternal, hslots⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Every stage is anchored at the SAME full representative R.
The list ends exactly when the actual residual vertex set is empty. -/
def ResidualGreedySequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) :
    Set (Fin q) → Set (Fin n) → List (Fin n) → Prop
  | U, W, [] => W = ∅ ∧ ResidualSlotPartition χ R U W
  | U, W, x :: xs =>
      x ∈ W ∧ ResidualSlotPartition χ R U W ∧
      ResidualLexMaximum χ R U W x ∧
      ResidualGreedySequence χ R
        (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) xs

/-- Prefix equality transports the EXACT residual-family anchor.
The chosen component and its exact internal selected-edge Finset are frozen. -/
theorem residualLexMaximum_of_same_component_and_prefix
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r R : RepresentativeChoice χ) (U : Set (Fin q)) (W : Set (Fin n))
    (x : Fin n) (hprefix : ∀ c ∈ U, R.edge c = r.edge c)
    (hmax : ResidualLexMaximum χ r U W x)
    (hsupport : componentSupport χ R x = componentSupport χ r x)
    (hinternal : internalSelectedEdges χ R (componentSupport χ r x) =
      internalSelectedEdges χ r (componentSupport χ r x)) :
    ResidualLexMaximum χ R U W x := by
  constructor
  · intro t z hz
    let old : OriginalResidualChoice χ r U W :=
      { choice := t.choice
        prefix_eq := fun c hc => (t.prefix_eq c hc).trans (hprefix c hc)
        eligible_inside := t.eligible_inside }
    rw [hsupport]
    exact hmax.1 old z hz
  · intro t z hz hsize
    let old : OriginalResidualChoice χ r U W :=
      { choice := t.choice
        prefix_eq := fun c hc => (t.prefix_eq c hc).trans (hprefix c hc)
        eligible_inside := t.eligible_inside }
    have hsizeOld : (componentSupport χ old.choice z).ncard =
        (componentSupport χ r x).ncard := by
      rw [← hsupport]
      exact hsize
    rw [hsupport, hinternal]
    exact hmax.2 old z hz hsizeOld

/-- Next-stage literal slot admissibility plus whole-support equality also
freezes the exact selected-color set, including when that set is empty. -/
theorem residualSelectedComponentColors_eq_of_frozen_next
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n)
    (t : OriginalResidualChoice χ r
      (U ∪ residualSelectedComponentColors χ r x)
      (W \ componentSupport χ r x))
    (hsupport : componentSupport χ t.choice x = componentSupport χ r x) :
    residualSelectedComponentColors χ t.choice x =
      residualSelectedComponentColors χ r x := by
  ext c
  change EdgeInside (componentSupport χ t.choice x) (t.choice.edge c).val ↔
    EdgeInside (componentSupport χ r x) (r.edge c).val
  rw [hsupport]
  constructor
  · intro hc
    by_cases hfixed : c ∈ U ∪ residualSelectedComponentColors χ r x
    · rw [t.prefix_eq c hfixed] at hc
      exact hc
    · obtain ⟨⟨a, b⟩, hpair⟩ := Sym2.mk_surjective ((t.choice.edge c).val)
      have haOwner : a ∈ (t.choice.edge c).val := by
        rw [← hpair]
        exact Sym2.mem_mk_left a b
      exact ((t.eligible_inside c hfixed a haOwner).2 (hc a haOwner)).elim
  · intro hc
    have hcP : c ∈ residualSelectedComponentColors χ r x := hc
    rw [t.prefix_eq c (Or.inr hcP)]
    exact hc

/-- At EVERY certified stage, freezing its WHOLE component preserves the
literal support, induced graph, internal edge Finset and selected color owners
for ALL next admissible full choices. -/
theorem residualGreedySequence_head_freeze
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) (xs : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W (x :: xs)) :
    let X := componentSupport χ R x
    let P := residualSelectedComponentColors χ R x
    X ⊆ W ∧ Disjoint P U ∧
    ResidualSlotPartition χ R (U ∪ P) (W \ X) ∧
    (W \ X).ncard < W.ncard ∧
    ∀ t : OriginalResidualChoice χ R (U ∪ P) (W \ X),
      (∃ old : OriginalResidualChoice χ R U W, old.choice = t.choice) ∧
      componentSupport χ t.choice x = X ∧
      (selectedGraph χ t.choice).induce X = (selectedGraph χ R).induce X ∧
      internalSelectedEdges χ t.choice X = internalSelectedEdges χ R X ∧
      ∀ c ∈ P, t.choice.edge c = R.edge c := by
  exact residual_component_freeze_invariants χ R U W
    hsequence.2.1 x hsequence.1

/-- The actual whole components of the finite certificate cover EXACTLY
its starting residual vertices; isolated vertices are included. -/
theorem residualGreedySequence_covers
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W roots) :
    ∀ v, v ∈ W ↔ ∃ x ∈ roots, v ∈ componentSupport χ R x := by
  induction roots generalizing U W with
  | nil =>
    intro v
    rw [hsequence.1]
    simp
  | cons x xs ih =>
    have hx : x ∈ W := hsequence.1
    have hpartition : ResidualSlotPartition χ R U W := hsequence.2.1
    have htail := hsequence.2.2.2
    have hX : componentSupport χ R x ⊆ W :=
      componentSupport_subset_of_residualSlotPartition χ R U W hpartition x hx
    have hcoverTail := ih (U ∪ residualSelectedComponentColors χ R x)
      (W \ componentSupport χ R x) htail
    intro v
    constructor
    · intro hv
      by_cases hvX : v ∈ componentSupport χ R x
      · exact ⟨x, List.mem_cons_self, hvX⟩
      · obtain ⟨y, hy, hvY⟩ := (hcoverTail v).mp ⟨hv, hvX⟩
        exact ⟨y, List.mem_cons_of_mem x hy, hvY⟩
    · rintro ⟨y, hy, hvY⟩
      rcases List.mem_cons.mp hy with hyHead | hyTail
      · subst y
        exact hX hvY
      · exact ((hcoverTail v).mpr ⟨y, hyTail, hvY⟩).1

/-- Every certified component is disjoint from all later WHOLE components. -/
theorem residualGreedySequence_pairwise_disjoint
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W roots) :
    roots.Pairwise (fun x y =>
      Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  induction roots generalizing U W with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have htail := hsequence.2.2.2
    have hcoverTail := residualGreedySequence_covers χ R
      (U ∪ residualSelectedComponentColors χ R x)
      (W \ componentSupport χ R x) xs htail
    apply List.pairwise_cons.mpr
    constructor
    · intro y hy
      apply Set.disjoint_left.mpr
      intro v hvX hvY
      exact ((hcoverTail v).mpr ⟨y, hy, hvY⟩).2 hvX
    · exact ih (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) htail

/-- Actual strict remaining-vertex descent constructs a FINAL full choice
and a finite sequence. EVERY stage maximum and boundary is expressed using
that SAME final choice, with all initial U slots fixed to original r. -/
theorem exists_residual_greedy_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W) :
    ∃ (s : OriginalResidualChoice χ r U W) (roots : List (Fin n)),
      ResidualGreedySequence χ s.choice U W roots ∧
      (∀ v, v ∈ W ↔ ∃ x ∈ roots, v ∈ componentSupport χ s.choice x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ s.choice x) (componentSupport χ s.choice y)) := by
  classical
  have hrec : ∀ N : ℕ, ∀ (r : RepresentativeChoice χ)
      (U : Set (Fin q)) (W : Set (Fin n)), W.ncard = N →
      ResidualSlotPartition χ r U W →
      ∃ (s : OriginalResidualChoice χ r U W) (roots : List (Fin n)),
        ResidualGreedySequence χ s.choice U W roots := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro r U W hcard hpartition
      by_cases hW : W.Nonempty
      · obtain ⟨s, x, hx, hmax, _hpartitionS, _hX, _hdisjoint,
          hnext, hdecrease, hforall⟩ :=
          exists_residual_greedy_stage χ r U W hpartition hW
        have hsmaller : (W \ componentSupport χ s.choice x).ncard < N := by
          rw [← hcard]
          exact hdecrease
        obtain ⟨t, xs, htailOld⟩ :=
          ih (W \ componentSupport χ s.choice x).ncard hsmaller s.choice
            (U ∪ residualSelectedComponentColors χ s.choice x)
            (W \ componentSupport χ s.choice x) rfl hnext
        obtain ⟨⟨original, horiginal⟩, hsupport, _hgraph, hinternal, _hslots⟩ :=
          hforall t
        have hcolors :=
          residualSelectedComponentColors_eq_of_frozen_next χ s.choice U W x t hsupport
        have hpartitionFinal : ResidualSlotPartition χ t.choice U W := by
          have h := residualSlotPartition_of_admissibleChoice χ r U W hpartition original
          rw [horiginal] at h
          exact h
        have hmaxFinal : ResidualLexMaximum χ t.choice U W x :=
          residualLexMaximum_of_same_component_and_prefix χ s.choice t.choice U W x
            (fun c hc => t.prefix_eq c (Or.inl hc)) hmax hsupport hinternal
        have htail : ResidualGreedySequence χ t.choice
            (U ∪ residualSelectedComponentColors χ t.choice x)
            (W \ componentSupport χ t.choice x) xs := by
          rw [hcolors, hsupport]
          exact htailOld
        refine ⟨original, x :: xs, ?_⟩
        rw [horiginal]
        exact ⟨hx, hpartitionFinal, hmaxFinal, htail⟩
      · have hWempty : W = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr (fun v hv => hW ⟨v, hv⟩)
        let original : OriginalResidualChoice χ r U W :=
          { choice := r
            prefix_eq := fun _ _ => rfl
            eligible_inside := hpartition.eligible_inside }
        exact ⟨original, [], hWempty, hpartition⟩
  obtain ⟨s, roots, hsequence⟩ := hrec W.ncard r U W rfl hpartition
  exact ⟨s, roots, hsequence,
    residualGreedySequence_covers χ s.choice U W roots hsequence,
    residualGreedySequence_pairwise_disjoint χ s.choice U W roots hsequence⟩

/-- From ANY valid original full representative, derive one final full R
whose whole components cover ALL vertices and whose EVERY residual-prefix
stage is maximal in size, then internal edges. No positive n or nonempty
palette is imposed, and singleton empty-palette stages are retained. -/
theorem exists_full_original_residual_greedy_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n)),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  have hpartition : ResidualSlotPartition χ r ∅ Set.univ := by
    constructor
    · intro c hc
      exact hc.elim
    · intro _c _hc _v _hv
      trivial
  obtain ⟨s, roots, hsequence, hcover, hdisjoint⟩ :=
    exists_residual_greedy_sequence χ r ∅ Set.univ hpartition
  exact ⟨s.choice, roots, hsequence, fun v => (hcover v).mp (Set.mem_univ v),
    hdisjoint⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- The entire exact existential conclusion of the existing one-stage API.
The actual original A/B owners, cut cover, outgoing boundary, zero-cut branch,
counts, component supports and all intrinsic/host size facts are retained. -/
def OriginalResidualStagePieceCertificate
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) : Prop :=
    ∃ (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
      (B : Finset (Sym2 (componentSupport χ r x))),
    let D := OriginalResidualRetainedGraph χ r (componentSupport χ r x) B
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ r x) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    B.card = A.card ∧
    (B : Set (Sym2 (componentSupport χ r x))) =
      OriginalResidualColorDeletion χ r U (componentSupport χ r x)
        (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))) ∧
    (B : Set (Sym2 (componentSupport χ r x))) ⊆
      ((selectedGraph χ r).induce (componentSupport χ r x)).edgeSet ∧
    (∀ b ∈ B, ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge b) ∧
    (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
      c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
    (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
      ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
      ¬ D.Reachable z w →
      ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
      χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
        ⟨χ e, hc⟩ ∈ A) ∧
    ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B.Nonempty) ∧
    (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B = ∅) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ r x) → B.Nonempty) ∧
    Nat.card D.ConnectedComponent = B.card + 1 ∧
    Nat.card D.ConnectedComponent = A.card + 1 ∧
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = componentSupport χ r x ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card (componentSupport χ r x)

/-- All original head premises and the actual existential stage certificate
at EVERY cons of ONE full R. Freeze the WHOLE component palette/support,
rather than merely its cut palette. Nil retains the original terminal facts. -/
def OriginalResidualPieceSequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) :
    Set (Fin q) → Set (Fin n) → List (Fin n) → Prop
  | U, W, [] => W = ∅ ∧ ResidualSlotPartition χ R U W
  | U, W, x :: xs =>
      x ∈ W ∧ ResidualSlotPartition χ R U W ∧
      ResidualLexMaximum χ R U W x ∧
      OriginalResidualStagePieceCertificate χ R U W x ∧
      OriginalResidualPieceSequence χ R
        (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) xs

/-- Every certified SAME-R greedy sequence admits
the full existing original retained-piece certificate at every stage. -/
theorem residualGreedySequence_original_piece_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R U W roots) :
    OriginalResidualPieceSequence χ R U W roots := by
  induction roots generalizing U W with
  | nil => exact hsequence
  | cons x xs ih =>
    rcases hsequence with ⟨hx, hpartition, hmax, htail⟩
    have hcomponent : componentSupport χ R x ⊆ W :=
      componentSupport_subset_of_residualSlotPartition χ R U W hpartition x hx
    have hstage : OriginalResidualStagePieceCertificate χ R U W x :=
      exists_original_residual_actual_retained_pieces
        χ R U W hpartition x hcomponent hmax
    exact ⟨hx, hpartition, hmax, hstage,
      ih (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) htail⟩

/-- From any valid original full representative,
derive a SAME-final-full-R enriched sequence. The existing actual whole
component coverage and disjointness conclusions are unchanged. -/
theorem exists_full_original_residual_piece_sequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n)),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  obtain ⟨R, roots, hsequence, hcover, hdisjoint⟩ :=
    exists_full_original_residual_greedy_sequence χ r
  exact ⟨R, roots, hsequence,
    residualGreedySequence_original_piece_sequence χ R ∅ Set.univ roots hsequence,
    hcover, hdisjoint⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- Both
no-duplication and completeness are derived from the greedy certificate. -/
theorem residualGreedySequence_component_inventory
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R ∅ Set.univ roots) :
    (roots.map (fun x => (selectedGraph χ R).connectedComponentMk x)).Nodup ∧
    (∀ C : (selectedGraph χ R).ConnectedComponent,
      C ∈ roots.map (fun x => (selectedGraph χ R).connectedComponentMk x)) := by
  have hpair := residualGreedySequence_pairwise_disjoint
    χ R ∅ Set.univ roots hsequence
  have hcover := residualGreedySequence_covers χ R ∅ Set.univ roots hsequence
  constructor
  · change (roots.map (fun x => (selectedGraph χ R).connectedComponentMk x)).Pairwise
      (fun C D => C ≠ D)
    apply List.pairwise_map.mpr
    apply hpair.imp
    intro x y hdisjoint hxy
    have hx : x ∈ componentSupport χ R x := by
      change (selectedGraph χ R).connectedComponentMk x =
        (selectedGraph χ R).connectedComponentMk x
      rfl
    have hy : x ∈ componentSupport χ R y := by
      change (selectedGraph χ R).connectedComponentMk x =
        (selectedGraph χ R).connectedComponentMk y
      exact hxy
    exact (Set.disjoint_left.mp hdisjoint) hx hy
  · intro C
    obtain ⟨v, hv⟩ := C.nonempty_supp
    obtain ⟨x, hx, hvx⟩ := (hcover v).mp (Set.mem_univ v)
    have hvC : (selectedGraph χ R).connectedComponentMk v = C := hv
    have hvX : (selectedGraph χ R).connectedComponentMk v =
        (selectedGraph χ R).connectedComponentMk x := hvx
    exact List.mem_map.mpr ⟨x, hx, hvX.symm.trans hvC⟩

/-- This includes n=0, where both quantities are zero. -/
theorem residualGreedySequence_root_count
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R ∅ Set.univ roots) :
    roots.length = Nat.card (selectedGraph χ R).ConnectedComponent := by
  classical
  let G := selectedGraph χ R
  let L := roots.map (fun x => G.connectedComponentMk x)
  obtain ⟨hnodup, hcomplete⟩ :=
    residualGreedySequence_component_inventory χ R roots hsequence
  have huniv : L.toFinset = (Finset.univ : Finset G.ConnectedComponent) := by
    ext C
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcomplete C
  calc
    roots.length = L.length := by simp only [L, List.length_map]
    _ = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = Fintype.card G.ConnectedComponent := by rw [huniv, Finset.card_univ]
    _ = Nat.card G.ConnectedComponent := Nat.card_eq_fintype_card.symm

/-- Sum the sizes of the ACTUAL whole selected components
at the derived roots. Isolates contribute one; the empty carrier contributes
the empty sum. The generic component vertex theorem is reused unchanged. -/
theorem residualGreedySequence_whole_component_size_sum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R ∅ Set.univ roots) :
    (roots.map (fun x => Nat.card (componentSupport χ R x))).sum = n := by
  classical
  let G := selectedGraph χ R
  let L := roots.map (fun x => G.connectedComponentMk x)
  obtain ⟨hnodup, hcomplete⟩ :=
    residualGreedySequence_component_inventory χ R roots hsequence
  have huniv : L.toFinset = (Finset.univ : Finset G.ConnectedComponent) := by
    ext C
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcomplete C
  have hlist : (L.map (fun C : G.ConnectedComponent => Nat.card C.supp)).sum =
      ∑ C : G.ConnectedComponent, Nat.card C.supp := by
    rw [← List.sum_toFinset (fun C : G.ConnectedComponent => Nat.card C.supp) hnodup]
    rw [huniv]
  have hvertex : (∑ C : G.ConnectedComponent, Nat.card C.supp) = n := by
    have h :=
      ErdosProblems.AntiRamseyPathFiveComponents.vertex_card_eq_sum_component_card G
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h.symm
  have htotal := hlist.trans hvertex
  simpa only [L, G, List.map_map, Function.comp_def, componentSupport] using htotal

/-- Public original existence starts only from chi and a
valid full original r. Derive one final full R, enriched actual stage sequence,
actual original component count and whole-component vertex ledger, keeping
the original coverage/disjointness statements unchanged. -/
theorem exists_full_original_component_ledger
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n)),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      roots.length = Nat.card (selectedGraph χ R).ConnectedComponent ∧
      (roots.map (fun x => Nat.card (componentSupport χ R x))).sum = n ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  obtain ⟨R, roots, hsequence, hpieces, hcover, hdisjoint⟩ :=
    exists_full_original_residual_piece_sequence χ r
  exact ⟨R, roots, hsequence, hpieces,
    residualGreedySequence_root_count χ R roots hsequence,
    residualGreedySequence_whole_component_size_sum χ R roots hsequence,
    hcover, hdisjoint⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- The complete existing one-stage payload, with its ACTUAL A/B exposed.
This is the body of OriginalResidualStagePieceCertificate after its two
existential binders, with every original field and both letI bindings retained. -/
def OriginalResidualCutStagePayload
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n)
    (A : Finset (EligibleInteriorColor χ U (componentSupport χ R x)))
    (B : Finset (Sym2 (componentSupport χ R x))) : Prop :=
    let D := OriginalResidualRetainedGraph χ R (componentSupport χ R x) B
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    B.card = A.card ∧
    (B : Set (Sym2 (componentSupport χ R x))) =
      OriginalResidualColorDeletion χ R U (componentSupport χ R x)
        (A : Set (EligibleInteriorColor χ U (componentSupport χ R x))) ∧
    (B : Set (Sym2 (componentSupport χ R x))) ⊆
      ((selectedGraph χ R).induce (componentSupport χ R x)).edgeSet ∧
    (∀ b ∈ B, ((selectedGraph χ R).induce (componentSupport χ R x)).IsBridge b) ∧
    (∀ c : EligibleInteriorColor χ U (componentSupport χ R x),
      c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ R x) → c ∈ A) ∧
    (∀ (f : HostEdge n), EdgeInside (componentSupport χ R x) f.val → χ f ∉ U →
      ∀ z w : componentSupport χ R x, f.val = s(z.val, w.val) →
      ¬ D.Reachable z w →
      ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ R x), ⟨χ f, hc⟩ ∈ A) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ R x → y ∈ W → y ∉ componentSupport χ R x →
      χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ R x),
        ⟨χ e, hc⟩ ∈ A) ∧
    ((commonEligibleInteriorColors χ U (componentSupport χ R x)).Nonempty → B.Nonempty) ∧
    (¬ (commonEligibleInteriorColors χ U (componentSupport χ R x)).Nonempty → B = ∅) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ R x) → B.Nonempty) ∧
    Nat.card D.ConnectedComponent = B.card + 1 ∧
    Nat.card D.ConnectedComponent = A.card + 1 ∧
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ componentSupport χ R x) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = componentSupport χ R x ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ R x) ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card (componentSupport χ R x)

/-- The exposed cut sets carry the whole existing certificate for THESE choices. -/
structure OriginalResidualCutStage
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) where
  root_mem : x ∈ W
  partition : ResidualSlotPartition χ R U W
  maximum : ResidualLexMaximum χ R U W x
  A : Finset (EligibleInteriorColor χ U (componentSupport χ R x))
  B : Finset (Sym2 (componentSupport χ R x))
  payload : OriginalResidualCutStagePayload χ R U W x A B

def OriginalResidualCutStage.root
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (_S : OriginalResidualCutStage χ R U W x) : Fin n := x

def OriginalResidualCutStage.rootSupport
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (_S : OriginalResidualCutStage χ R U W x) : Set (Fin n) := componentSupport χ R x

def OriginalResidualCutStage.retainedGraph
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) : SimpleGraph (componentSupport χ R x) :=
  OriginalResidualRetainedGraph χ R (componentSupport χ R x) S.B

/-- The next stage is indexed by the WHOLE frozen palette and support.
The exposed constructor permits a later literal lifted-cut recursion. -/
inductive OriginalResidualCutFamily
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) :
    Set (Fin q) → Set (Fin n) → List (Fin n) → Type
  | nil {U W} (empty : W = ∅) (partition : ResidualSlotPartition χ R U W) :
      OriginalResidualCutFamily χ R U W []
  | cons {U W x xs} (stage : OriginalResidualCutStage χ R U W x)
      (tail : OriginalResidualCutFamily χ R
        (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) xs) :
      OriginalResidualCutFamily χ R U W (x :: xs)

/-- Choose A/B recursively from the derived EXISTENTIAL
stage certificates. Classical.choose performs the Prop-to-data extraction;
no desired witnesses, counts or family are supplied. -/
noncomputable def originalCutFamilyOfPieceSequence
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (roots : List (Fin n))
    (hsequence : OriginalResidualPieceSequence χ R U W roots) :
    OriginalResidualCutFamily χ R U W roots := by
  classical
  induction roots generalizing U W with
  | nil => exact .nil hsequence.1 hsequence.2
  | cons x xs ih =>
    let hstage := hsequence.2.2.2.1
    let A := Classical.choose hstage
    let B := Classical.choose (Classical.choose_spec hstage)
    let stage : OriginalResidualCutStage χ R U W x :=
      { root_mem := hsequence.1
        partition := hsequence.2.1
        maximum := hsequence.2.2.1
        A := A
        B := B
        payload := Classical.choose_spec (Classical.choose_spec hstage) }
    exact .cons stage
      (ih (U ∪ residualSelectedComponentColors χ R x)
        (W \ componentSupport χ R x) hsequence.2.2.2.2)

/-- Recover the FULL original all-stage certificate
for this exact data family; no stage's original payload is lost. -/
theorem originalCutFamily_piece_sequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalResidualPieceSequence χ R U W roots := by
  induction F with
  | nil empty partition => exact ⟨empty, partition⟩
  | cons stage tail ih =>
    exact ⟨stage.root_mem, stage.partition, stage.maximum,
      ⟨stage.A, stage.B, stage.payload⟩, ih⟩

/-- Public method spelling for recovery of the complete original piece sequence. -/
theorem OriginalResidualCutFamily.toPieceSequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalResidualPieceSequence χ R U W roots :=
  originalCutFamily_piece_sequence F

/-- Recover the actual greedy sequence directly from
the data chain's original head premises and exact whole-prefix tail. -/
theorem OriginalResidualCutFamily.toGreedySequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ResidualGreedySequence χ R U W roots := by
  induction F with
  | nil empty partition => exact ⟨empty, partition⟩
  | cons stage tail ih =>
    exact ⟨stage.root_mem, stage.partition, stage.maximum, ih⟩

/-- The ACTUAL retained-component index family, with no manufactured pieces.
At nil it is empty; at cons it contains every actual deleted-graph component. -/
def OriginalCutFamilyPieceIndex
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Type :=
  match F with
  | .nil _ _ => PEmpty
  | .cons stage tail => stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail

noncomputable instance originalCutFamilyPieceIndexFintype
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Fintype (OriginalCutFamilyPieceIndex F) := by
  classical
  induction F with
  | nil =>
    change Fintype PEmpty
    exact inferInstance
  | cons stage tail ih =>
    letI : Fintype (OriginalCutFamilyPieceIndex tail) := ih
    change Fintype (stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail)
    exact inferInstance

/-- Literal ACTUAL per-stage B.card sum; the genuine-prefix tail remains
exposed in F.cons for the later original host lifted-edge union. -/
def originalCutFamilyCutTotal
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : ℕ :=
  match F with
  | .nil _ _ => 0
  | .cons stage tail => stage.B.card + originalCutFamilyCutTotal tail

def originalCutFamilyPieceSupport
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalCutFamilyPieceIndex F → Set (Fin n) :=
  match F with
  | .nil _ _ => fun i => PEmpty.elim i
  | .cons _stage tail => Sum.elim (fun C => originalResidualHostPiece C)
      (originalCutFamilyPieceSupport tail)

noncomputable def originalCutFamilyPieceSize
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    OriginalCutFamilyPieceIndex F → ℕ :=
  match F with
  | .nil _ _ => fun i => PEmpty.elim i
  | .cons _stage tail => Sum.elim (fun C => Nat.card C.supp) (originalCutFamilyPieceSize tail)

noncomputable def originalCutFamilyTotalPieceSize
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : ℕ :=
  ∑ i : OriginalCutFamilyPieceIndex F, originalCutFamilyPieceSize F i

/-- Concise public data methods for the later literal lifted-cut recursion. -/
abbrev OriginalResidualCutFamily.PieceIndex
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Type := OriginalCutFamilyPieceIndex F

abbrev OriginalResidualCutFamily.cutCount
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : ℕ := originalCutFamilyCutTotal F

noncomputable abbrev OriginalResidualCutFamily.pieceSize
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : F.PieceIndex → ℕ :=
  originalCutFamilyPieceSize F

abbrev OriginalResidualCutFamily.pieceSupport
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : F.PieceIndex → Set (Fin n) :=
  originalCutFamilyPieceSupport F

theorem originalCutStage_component_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    Nat.card S.retainedGraph.ConnectedComponent = S.B.card + 1 := by
  have h := S.payload
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hcount, _⟩
  exact hcount

theorem originalCutStage_vertex_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel S.retainedGraph.Adj := Classical.decRel _
    (∑ C : S.retainedGraph.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ R x) := by
  have h := S.payload
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum, _⟩
  exact hsum

theorem OriginalResidualCutStage.actual_edges
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    (S.B : Set (Sym2 (componentSupport χ R x))) ⊆
      ((selectedGraph χ R).induce (componentSupport χ R x)).edgeSet := by
  have h := S.payload
  rcases h with ⟨_, _, hedges, _⟩
  exact hedges

theorem OriginalResidualCutStage.support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) : S.rootSupport ⊆ W :=
  componentSupport_subset_of_residualSlotPartition χ R U W S.partition x S.root_mem

theorem OriginalResidualCutStage.component_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    Nat.card S.retainedGraph.ConnectedComponent = S.B.card + 1 :=
  originalCutStage_component_count S

theorem OriginalResidualCutStage.intrinsic_size_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel S.retainedGraph.Adj := Classical.decRel _
    (∑ C : S.retainedGraph.ConnectedComponent, Nat.card C.supp) = Nat.card S.rootSupport :=
  originalCutStage_vertex_sum S

theorem OriginalResidualCutStage.host_size_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) :
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ R x) := Classical.decPred _
    letI : DecidableRel S.retainedGraph.Adj := Classical.decRel _
    (∑ C : S.retainedGraph.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card S.rootSupport := by
  have h := S.payload
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum⟩
  exact hsum

/-- T is the cardinality of the ACTUAL dependent piece
carrier, not a supplied abstract counter. Every zero-cut stage contributes one. -/
theorem originalCutFamily_piece_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    Nat.card (OriginalCutFamilyPieceIndex F) = roots.length + originalCutFamilyCutTotal F := by
  induction F with
  | nil => simp [OriginalCutFamilyPieceIndex, originalCutFamilyCutTotal]
  | cons stage tail ih =>
    simp only [OriginalCutFamilyPieceIndex, Nat.card_sum, originalCutFamilyCutTotal,
      List.length_cons]
    rw [originalCutStage_component_count stage, ih]
    omega

theorem originalCutFamily_piece_size_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    originalCutFamilyTotalPieceSize F =
      (roots.map (fun x => Nat.card (componentSupport χ R x))).sum := by
  classical
  induction F with
  | nil =>
    change (∑ i : PEmpty, (PEmpty.elim i : ℕ)) = 0
    exact Finset.sum_eq_zero fun i _ => PEmpty.elim i
  | @cons U W x xs stage tail ih =>
    change
      (∑ i : stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail,
        Sum.elim (fun C => Nat.card C.supp) (originalCutFamilyPieceSize tail) i) =
        Nat.card (componentSupport χ R x) +
          (xs.map (fun y => Nat.card (componentSupport χ R y))).sum
    rw [Fintype.sum_sumElim]
    rw [originalCutStage_vertex_sum stage]
    change Nat.card (componentSupport χ R x) + originalCutFamilyTotalPieceSize tail = _
    rw [ih]

/-- Public existence starts only from original chi/full r. The SAME final R and full initial certificates are retained; the ACTUAL data
family, T=c+b and total retained size n are derived, not assumed. -/
theorem exists_full_original_cut_family
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n))
      (F : OriginalResidualCutFamily χ R ∅ Set.univ roots),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      roots.length = Nat.card (selectedGraph χ R).ConnectedComponent ∧
      Nat.card (OriginalCutFamilyPieceIndex F) =
        Nat.card (selectedGraph χ R).ConnectedComponent + originalCutFamilyCutTotal F ∧
      originalCutFamilyTotalPieceSize F = n ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  obtain ⟨R, roots, hgreedy, hpieces, hcount, hsize, hcover, hdisjoint⟩ :=
    exists_full_original_component_ledger χ r
  let F := originalCutFamilyOfPieceSequence χ R ∅ Set.univ roots hpieces
  have hT : Nat.card (OriginalCutFamilyPieceIndex F) =
      Nat.card (selectedGraph χ R).ConnectedComponent + originalCutFamilyCutTotal F := by
    rw [originalCutFamily_piece_count F, hcount]
  have hS : originalCutFamilyTotalPieceSize F = n :=
    (originalCutFamily_piece_size_sum F).trans hsize
  exact ⟨R, roots, F, hgreedy, hpieces, hcount, hT, hS, hcover, hdisjoint⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- With the literal FULL tail edgeless, all selected
owners of every original color lie wholly in the earlier vertices or current
WHOLE component. Earlier and current cut colors are included without exception. Only the exact original slot partition and actual component definition are used. -/
theorem original_owner_inside_processed_prefix_of_edgeless_tail
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ R U W) (x : Fin n)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (c : Fin q) :
    EdgeInside (Wᶜ ∪ componentSupport χ R x) (R.edge c).val := by
  by_cases hc : c ∈ U
  · intro z hz
    exact Or.inl (hpartition.removed_outside c hc z hz)
  · have hinside : EdgeInside W (R.edge c).val :=
      hpartition.eligible_inside c hc
    have hselected : (R.edge c).val ∈ (selectedGraph χ R).edgeSet := by
      rw [selectedGraph_edgeSet]
      exact ⟨c, rfl⟩
    obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective (R.edge c).val
    have hadj : (selectedGraph χ R).Adj u v := by
      rw [← huv] at hselected
      exact hselected
    have huOwner : u ∈ (R.edge c).val := by
      rw [← huv]
      exact Sym2.mem_mk_left u v
    have hvOwner : v ∈ (R.edge c).val := by
      rw [← huv]
      exact Sym2.mem_mk_right u v
    have huW : u ∈ W := hinside u huOwner
    have hvW : v ∈ W := hinside v hvOwner
    have hcomponent : u ∈ componentSupport χ R x ↔
        v ∈ componentSupport χ R x := by
      change u ∈ ((selectedGraph χ R).connectedComponentMk x).supp ↔
        v ∈ ((selectedGraph χ R).connectedComponentMk x).supp
      exact ((selectedGraph χ R).connectedComponentMk x).mem_supp_congr_adj hadj
    by_cases huX : u ∈ componentSupport χ R x
    · have hvX : v ∈ componentSupport χ R x := hcomponent.mp huX
      rw [← huv]
      intro z hz
      apply Or.inr
      rcases Sym2.mem_iff.mp hz with hzu | hzv
      · rw [hzu]
        exact huX
      · rw [hzv]
        exact hvX
    · have hvX : v ∉ componentSupport χ R x :=
        fun hv => huX (hcomponent.mpr hv)
      let uT : {z : Fin n // z ∈ W \ componentSupport χ R x} := ⟨u, huW, huX⟩
      let vT : {z : Fin n // z ∈ W \ componentSupport χ R x} := ⟨v, hvW, hvX⟩
      have htailAdj : ((selectedGraph χ R).induce
          (W \ componentSupport χ R x)).Adj uT vT := by
        change (selectedGraph χ R).Adj u v
        exact hadj
      have hfalse : False := by
        simp only [htail, SimpleGraph.bot_adj] at htailAdj
      exact hfalse.elim

/-- Stage method spelling for the same exact confinement. The premise concerns the FULL selected graph on the unprocessed tail, not the
final globally cut graph. Its source can be the uncut-tail endpoint theorem. -/
theorem OriginalResidualCutStage.owner_inside_processed_prefix
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (c : Fin q) :
    EdgeInside (Wᶜ ∪ componentSupport χ R x) (R.edge c).val :=
  original_owner_inside_processed_prefix_of_edgeless_tail
    χ R U W S.partition x htail c

/-- Every SAME original color is realized by a literal
original complete-host edge wholly in the processed prefix. No reduced palette
or cardinality assumption occurs. Properness and m ≥ k are separate obligations. -/
theorem OriginalResidualCutStage.every_color_in_processed_prefix
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (c : Fin q) :
    ∃ e : HostEdge n,
      EdgeInside (Wᶜ ∪ componentSupport χ R x) e.val ∧ χ e = c :=
  ⟨R.edge c, S.owner_inside_processed_prefix htail c, R.color_eq c⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperSubgraphComponentDecomposition

open SimpleGraph

universe u

variable {V : Type u} {G H : SimpleGraph V}

/-- An H-walk cannot leave an actual original G-component when H ≤ G.
This specializes the physical Mathlib `walk_toSimpleGraph` recursion by
coercing each actual H adjacency through the supplied subgraph inequality. -/
def originalComponentRestrictedWalk
    (hHG : H ≤ G) (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) (p : H.Walk u v) :
    (H.induce C.supp).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hu (hHG h)
    have h' : (H.induce C.supp).Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (originalComponentRestrictedWalk hHG C hw hv p)

/-- Exact actual reachability reflection for H restricted to an original
G-component. Both directions include reflexive walks at isolated vertices. -/
theorem reachable_induce_original_component_iff
    (hHG : H ≤ G) (C : G.ConnectedComponent) (u v : C.supp) :
    (H.induce C.supp).Reachable u v ↔ H.Reachable u.val v.val := by
  constructor
  · intro h
    exact h.map (SimpleGraph.Embedding.induce (G := H) C.supp).toHom
  · rintro ⟨p⟩
    exact ⟨originalComponentRestrictedWalk hHG C u.property v.property p⟩

/-- Inclusion of each actual locally induced H-component into host H.
The target is the quotient of actual host reachability, not a proposed
partition type or a chosen list of desired supports. -/
def originalComponentRefinementMap (G H : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, (H.induce C.supp).ConnectedComponent) →
      H.ConnectedComponent :=
  fun P => P.2.map (SimpleGraph.Embedding.induce (G := H) P.1.supp).toHom

/-- The mapped host component has exactly the lifted actual local support;
no support equality is assumed. -/
theorem original_component_refinement_map_supp
    (hHG : H ≤ G) (C : G.ConnectedComponent)
    (c : (H.induce C.supp).ConnectedComponent) :
    (originalComponentRefinementMap G H ⟨C, c⟩).supp =
      (Subtype.val '' c.supp : Set V) := by
  refine c.ind ?_
  intro u
  change (H.connectedComponentMk u.val).supp =
    (Subtype.val '' ((H.induce C.supp).connectedComponentMk u).supp : Set V)
  ext v
  constructor
  · intro hv
    have hr : H.Reachable v u.val := ConnectedComponent.exact hv
    have hvC : v ∈ C.supp :=
      (ConnectedComponent.sound (hr.mono hHG)).trans u.property
    refine ⟨⟨v, hvC⟩, ?_, rfl⟩
    exact ConnectedComponent.sound
      ((reachable_induce_original_component_iff hHG C ⟨v, hvC⟩ u).mpr hr)
  · rintro ⟨w, hw, rfl⟩
    have hr : (H.induce C.supp).Reachable w u := ConnectedComponent.exact hw
    exact ConnectedComponent.sound
      ((reachable_induce_original_component_iff hHG C w u).mp hr)

/-- Actual host H-components correspond bijectively to the dependent family
of actual H-components inside original G-components. This derives the
correspondence from H ≤ G, including empty carriers and isolated vertices. -/
theorem original_component_refinement_map_bijective
    (hHG : H ≤ G) : Function.Bijective (originalComponentRefinementMap G H) := by
  constructor
  · rintro ⟨C, c⟩ ⟨E, d⟩ h
    have hCE : C = E := by
      obtain ⟨u, hu⟩ := c.nonempty_supp
      have huHost : u.val ∈ (originalComponentRefinementMap G H ⟨C, c⟩).supp := by
        rw [original_component_refinement_map_supp hHG C c]
        exact ⟨u, hu, rfl⟩
      have huOther : u.val ∈ (originalComponentRefinementMap G H ⟨E, d⟩).supp := by
        rw [← h]
        exact huHost
      rw [original_component_refinement_map_supp hHG E d] at huOther
      obtain ⟨v, _hv, hvu⟩ := huOther
      have huE : u.val ∈ E.supp := hvu ▸ v.property
      exact ConnectedComponent.eq_of_common_vertex u.property huE
    cases hCE
    have hsupport := congrArg (fun K : H.ConnectedComponent => K.supp) h
    rw [original_component_refinement_map_supp hHG C c,
      original_component_refinement_map_supp hHG C d] at hsupport
    have hcd : c = d :=
      ConnectedComponent.supp_injective
        (Subtype.val_injective.image_injective hsupport)
    cases hcd
    rfl
  · intro K
    obtain ⟨v, rfl⟩ := K.exists_rep
    refine ⟨⟨G.connectedComponentMk v,
      (H.induce (G.connectedComponentMk v).supp).connectedComponentMk ⟨v, rfl⟩⟩, ?_⟩
    rfl

/-- The actual derived component correspondence, oriented local-to-host so
that its support formula is the original subtype lifting. -/
noncomputable def originalComponentRefinementEquiv
    (hHG : H ≤ G) :
    (Σ C : G.ConnectedComponent, (H.induce C.supp).ConnectedComponent) ≃
      H.ConnectedComponent :=
  Equiv.ofBijective (originalComponentRefinementMap G H)
    (original_component_refinement_map_bijective hHG)

theorem original_component_refinement_equiv_supp
    (hHG : H ≤ G) (C : G.ConnectedComponent)
    (c : (H.induce C.supp).ConnectedComponent) :
    (originalComponentRefinementEquiv hHG ⟨C, c⟩).supp =
      (Subtype.val '' c.supp : Set V) := by
  exact original_component_refinement_map_supp hHG C c

end ErdosProblems.PathUpperSubgraphComponentDecomposition

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

noncomputable def liftOriginalComponentCut (X : Set (Fin n))
    (B : Finset (Sym2 X)) : Finset (Sym2 (Fin n)) := by
  classical
  exact B.image (Sym2.map (Subtype.val : X → Fin n))

theorem liftOriginalComponentCut_card (X : Set (Fin n)) (B : Finset (Sym2 X)) :
    (liftOriginalComponentCut X B).card = B.card := by
  classical
  exact Finset.card_image_of_injective B (Sym2.map.injective Subtype.val_injective)

theorem liftOriginalComponentCut_mem_map_iff (X : Set (Fin n))
    (B : Finset (Sym2 X)) (e : Sym2 X) :
    Sym2.map (Subtype.val : X → Fin n) e ∈ liftOriginalComponentCut X B ↔ e ∈ B := by
  classical
  constructor
  · intro he
    obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp he
    have h : d = e := Sym2.map.injective Subtype.val_injective hde
    exact h ▸ hd
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem liftOriginalComponentCut_vertex_mem (X : Set (Fin n)) (B : Finset (Sym2 X))
    {e : Sym2 (Fin n)} (he : e ∈ liftOriginalComponentCut X B)
    {v : Fin n} (hv : v ∈ e) : v ∈ X := by
  classical
  obtain ⟨d, _hd, hde⟩ := Finset.mem_image.mp he
  rw [← hde] at hv
  obtain ⟨z, _hz, hzv⟩ := Sym2.mem_map.mp hv
  exact hzv ▸ z.property

theorem liftOriginalComponentCut_selected_edges (G : SimpleGraph (Fin n))
    (X : Set (Fin n)) (B : Finset (Sym2 X))
    (hB : (B : Set (Sym2 X)) ⊆ (G.induce X).edgeSet) :
    (liftOriginalComponentCut X B : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
  classical
  intro e he
  obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp he
  have hhost := (SimpleGraph.Embedding.induce (G := G) X).toHom.map_mem_edgeSet (hB hd)
  exact hde ▸ hhost

noncomputable def originalCutFamilyLiftedCuts
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Finset (Sym2 (Fin n)) := by
  classical
  exact match F with
  | .nil _ _ => ∅
  | .cons stage tail =>
      liftOriginalComponentCut stage.rootSupport stage.B ∪ originalCutFamilyLiftedCuts tail

/-- Every actual cut endpoint lies in its actual residual host W. -/
theorem originalCutFamilyLiftedCuts_vertex_mem
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ {e : Sym2 (Fin n)}, e ∈ originalCutFamilyLiftedCuts F →
      ∀ {v : Fin n}, v ∈ e → v ∈ W := by
  classical
  induction F with
  | nil => simp [originalCutFamilyLiftedCuts]
  | cons stage tail ih =>
    intro e he v hv
    change e ∈ liftOriginalComponentCut stage.rootSupport stage.B ∪
      originalCutFamilyLiftedCuts tail at he
    rcases Finset.mem_union.mp he with he | he
    · exact stage.support_subset (liftOriginalComponentCut_vertex_mem _ _ he hv)
    · exact (ih he hv).1

/-- Actual whole-prefix removal makes head and tail lifted cuts disjoint. -/
theorem originalCutFamilyLiftedCuts_card
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    (originalCutFamilyLiftedCuts F).card = F.cutCount := by
  classical
  induction F with
  | nil => simp [originalCutFamilyLiftedCuts, OriginalResidualCutFamily.cutCount,
      originalCutFamilyCutTotal]
  | cons stage tail ih =>
    have hdis : Disjoint (liftOriginalComponentCut stage.rootSupport stage.B)
        (originalCutFamilyLiftedCuts tail) := by
      apply Finset.disjoint_left.mpr
      intro e he ht
      have hx := liftOriginalComponentCut_vertex_mem _ _ he (Sym2.out_fst_mem e)
      have hy := originalCutFamilyLiftedCuts_vertex_mem tail ht (Sym2.out_fst_mem e)
      exact hy.2 hx
    change (liftOriginalComponentCut stage.rootSupport stage.B ∪
      originalCutFamilyLiftedCuts tail).card = stage.B.card + tail.cutCount
    exact (Finset.card_union_of_disjoint hdis).trans
      (congrArg₂ Nat.add (liftOriginalComponentCut_card _ stage.B) ih)

/-- Each lifted cut is a literal selected edge, not only an abstract bridge. -/
theorem originalCutFamilyLiftedCuts_selected_edges
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    originalCutFamilyLiftedCuts F ⊆ (selectedGraph χ R).edgeFinset := by
  classical
  induction F with
  | nil => simp [originalCutFamilyLiftedCuts]
  | cons stage tail ih =>
    intro e he
    change e ∈ liftOriginalComponentCut stage.rootSupport stage.B ∪
      originalCutFamilyLiftedCuts tail at he
    rcases Finset.mem_union.mp he with he | he
    · apply SimpleGraph.mem_edgeFinset.mpr
      exact liftOriginalComponentCut_selected_edges _ _ _ stage.actual_edges he
    · exact ih he

noncomputable def originalCutFamilyGlobalRetainedGraph
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : SimpleGraph (Fin n) :=
  (selectedGraph χ R).deleteEdges (originalCutFamilyLiftedCuts F)

/-- The literal global graph restricts to the stored actual first-stage D.
Tail cuts cannot affect a vertex in the whole removed head component. -/
theorem originalCutFamily_global_head_induce
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (stage : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs) :
    (originalCutFamilyGlobalRetainedGraph (.cons stage tail)).induce stage.rootSupport =
      stage.retainedGraph := by
  classical
  ext u v
  dsimp only [OriginalResidualCutStage.rootSupport] at u v ⊢
  have htail : s(u.val, v.val) ∉ originalCutFamilyLiftedCuts tail := by
    intro he
    have hu := originalCutFamilyLiftedCuts_vertex_mem tail he (Sym2.mem_mk_left _ _)
    exact hu.2 u.property
  have hhead : s(u.val, v.val) ∈ liftOriginalComponentCut (componentSupport χ R x) stage.B ↔
      s(u, v) ∈ stage.B := liftOriginalComponentCut_mem_map_iff _ _ s(u, v)
  simp only [originalCutFamilyGlobalRetainedGraph, originalCutFamilyLiftedCuts,
    OriginalResidualCutStage.rootSupport, OriginalResidualCutStage.retainedGraph, OriginalResidualRetainedGraph,
    SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Finset.mem_coe, Finset.mem_union,
    htail, or_false, hhead]

/-- Exact edge deletion for actual cuts; the whole original palette is retained. -/
theorem originalCutFamily_global_edge_card
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    let H := originalCutFamilyGlobalRetainedGraph F
    letI : DecidableRel H.Adj := Classical.decRel _
    q = H.edgeFinset.card + F.cutCount := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hcard : H.edgeFinset.card + (originalCutFamilyLiftedCuts F).card =
      (selectedGraph χ R).edgeFinset.card := by
    rw [show H = (selectedGraph χ R).deleteEdges (originalCutFamilyLiftedCuts F) from rfl,
      SimpleGraph.edgeFinset_deleteEdges]
    exact Finset.card_sdiff_add_card_eq_card (originalCutFamilyLiftedCuts_selected_edges F)
  rw [originalCutFamilyLiftedCuts_card F, selectedGraph_card_edgeFinset] at hcard
  exact hcard.symm

/-- Count the edges of the ACTUAL global components after literal deletion. -/
theorem originalCutFamily_global_component_edge_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    let H := originalCutFamilyGlobalRetainedGraph F
    letI : DecidableRel H.Adj := Classical.decRel _
    q = (∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) + F.cutCount := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hq := originalCutFamily_global_edge_card F
  have hparts := ErdosProblems.AntiRamseyPathFiveComponents.edge_card_eq_sum_component_edge_card H
  change q = H.edgeFinset.card + F.cutCount at hq
  exact hq.trans (congrArg (fun t => t + F.cutCount) hparts)

/-- Deleting edges keeps every host vertex, including all isolated vertices. -/
theorem originalCutFamily_global_component_vertex_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    let H := originalCutFamilyGlobalRetainedGraph F
    letI : DecidableRel H.Adj := Classical.decRel _
    (∑ C : H.ConnectedComponent, Nat.card C.supp) = n := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hparts := ErdosProblems.AntiRamseyPathFiveComponents.vertex_card_eq_sum_component_card H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hparts.symm

/-- Apply the derived generic refinement to the literal actual deletion graph.
Matching these actual local H-components to every stage D remains a separate seam. -/
noncomputable def originalCutFamilyGlobalComponentRefinement
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    (Σ C : (selectedGraph χ R).ConnectedComponent,
      ((originalCutFamilyGlobalRetainedGraph F).induce C.supp).ConnectedComponent) ≃
      (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent :=
  ErdosProblems.PathUpperSubgraphComponentDecomposition.originalComponentRefinementEquiv
    (G := selectedGraph χ R) (H := originalCutFamilyGlobalRetainedGraph F)
    (show originalCutFamilyGlobalRetainedGraph F ≤ selectedGraph χ R from
      SimpleGraph.deleteEdges_le (G := selectedGraph χ R)
        (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n))))

/-- Public existence derives the actual family and global graph from χ/full r.
No cuts, counts, partitions or favorable component correspondence are assumed. -/
theorem exists_full_original_global_cut_ledger
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n))
      (F : OriginalResidualCutFamily χ R ∅ Set.univ roots),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      roots.length = Nat.card (selectedGraph χ R).ConnectedComponent ∧
      Nat.card F.PieceIndex =
        Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount ∧
      originalCutFamilyTotalPieceSize F = n ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) ∧
      (originalCutFamilyLiftedCuts F).card = F.cutCount ∧
      (originalCutFamilyLiftedCuts F ⊆ (selectedGraph χ R).edgeFinset) ∧
      (let H := originalCutFamilyGlobalRetainedGraph F
       letI : DecidableRel H.Adj := Classical.decRel _
       q = (∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) + F.cutCount) ∧
      (let H := originalCutFamilyGlobalRetainedGraph F
       letI : DecidableRel H.Adj := Classical.decRel _
       (∑ C : H.ConnectedComponent, Nat.card C.supp) = n) := by
  obtain ⟨R, roots, F, hgreedy, hpieces, hcount, hT, hS, hcover, hdisjoint⟩ :=
    exists_full_original_cut_family χ r
  exact ⟨R, roots, F, hgreedy, hpieces, hcount, hT, hS, hcover, hdisjoint,
    originalCutFamilyLiftedCuts_card F, originalCutFamilyLiftedCuts_selected_edges F,
    originalCutFamily_global_component_edge_sum F, originalCutFamily_global_component_vertex_sum F⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The actual stage and actual local component underlying a family piece. -/
structure OriginalCutFamilyLocalPieceData
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) where
  U : Set (Fin q)
  W : Set (Fin n)
  x : Fin n
  stage : OriginalResidualCutStage χ R U W x
  component : stage.retainedGraph.ConnectedComponent

noncomputable def originalCutFamilyLocalPieceData
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    F.PieceIndex → OriginalCutFamilyLocalPieceData χ R :=
  match F with
  | .nil _ _ => fun i => PEmpty.elim i
  | .cons stage tail => Sum.elim (fun C => ⟨_, _, _, stage, C⟩)
      (originalCutFamilyLocalPieceData tail)

theorem originalCutFamily_local_stage_support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i, (originalCutFamilyLocalPieceData F i).stage.rootSupport ⊆ W := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
    cases i with
    | inl C => exact stage.support_subset
    | inr i => exact fun _ hv => (ih i hv).1

theorem originalCutFamily_local_piece_support
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i, (Subtype.val '' (originalCutFamilyLocalPieceData F i).component.supp : Set (Fin n)) =
      F.pieceSupport i := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
    cases i with
    | inl C => rfl
    | inr i => exact ih i

/-- Ancestor head cuts vanish on the genuine tail residual vertex carrier. -/
theorem originalCutFamily_global_tail_induce
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (stage : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs)
    (Z : Set (Fin n)) (hZ : Z ⊆ W \ componentSupport χ R x) :
    (originalCutFamilyGlobalRetainedGraph (.cons stage tail)).induce Z =
      (originalCutFamilyGlobalRetainedGraph tail).induce Z := by
  classical
  ext u v
  have hhead : s(u.val, v.val) ∉ liftOriginalComponentCut stage.rootSupport stage.B := by
    intro he
    exact (hZ u.property).2
      (liftOriginalComponentCut_vertex_mem _ _ he (Sym2.mem_mk_left _ _))
  simp only [originalCutFamilyGlobalRetainedGraph, originalCutFamilyLiftedCuts,
    SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Finset.mem_coe,
    Finset.mem_union, hhead, false_or]

/-- The restriction equality is DERIVED for every actual family piece's stage. -/
theorem originalCutFamily_global_piece_stage_induce
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i, (originalCutFamilyGlobalRetainedGraph F).induce
        (originalCutFamilyLocalPieceData F i).stage.rootSupport =
      (originalCutFamilyLocalPieceData F i).stage.retainedGraph := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
    cases i with
    | inl C => exact originalCutFamily_global_head_induce stage tail
    | inr i =>
      exact (originalCutFamily_global_tail_induce stage tail
        (originalCutFamilyLocalPieceData tail i).stage.rootSupport
        (originalCutFamily_local_stage_support_subset tail i)).trans (ih i)

theorem connectedComponent_cast_supp
    {V : Type*} {G H : SimpleGraph V} (h : G = H) (C : G.ConnectedComponent) :
    (Equiv.cast (congrArg (fun K : SimpleGraph V => K.ConnectedComponent) h) C).supp = C.supp := by
  cases h
  rfl

/-- Actual local-to-host component map, using only the derived graph equality. -/
noncomputable def originalCutFamilyGlobalPieceMap
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent := by
  let P := originalCutFamilyLocalPieceData F i
  have hgraph : (originalCutFamilyGlobalRetainedGraph F).induce
      (componentSupport χ R P.x) = P.stage.retainedGraph := by
    simpa only [OriginalResidualCutStage.rootSupport] using
      originalCutFamily_global_piece_stage_induce F i
  let C := Equiv.cast
    (congrArg (fun K : SimpleGraph (componentSupport χ R P.x) => K.ConnectedComponent)
      hgraph.symm) P.component
  exact ErdosProblems.PathUpperSubgraphComponentDecomposition.originalComponentRefinementMap
    (selectedGraph χ R) (originalCutFamilyGlobalRetainedGraph F)
    ⟨(selectedGraph χ R).connectedComponentMk P.x, C⟩

theorem originalCutFamilyGlobalPieceMap_supp
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    (originalCutFamilyGlobalPieceMap F i).supp = F.pieceSupport i := by
  let P := originalCutFamilyLocalPieceData F i
  have hgraph : (originalCutFamilyGlobalRetainedGraph F).induce
      (componentSupport χ R P.x) = P.stage.retainedGraph := by
    simpa only [OriginalResidualCutStage.rootSupport] using
      originalCutFamily_global_piece_stage_induce F i
  let C : ((originalCutFamilyGlobalRetainedGraph F).induce
      (componentSupport χ R P.x)).ConnectedComponent :=
    Equiv.cast
      (congrArg (fun K : SimpleGraph (componentSupport χ R P.x) => K.ConnectedComponent)
        hgraph.symm) P.component
  have hle : originalCutFamilyGlobalRetainedGraph F ≤ selectedGraph χ R := by
    exact (show (selectedGraph χ R).deleteEdges
        (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n))) ≤ selectedGraph χ R from
      SimpleGraph.deleteEdges_le (G := selectedGraph χ R)
        (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n))))
  have hmap :=
    ErdosProblems.PathUpperSubgraphComponentDecomposition.original_component_refinement_map_supp
      (G := selectedGraph χ R) (H := originalCutFamilyGlobalRetainedGraph F)
      hle ((selectedGraph χ R).connectedComponentMk P.x) C
  have hcast : C.supp = P.component.supp :=
    connectedComponent_cast_supp hgraph.symm P.component
  have himage := congrArg
    (fun S : Set (componentSupport χ R P.x) => (Subtype.val '' S : Set (Fin n))) hcast
  change
    (ErdosProblems.PathUpperSubgraphComponentDecomposition.originalComponentRefinementMap
      (selectedGraph χ R) (originalCutFamilyGlobalRetainedGraph F)
      ⟨(selectedGraph χ R).connectedComponentMk P.x, C⟩).supp = F.pieceSupport i
  exact hmap.trans (himage.trans (originalCutFamily_local_piece_support F i))

theorem originalCutFamily_piece_support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    F.pieceSupport i ⊆ W := by
  rw [← originalCutFamily_local_piece_support F i]
  rintro v ⟨u, _hu, rfl⟩
  exact originalCutFamily_local_stage_support_subset F i u.property

theorem originalCutFamily_piece_support_nonempty
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    (F.pieceSupport i).Nonempty := by
  rw [← originalCutFamily_local_piece_support F i]
  obtain ⟨u, hu⟩ := (originalCutFamilyLocalPieceData F i).component.nonempty_supp
  exact ⟨u.val, u, hu, rfl⟩

theorem original_host_piece_disjoint
    {X : Set (Fin n)} (D : SimpleGraph X) {C E : D.ConnectedComponent} (hCE : C ≠ E) :
    Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨c, hc, hcv⟩ ⟨e, he, hev⟩
  have hce : c = e := Subtype.ext (hcv.trans hev.symm)
  exact (Set.disjoint_left.mp (D.pairwise_disjoint_supp_connectedComponent hCE))
    hc (hce.symm ▸ he)

theorem originalCutFamily_piece_support_disjoint
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i j, i ≠ j → Disjoint (F.pieceSupport i) (F.pieceSupport j) := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i j hij
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i j
    cases i with
    | inl C =>
      cases j with
      | inl E =>
        exact original_host_piece_disjoint stage.retainedGraph
          (fun h => hij (congrArg Sum.inl h))
      | inr j =>
        apply Set.disjoint_left.mpr
        rintro v ⟨u, _hu, rfl⟩ hv
        exact (originalCutFamily_piece_support_subset tail j hv).2 u.property
    | inr i =>
      cases j with
      | inl C =>
        apply Set.disjoint_left.mpr
        rintro v hv ⟨u, _hu, rfl⟩
        exact (originalCutFamily_piece_support_subset tail i hv).2 u.property
      | inr j => exact ih i j (fun h => hij (congrArg Sum.inr h))

theorem originalCutFamily_piece_support_cover
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ v, v ∈ W ↔ ∃ i, v ∈ F.pieceSupport i := by
  induction F with
  | nil empty partition =>
    intro v
    constructor
    · intro hv
      rw [empty] at hv
      exact hv.elim
    · rintro ⟨i, _⟩; exact PEmpty.elim i
  | @cons U W x xs stage tail ih =>
    intro v
    constructor
    · intro hv
      by_cases hx : v ∈ componentSupport χ R x
      · let u : componentSupport χ R x := ⟨v, hx⟩
        refine ⟨Sum.inl (stage.retainedGraph.connectedComponentMk u), ?_⟩
        exact ⟨u, ConnectedComponent.connectedComponentMk_mem, rfl⟩
      · obtain ⟨i, hi⟩ := (ih v).mp ⟨hv, hx⟩
        exact ⟨Sum.inr i, hi⟩
    · rintro ⟨i, hi⟩
      exact originalCutFamily_piece_support_subset (.cons stage tail) i hi

/-- Bijection follows from the DERIVED actual supports, not a desired partition. -/
theorem originalCutFamilyGlobalPieceMap_bijective
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) :
    Function.Bijective (originalCutFamilyGlobalPieceMap F) := by
  constructor
  · intro i j hij
    by_contra hne
    obtain ⟨v, hv⟩ := originalCutFamily_piece_support_nonempty F i
    have hsupport : F.pieceSupport i = F.pieceSupport j := by
      rw [← originalCutFamilyGlobalPieceMap_supp F i,
        ← originalCutFamilyGlobalPieceMap_supp F j, hij]
    exact (Set.disjoint_left.mp (originalCutFamily_piece_support_disjoint F i j hne))
      hv (hsupport ▸ hv)
  · intro C
    obtain ⟨v, hvC⟩ := C.nonempty_supp
    obtain ⟨i, hi⟩ := (originalCutFamily_piece_support_cover F v).mp (Set.mem_univ v)
    refine ⟨i, ConnectedComponent.eq_of_common_vertex ?_ hvC⟩
    rw [originalCutFamilyGlobalPieceMap_supp F i]
    exact hi

noncomputable def originalCutFamilyGlobalComponentCoupling
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) :
    (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent ≃ F.PieceIndex :=
  (Equiv.ofBijective (originalCutFamilyGlobalPieceMap F)
    (originalCutFamilyGlobalPieceMap_bijective F)).symm

theorem originalCutFamilyGlobalComponentCoupling_supp
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots)
    (i : F.PieceIndex) :
    ((originalCutFamilyGlobalComponentCoupling F).symm i).supp = F.pieceSupport i :=
  originalCutFamilyGlobalPieceMap_supp F i

theorem originalCutFamily_global_component_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) :
    Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent =
      Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount := by
  calc
    Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent = Nat.card F.PieceIndex :=
      Nat.card_congr (originalCutFamilyGlobalComponentCoupling F)
    _ = roots.length + F.cutCount := originalCutFamily_piece_count F
    _ = Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount := by
      rw [residualGreedySequence_root_count χ R roots F.toGreedySequence]

theorem exists_full_original_global_component_coupling
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n))
      (F : OriginalResidualCutFamily χ R ∅ Set.univ roots),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      Nonempty ((originalCutFamilyGlobalRetainedGraph F).ConnectedComponent ≃ F.PieceIndex) ∧
      (∀ i : F.PieceIndex,
        ((originalCutFamilyGlobalComponentCoupling F).symm i).supp = F.pieceSupport i) ∧
      Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent =
        Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount := by
  obtain ⟨R, roots, F, hgreedy, hpieces, _hcount, _hT, _hS, _hcover, _hdisjoint⟩ :=
    exists_full_original_cut_family χ r
  exact ⟨R, roots, F, hgreedy, hpieces, ⟨originalCutFamilyGlobalComponentCoupling F⟩,
    originalCutFamilyGlobalComponentCoupling_supp F, originalCutFamily_global_component_count F⟩

end ErdosProblems.PathUpperReduction

section

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem selected_host_owner
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (e : HostEdge n) (he : e.val ∈ (selectedGraph χ R).edgeSet) :
    e = R.edge (χ e) := by
  rw [selectedGraph_edgeSet] at he
  obtain ⟨c, hc⟩ := he
  have howner : e = R.edge c := Subtype.ext hc.symm
  have hcolor : χ e = c := (congrArg χ howner).trans (R.color_eq c)
  rw [hcolor]
  exact howner

/-- Every A color has its SAME original owner in the actual lifted head cut.
Owner containment is derived from the stage maximum, not supplied. -/
theorem OriginalResidualCutStage.owner_mem_lifted_cut
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (c : EligibleInteriorColor χ U (componentSupport χ R x)) (hc : c ∈ S.A) :
    (R.edge c.val).val ∈ liftOriginalComponentCut S.rootSupport S.B := by
  classical
  have hinside := selected_edge_inside_of_eligibleInterior_color
    χ R U W S.partition x S.support_subset S.maximum c.val c.property
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective ((R.edge c.val).val)
  change s(a, b) = (R.edge c.val).val at hab
  have ha : a ∈ (R.edge c.val).val := by
    rw [← hab]
    exact Sym2.mem_mk_left _ _
  have hb : b ∈ (R.edge c.val).val := by
    rw [← hab]
    exact Sym2.mem_mk_right _ _
  let z : componentSupport χ R x := ⟨a, hinside a ha⟩
  let w : componentSupport χ R x := ⟨b, hinside b hb⟩
  have hmap : Sym2.map (Subtype.val : componentSupport χ R x → Fin n) s(z, w) =
      (R.edge c.val).val := by
    simpa only [Sym2.map_mk, z, w] using hab
  have hBset : (S.B : Set (Sym2 (componentSupport χ R x))) =
      OriginalResidualColorDeletion χ R U (componentSupport χ R x) (S.A : Set _) :=
    S.payload.2.1
  have hB : s(z, w) ∈ S.B := by
    change s(z, w) ∈ (S.B : Set (Sym2 (componentSupport χ R x)))
    rw [hBset]
    exact ⟨c, hc, hmap⟩
  change (R.edge c.val).val ∈ S.B.image
    (Sym2.map (Subtype.val : componentSupport χ R x → Fin n))
  exact Finset.mem_image.mpr ⟨s(z, w), hB, hmap⟩

theorem global_retained_host_edge_facts
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (e : HostEdge n)
    (he : e.val ∈ (originalCutFamilyGlobalRetainedGraph F).edgeSet) :
    e.val ∈ (selectedGraph χ R).edgeSet ∧ e.val ∉ originalCutFamilyLiftedCuts F := by
  simpa only [originalCutFamilyGlobalRetainedGraph, SimpleGraph.edgeSet_deleteEdges,
    Set.mem_sdiff, Finset.mem_coe] using he

/-- A retained original edge inside the earliest remaining carrier avoids
the frozen prefix U and ALL actual head-A labels. -/
theorem originalCutFamily_head_retained_edge_avoids_prefix_and_cut
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs)
    (f : HostEdge n)
    (hf : f.val ∈ (originalCutFamilyGlobalRetainedGraph (.cons S tail)).edgeSet)
    (hinside : EdgeInside W f.val) :
    χ f ∉ U ∧ χ f ∉ S.A.image (fun c => c.val) := by
  classical
  obtain ⟨hfG, hfcut⟩ := global_retained_host_edge_facts (.cons S tail) f hf
  have howner := selected_host_owner χ R f hfG
  have hz : f.val.out.1 ∈ f.val := Sym2.out_fst_mem _
  have hzowner : f.val.out.1 ∈ (R.edge (χ f)).val := by
    rw [← howner]
    exact hz
  constructor
  · exact selected_slot_color_not_removed_of_endpoint_in_remaining
      χ R U W S.partition (χ f) f.val.out.1 hzowner (hinside _ hz)
  · intro hA
    obtain ⟨c, hc, hcf⟩ := Finset.mem_image.mp hA
    have hmem : f.val ∈ liftOriginalComponentCut S.rootSupport S.B := by
      rw [howner, ← hcf]
      exact S.owner_mem_lifted_cut c hc
    apply hfcut
    change f.val ∈ liftOriginalComponentCut S.rootSupport S.B ∪
      originalCutFamilyLiftedCuts tail
    exact Finset.mem_union.mpr (Or.inl hmem)

theorem originalCutFamily_global_cons_le_tail
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs) :
    originalCutFamilyGlobalRetainedGraph (.cons S tail) ≤
      originalCutFamilyGlobalRetainedGraph tail := by
  classical
  apply SimpleGraph.deleteEdges_anti
  intro e he
  change e ∈ liftOriginalComponentCut S.rootSupport S.B ∪
    originalCutFamilyLiftedCuts tail
  exact Finset.mem_union.mpr (Or.inr he)

theorem originalCutFamily_head_label_fresh_of_cover
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs)
    (e f : HostEdge n)
    (hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val))
    (hf : f.val ∈ (originalCutFamilyGlobalRetainedGraph (.cons S tail)).edgeSet)
    (hinside : EdgeInside W f.val) : χ f ≠ χ e := by
  obtain ⟨hU, hA⟩ := originalCutFamily_head_retained_edge_avoids_prefix_and_cut
    S tail f hf hinside
  intro heq
  rcases hcover with hcover | hcover
  · exact hU (heq.symm ▸ hcover)
  · exact hA (heq.symm ▸ hcover)

/-- Every joining host label between TWO distinct actual
pieces is fresh against ANY selected globally retained edge inside either
piece. Later U colors remain an alternative and are excluded at the EARLIEST
of the two chosen original stages. Singleton pieces are allowed. -/
theorem originalCutFamily_cross_piece_color_fresh
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ (i j : F.PieceIndex), i ≠ j →
      ∀ (e : HostEdge n) (u v : Fin n), e.val = s(u, v) →
        u ∈ F.pieceSupport i → v ∈ F.pieceSupport j →
        ∀ (f : HostEdge n), f.val ∈ (originalCutFamilyGlobalRetainedGraph F).edgeSet →
          (EdgeInside (F.pieceSupport i) f.val ∨ EdgeInside (F.pieceSupport j) f.val) →
            χ f ≠ χ e := by
  classical
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | @cons U W x xs S tail ih =>
    intro i j hij e u v he hu hv f hf hinside
    have hfW : EdgeInside W f.val := by
      intro z hz
      rcases hinside with hi | hj
      · exact originalCutFamily_piece_support_subset (.cons S tail) i (hi z hz)
      · exact originalCutFamily_piece_support_subset (.cons S tail) j (hj z hz)
    change S.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i j
    cases i with
    | inl C =>
      cases j with
      | inl E =>
        change u ∈ originalResidualHostPiece C at hu
        change v ∈ originalResidualHostPiece E at hv
        rcases hu with ⟨z, hz, rfl⟩
        rcases hv with ⟨w, hw, rfl⟩
        have hCE : C ≠ E := fun h => hij (congrArg Sum.inl h)
        have hnotreachable : ¬ S.retainedGraph.Reachable z w := by
          intro hreach
          have hzC : S.retainedGraph.connectedComponentMk z = C := hz
          have hwE : S.retainedGraph.connectedComponentMk w = E := hw
          exact hCE (hzC.symm.trans
            ((SimpleGraph.ConnectedComponent.sound hreach).trans hwE))
        have heX : EdgeInside S.rootSupport e.val := by
          intro a ha
          rw [he] at ha
          rcases Sym2.mem_iff.mp ha with rfl | rfl
          · exact z.property
          · exact w.property
        have hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val) := by
          by_cases hU : χ e ∈ U
          · exact Or.inl hU
          · right
            have h := S.payload
            rcases h with ⟨_, _, _, _, _, hcross, _⟩
            obtain ⟨hc, hA⟩ := hcross e heX hU z w he hnotreachable
            exact Finset.mem_image.mpr ⟨⟨χ e, hc⟩, hA, rfl⟩
        exact originalCutFamily_head_label_fresh_of_cover S tail e f hcover hf hfW
      | inr j =>
        change u ∈ originalResidualHostPiece C at hu
        change v ∈ tail.pieceSupport j at hv
        rcases hu with ⟨z, _hz, rfl⟩
        have hvLater := originalCutFamily_piece_support_subset tail j hv
        have h := S.payload
        rcases h with ⟨_, _, _, _, _, _, hout, _⟩
        have hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val) := by
          rcases hout e z.val v he z.property hvLater.1 hvLater.2 with hU | ⟨hc, hA⟩
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ e, hc⟩, hA, rfl⟩)
        exact originalCutFamily_head_label_fresh_of_cover S tail e f hcover hf hfW
    | inr i =>
      cases j with
      | inl E =>
        change u ∈ tail.pieceSupport i at hu
        change v ∈ originalResidualHostPiece E at hv
        rcases hv with ⟨w, _hw, rfl⟩
        have huLater := originalCutFamily_piece_support_subset tail i hu
        have heSwap : e.val = s(w.val, u) := he.trans Sym2.eq_swap
        have h := S.payload
        rcases h with ⟨_, _, _, _, _, _, hout, _⟩
        have hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val) := by
          rcases hout e w.val u heSwap w.property huLater.1 huLater.2 with hU | ⟨hc, hA⟩
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ e, hc⟩, hA, rfl⟩)
        exact originalCutFamily_head_label_fresh_of_cover S tail e f hcover hf hfW
      | inr j =>
        have hijTail : i ≠ j := fun h => hij (congrArg Sum.inr h)
        have hfTail : f.val ∈ (originalCutFamilyGlobalRetainedGraph tail).edgeSet :=
          SimpleGraph.edgeSet_mono (originalCutFamily_global_cons_le_tail S tail) hf
        exact ih i j hijTail e u v he hu hv f hfTail hinside

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem original_piece_copy_edge_inside
    {a : ℕ} {H : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (A : (pathGraph a).Copy H) (hA : Set.range (fun u => A u) ⊆ X)
    (e : (pathGraph a).edgeSet) : EdgeInside X (A.mapEdgeSet e).val := by
  intro v hv
  change v ∈ Sym2.map A.toHom e.val at hv
  obtain ⟨u, _hu, huv⟩ := Sym2.mem_map.mp hv
  exact huv ▸ hA ⟨u, rfl⟩

theorem original_piece_edge_has_vertex (e : Sym2 (Fin n)) :
    ∃ v, v ∈ e := by
  induction e using Sym2.inductionOn with
  | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩

/-- The actual original graph supplies every color and disjointness fact
needed to append two paths in different actual retained pieces. The order of
each path is preserved, with the literal last-A / first-B complete-host edge.
Counts a and b are numbers of vertices; a=b=1 is permitted. -/
theorem originalCutFamily_rainbow_path_of_two_piece_paths
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots)
    (i j : F.PieceIndex) (hij : i ≠ j)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (A : (pathGraph a).Copy (originalCutFamilyGlobalRetainedGraph F))
    (B : (pathGraph b).Copy (originalCutFamilyGlobalRetainedGraph F))
    (hA : Set.range (fun u => A u) ⊆ F.pieceSupport i)
    (hB : Set.range (fun u => B u) ⊆ F.pieceSupport j) :
    ∃ P : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow P.toHom χ ∧
      (∀ u : Fin a, P (Fin.castAdd b u) = A u) ∧
      (∀ v : Fin b, P (Fin.natAdd a v) = B v) := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hH : H ≤ selectedGraph χ R :=
    SimpleGraph.deleteEdges_le (G := selectedGraph χ R)
      (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n)))
  let As : (pathGraph a).Copy (selectedGraph χ R) :=
    (Copy.ofLE H (selectedGraph χ R) hH).comp A
  let Bs : (pathGraph b).Copy (selectedGraph χ R) :=
    (Copy.ofLE H (selectedGraph χ R) hH).comp B
  let Ah : (pathGraph a).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp As
  let Bh : (pathGraph b).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Bs
  have hAr : IsRainbow Ah.toHom χ := copy_in_selectedGraph_isRainbow χ R As
  have hBr : IsRainbow Bh.toHom χ := copy_in_selectedGraph_isRainbow χ R Bs
  have hs := originalCutFamily_piece_support_disjoint F i j hij
  have hdis : Disjoint (Set.range fun u : Fin a => Ah u)
      (Set.range fun v : Fin b => Bh v) := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact (Set.disjoint_left.mp hs) (hA hzA) (hB hzB)
  have hpal : ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      χ (Ah.toHom.mapEdgeSet e) ≠ χ (Bh.toHom.mapEdgeSet d) := by
    intro e d heq
    have hselected : As.mapEdgeSet e = Bs.mapEdgeSet d := by
      apply selectedColor_injective χ R
      change χ (Ah.toHom.mapEdgeSet e) = χ (Bh.toHom.mapEdgeSet d)
      exact heq
    have hval : (A.mapEdgeSet e).val = (B.mapEdgeSet d).val :=
      congrArg (fun t : (selectedGraph χ R).edgeSet => t.val) hselected
    obtain ⟨v, hv⟩ := original_piece_edge_has_vertex (A.mapEdgeSet e).val
    have hvA := original_piece_copy_edge_inside A hA e v hv
    have hvB := original_piece_copy_edge_inside B hB d v (hval ▸ hv)
    exact (Set.disjoint_left.mp hs) hvA hvB
  let lastA : Fin a := ⟨a - 1, by omega⟩
  let firstB : Fin b := ⟨0, by omega⟩
  have hne : A lastA ≠ B firstB := by
    intro heq
    have hBj : A lastA ∈ F.pieceSupport j := by
      rw [heq]
      exact hB ⟨firstB, rfl⟩
    exact (Set.disjoint_left.mp hs) (hA ⟨lastA, rfl⟩)
      hBj
  let join : HostEdge n :=
    ⟨s(A lastA, B firstB), (SimpleGraph.top_adj _ _).mpr hne⟩
  have hjoin : join.val = s(Ah ⟨a - 1, by omega⟩, Bh ⟨0, by omega⟩) := rfl
  have hfreshA : ∀ e : (pathGraph a).edgeSet,
      χ (Ah.toHom.mapEdgeSet e) ≠ χ join := by
    intro e
    exact originalCutFamily_cross_piece_color_fresh F i j hij join
      (A lastA) (B firstB) rfl (hA ⟨lastA, rfl⟩) (hB ⟨firstB, rfl⟩)
      (Ah.toHom.mapEdgeSet e) (A.mapEdgeSet e).property
      (Or.inl (original_piece_copy_edge_inside A hA e))
  have hfreshB : ∀ d : (pathGraph b).edgeSet,
      χ (Bh.toHom.mapEdgeSet d) ≠ χ join := by
    intro d
    exact originalCutFamily_cross_piece_color_fresh F i j hij join
      (A lastA) (B firstB) rfl (hA ⟨lastA, rfl⟩) (hB ⟨firstB, rfl⟩)
      (Bh.toHom.mapEdgeSet d) (B.mapEdgeSet d).property
      (Or.inr (original_piece_copy_edge_inside B hB d))
  exact ErdosProblems.PathHighNewStageOne.rainbow_path_of_original_disjoint_paths_and_fresh_join
    ha hb χ Ah Bh hAr hBr hdis hpal join hjoin hfreshA hfreshB

/-- An original no-rainbow condition at the SUM length excludes the two
actual positive piece paths. Restricting a longer joined path to length k is
a separate prefix-copy application; no numerical path upper is asserted. -/
theorem originalCutFamily_no_rainbow_sum_excludes_two_piece_paths
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots)
    (i j : F.PieceIndex) (hij : i ≠ j)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hno : ∀ P : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) :
    ¬ ∃ (A : (pathGraph a).Copy (originalCutFamilyGlobalRetainedGraph F))
      (B : (pathGraph b).Copy (originalCutFamilyGlobalRetainedGraph F)),
      (Set.range (fun u => A u) ⊆ F.pieceSupport i) ∧
      (Set.range (fun v => B v) ⊆ F.pieceSupport j) := by
  rintro ⟨A, B, hA, hB⟩
  obtain ⟨P, hP, _hPA, _hPB⟩ :=
    originalCutFamily_rainbow_path_of_two_piece_paths F i j hij ha hb A B hA hB
  exact hno P hP

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

def original_piece_path_prefix_copy {a b : ℕ} (hab : a ≤ b) :
    (pathGraph a).Copy (pathGraph b) where
  toHom :=
    { toFun := Fin.castLE hab
      map_rel' := by
        intro i j hij
        apply pathGraph_adj.mpr
        simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
  injective' := Fin.castLE_injective hab

theorem original_piece_rainbow_copy_comp
    {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (f : A.Copy B) (g : B.Copy (⊤ : SimpleGraph (Fin n)))
    (hg : IsRainbow g.toHom χ) :
    IsRainbow (g.comp f).toHom χ := by
  have hmap (e : A.edgeSet) :
      (g.comp f).toHom.mapEdgeSet e =
        g.toHom.mapEdgeSet (f.toHom.mapEdgeSet e) := by
    apply Subtype.ext
    simpa only [Copy.comp, Hom.mapEdgeSet, Hom.coe_comp] using
      (Sym2.map_map (f := f.toHom) (g := g.toHom) e.val).symm
  intro e d heq
  apply Hom.mapEdgeSet.injective f.toHom f.injective
  apply hg
  simpa only [EdgeLabeling.pullback_apply, hmap] using heq

/-- The original no-rainbow predicate forces the
combined VERTEX order of positive paths in any two different actual family
pieces to be strictly below k. The original connector and its two-path
freshness are derived by the prior actual-family theorem. No desired rainbow
copy, disjoint palette, freshness, or path-order conclusion is supplied. The prefix copy is valid for every natural k, including 0 and 1. -/
theorem originalCutFamily_two_piece_path_order_lt
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)} {k : ℕ}
    (F : OriginalResidualCutFamily χ R U W roots)
    (hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (i j : F.PieceIndex) (hij : i ≠ j)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (A : (pathGraph a).Copy (originalCutFamilyGlobalRetainedGraph F))
    (B : (pathGraph b).Copy (originalCutFamilyGlobalRetainedGraph F))
    (hA : Set.range (fun u => A u) ⊆ F.pieceSupport i)
    (hB : Set.range (fun u => B u) ⊆ F.pieceSupport j) :
    a + b < k := by
  by_contra hnot
  have hsum : k ≤ a + b := by omega
  obtain ⟨P, hP, _hleft, _hright⟩ :=
    originalCutFamily_rainbow_path_of_two_piece_paths F i j hij ha hb A B hA hB
  let f : (pathGraph k).Copy (pathGraph (a + b)) :=
    original_piece_path_prefix_copy hsum
  exact hno (P.comp f) (original_piece_rainbow_copy_comp χ f P hP)

end ErdosProblems.PathUpperReduction

end

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem uncut_tail_copy_edge_inside
    {a : ℕ} {G : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (P : (pathGraph a).Copy G) (hP : Set.range (fun u => P u) ⊆ X)
    (e : (pathGraph a).edgeSet) : EdgeInside X (P.mapEdgeSet e).val := by
  intro v hv
  change v ∈ Sym2.map P.toHom e.val at hv
  obtain ⟨u, _hu, huv⟩ := Sym2.mem_map.mp hv
  exact huv ▸ hP ⟨u, rfl⟩

def uncut_tail_path_prefix_copy {a b : ℕ} (hab : a ≤ b) :
    (pathGraph a).Copy (pathGraph b) where
  toHom :=
    { toFun := Fin.castLE hab
      map_rel' := by
        intro i j hij
        apply pathGraph_adj.mpr
        simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
  injective' := Fin.castLE_injective hab

theorem uncut_tail_rainbow_copy_comp
    {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (f : A.Copy B) (g : B.Copy (⊤ : SimpleGraph (Fin n)))
    (hg : IsRainbow g.toHom χ) :
    IsRainbow (g.comp f).toHom χ := by
  have hmap (e : A.edgeSet) :
      (g.comp f).toHom.mapEdgeSet e =
        g.toHom.mapEdgeSet (f.toHom.mapEdgeSet e) := by
    apply Subtype.ext
    simpa only [Copy.comp, Hom.mapEdgeSet, Hom.coe_comp] using
      (Sym2.map_map (f := f.toHom) (g := g.toHom) e.val).symm
  intro e d heq
  apply Hom.mapEdgeSet.injective f.toHom f.injective
  apply hg
  simpa only [EdgeLabeling.pullback_apply, hmap] using heq

/-- Join a positive retained-head path to a positive FULL-selected-graph tail
path. The actual tail contains all selected edges, including later cut owners.
The original host copy preserves both orders and has a+b vertices. -/
theorem OriginalResidualCutStage.uncut_tail_rainbow_path
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (P : (pathGraph a).Copy S.retainedGraph)
    (Q : (pathGraph b).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x) :
    ∃ F : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow F.toHom χ ∧
      (∀ u : Fin a, F (Fin.castAdd b u) = (P u).val) ∧
      (∀ v : Fin b, F (Fin.natAdd a v) = Q v) := by
  classical
  let Ps : (pathGraph a).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := fun u => (P u).val
          map_rel' := by
            intro u v huv
            exact (SimpleGraph.deleteEdges_adj.mp (P.toHom.map_rel' huv)).1 }
      injective' := by
        intro u v huv
        apply P.injective
        exact Subtype.ext huv }
  let Ph : (pathGraph a).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Ps
  let Qh : (pathGraph b).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Q
  have hPr : IsRainbow Ph.toHom χ := copy_in_selectedGraph_isRainbow χ R Ps
  have hQr : IsRainbow Qh.toHom χ := copy_in_selectedGraph_isRainbow χ R Q
  have hPX : Set.range (fun u => Ps u) ⊆ componentSupport χ R x := by
    rintro v ⟨u, rfl⟩
    exact (P u).property
  have hdis : Disjoint (Set.range fun u : Fin a => Ph u)
      (Set.range fun v : Fin b => Qh v) := by
    apply Set.disjoint_left.mpr
    intro v hvP hvQ
    exact (hQ hvQ).2 (hPX hvP)
  have hpal : ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      χ (Ph.toHom.mapEdgeSet e) ≠ χ (Qh.toHom.mapEdgeSet d) := by
    intro e d heq
    have hselected : Ps.mapEdgeSet e = Q.mapEdgeSet d := by
      apply selectedColor_injective χ R
      change χ (Ph.toHom.mapEdgeSet e) = χ (Qh.toHom.mapEdgeSet d)
      exact heq
    have hval : (Ps.mapEdgeSet e).val = (Q.mapEdgeSet d).val :=
      congrArg (fun z : (selectedGraph χ R).edgeSet => z.val) hselected
    let v := (Ps.mapEdgeSet e).val.out.1
    have hv : v ∈ (Ps.mapEdgeSet e).val := Sym2.out_fst_mem _
    have hvX := uncut_tail_copy_edge_inside Ps hPX e v hv
    have hvTail := uncut_tail_copy_edge_inside Q hQ d v (hval ▸ hv)
    exact hvTail.2 hvX
  let lastP : Fin a := ⟨a - 1, by omega⟩
  let firstQ : Fin b := ⟨0, by omega⟩
  have hlast : (P lastP).val ∈ componentSupport χ R x := (P lastP).property
  have hfirst : Q firstQ ∈ W \ componentSupport χ R x := hQ ⟨firstQ, rfl⟩
  have hne : (P lastP).val ≠ Q firstQ := by
    intro heq
    apply hfirst.2
    rw [← heq]
    exact hlast
  let join : HostEdge n :=
    ⟨s((P lastP).val, Q firstQ), (SimpleGraph.top_adj _ _).mpr hne⟩
  have hjoin : join.val = s(Ph ⟨a - 1, by omega⟩, Qh ⟨0, by omega⟩) := rfl
  have hcover : χ join ∈ U ∨ χ join ∈ S.A.image (fun c => c.val) := by
    have h := S.payload
    rcases h with ⟨_, _, _, _, _, _, hout, _⟩
    rcases hout join (P lastP).val (Q firstQ) rfl hlast hfirst.1 hfirst.2 with
      hU | ⟨hc, hcA⟩
    · exact Or.inl hU
    · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ join, hc⟩, hcA, rfl⟩)
  have hfreshP : ∀ e : (pathGraph a).edgeSet,
      χ (Ph.toHom.mapEdgeSet e) ≠ χ join := by
    intro e
    obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.val
    change s(u, v) = e.val at huv
    have hadj : (pathGraph a).Adj u v := by
      have he := e.property
      rwa [← huv] at he
    have hval : (Ph.toHom.mapEdgeSet e).val = s((P u).val, (P v).val) := by
      change Sym2.map (fun z : Fin a => (P z).val) e.val = _
      rw [← huv, Sym2.map_mk]
    have hBset : (S.B : Set (Sym2 (componentSupport χ R x))) =
        OriginalResidualColorDeletion χ R U (componentSupport χ R x) (S.A : Set _) := by
      have h := S.payload
      rcases h with ⟨_, hBset, _⟩
      exact hBset
    have havoid := original_retained_edge_color_outside_removed_and_cut
      χ R U W S.partition (componentSupport χ R x) S.support_subset S.A S.B hBset
      (P u) (P v) (P.toHom.map_rel' hadj) (Ph.toHom.mapEdgeSet e) hval
    intro heq
    rcases hcover with hU | hA
    · apply havoid.1
      rw [heq]
      exact hU
    · apply havoid.2
      rw [heq]
      exact hA
  have hfreshQ : ∀ d : (pathGraph b).edgeSet,
      χ (Qh.toHom.mapEdgeSet d) ≠ χ join := by
    intro d
    have havoid := original_later_selected_edge_color_outside_removed_and_cut
      χ R U W S.partition x S.support_subset S.maximum S.A
      (Qh.toHom.mapEdgeSet d) (Q.mapEdgeSet d).property
      (uncut_tail_copy_edge_inside Q hQ d)
    intro heq
    rcases hcover with hU | hA
    · apply havoid.1
      rw [heq]
      exact hU
    · apply havoid.2
      rw [heq]
      exact hA
  exact ErdosProblems.PathHighNewStageOne.rainbow_path_of_original_disjoint_paths_and_fresh_join
    ha hb χ Ph Qh hPr hQr hdis hpal join hjoin hfreshP hfreshQ

/-- Original noRainbow(Pk) limits a retained head path plus an UNCUT full-G
tail path. No positivity or host-size premise beyond the two supplied paths
is silently added; truncation works for arbitrary natural k. -/
theorem OriginalResidualCutStage.uncut_tail_path_order_lt
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (P : (pathGraph a).Copy S.retainedGraph)
    (Q : (pathGraph b).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x) :
    a + b < k := by
  by_contra hnot
  have hsum : k ≤ a + b := by omega
  obtain ⟨F, hF, _hleft, _hright⟩ := S.uncut_tail_rainbow_path ha hb P Q hQ
  let prefCopy : (pathGraph k).Copy (pathGraph (a + b)) := uncut_tail_path_prefix_copy hsum
  exact hno (F.comp prefCopy) (uncut_tail_rainbow_copy_comp χ prefCopy F hF)

/-- A retained head path on k-2 vertices forces the FULL selected graph on
the remaining W minus WHOLE X to be edgeless, before any later cuts. It does
not imply that the processed prefix is proper or that G is connected. -/
theorem OriginalResidualCutStage.uncut_tail_edgeless_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ) :
    (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥ := by
  classical
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have hne : u.val ≠ v.val := (selectedGraph χ R).ne_of_adj huv
  let f : Fin 2 → Fin n := fun i => if i = 0 then u.val else v.val
  let Q : (pathGraph 2).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := f
          map_rel' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · have h := pathGraph_adj.mp hij
              omega
            · simpa [f] using huv
            · simpa [f] using huv.symm
            · have h := pathGraph_adj.mp hij
              omega }
      injective' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hne (by simpa [f] using hij))
        · exact False.elim (hne (by simpa [f] using hij.symm))
        · rfl }
  have hQ : Set.range (fun i => Q i) ⊆ W \ componentSupport χ R x := by
    rintro z ⟨i, rfl⟩
    change (if i = 0 then u.val else v.val) ∈ W \ componentSupport χ R x
    by_cases hi : i = 0
    · rw [ite_eq_left hi]
      exact u.property
    · rw [ite_eq_right hi]
      exact v.property
  have hlt := S.uncut_tail_path_order_lt hno (a := k - 2) (b := 2)
    (by omega) (by omega) P Q hQ
  omega

end ErdosProblems.PathUpperReduction

section

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n m q : ℕ}

/-- The original complete-host coloring pulled through a vertex embedding.
The color type remains literally Fin q. -/
def originalPrefixRestrictedColoring
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (i : Fin m ↪ Fin n) :
    TopEdgeLabeling (Fin m) (Fin q) :=
  EdgeLabeling.pullback χ (SimpleGraph.Embedding.completeGraph i).toHom

/-- If all ORIGINAL representative owners lie in the
embedding range, this restricted coloring still uses EVERY original color. -/
theorem originalPrefixRestrictedColoring_surjective
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (i : Fin m ↪ Fin n)
    (howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val) :
    Function.Surjective (originalPrefixRestrictedColoring χ i) := by
  intro c
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective (R.edge c).val
  have huOwner : u ∈ (R.edge c).val := by
    rw [← huv]
    exact Sym2.mem_mk_left u v
  have hvOwner : v ∈ (R.edge c).val := by
    rw [← huv]
    exact Sym2.mem_mk_right u v
  obtain ⟨u', hu'⟩ := howners c u huOwner
  obtain ⟨v', hv'⟩ := howners c v hvOwner
  have huvNe : u ≠ v := by
    have htop : (⊤ : SimpleGraph (Fin n)).Adj u v := by
      have he := (R.edge c).property
      rw [← huv] at he
      exact he
    exact (SimpleGraph.top_adj u v).mp htop
  have hpreNe : u' ≠ v' := by
    intro h
    exact huvNe (hu'.symm.trans ((congrArg i h).trans hv'))
  let e : HostEdge m := ⟨s(u', v'), (SimpleGraph.top_adj u' v').mpr hpreNe⟩
  have hmap : (SimpleGraph.Embedding.completeGraph i).toHom.mapEdgeSet e =
      R.edge c := by
    apply Subtype.ext
    change Sym2.map i s(u', v') = (R.edge c).val
    rw [Sym2.map_mk, hu', hv']
    exact huv
  refine ⟨e, ?_⟩
  change χ ((SimpleGraph.Embedding.completeGraph i).toHom.mapEdgeSet e) = c
  rw [hmap]
  exact R.color_eq c

/-- A rainbow ordinary copy for the restricted original
coloring would compose with the complete-host embedding into the SAME original
coloring. No induced-copy or connectedness hypothesis is needed. -/
theorem originalPrefixRestrictedColoring_noRainbowCopy
    {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (i : Fin m ↪ Fin n)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬ IsRainbow f.toHom (originalPrefixRestrictedColoring χ i) := by
  intro f hr
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    ((SimpleGraph.Embedding.completeGraph i).toCopy).comp f
  apply hno g
  intro e₁ e₂ heq
  apply hr
  have hcolor (e : H.edgeSet) :
      (EdgeLabeling.pullback χ g.toHom) e =
        (EdgeLabeling.pullback (originalPrefixRestrictedColoring χ i) f.toHom) e := by
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (g : α → Fin n) e.val =
      Sym2.map i (Sym2.map (f : α → Fin m) e.val)
    rw [Sym2.map_map]
    congr 1
  rw [hcolor e₁, hcolor e₂] at heq
  exact heq

/-- The direct literal bounded sSup witness. No reduced
image palette or unbounded-supremum shortcut is used. -/
theorem original_surjective_noRainbow_color_count_le_antiRamseyNum
    {α : Type*} [Fintype α] (H : SimpleGraph α)
    (φ : TopEdgeLabeling (Fin m) (Fin q)) (hφ : Function.Surjective φ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬ IsRainbow f.toHom φ) :
    q ≤ antiRamseyNum H m := by
  classical
  let A : Set ℕ :=
    {p | ∃ ψ : TopEdgeLabeling (Fin m) (Fin p), Function.Surjective ψ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬ IsRainbow f.toHom ψ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin m)).edgeSet), ?_⟩
    intro p hp
    obtain ⟨ψ, hψ, _⟩ := hp
    simpa using Fintype.card_le_of_surjective ψ hψ
  have hmem : q ∈ A := ⟨φ, hφ, hno⟩
  change q ≤ sSup A
  exact le_csSup hbounded hmem

/-- Original owner confinement supplies the same full
Fin-q restricted coloring, its no-rainbow predicate, and the numeric witness. -/
theorem originalPrefixRestrictedColoring_full_witness
    {α : Type*} [Fintype α] (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (i : Fin m ↪ Fin n)
    (howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ) :
    Function.Surjective (originalPrefixRestrictedColoring χ i) ∧
    (∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬ IsRainbow f.toHom (originalPrefixRestrictedColoring χ i)) ∧
    q ≤ antiRamseyNum H m := by
  have hsurj := originalPrefixRestrictedColoring_surjective χ R i howners
  have hrestricted := originalPrefixRestrictedColoring_noRainbowCopy H χ i hno
  exact ⟨hsurj, hrestricted,
    original_surjective_noRainbow_color_count_le_antiRamseyNum
      H (originalPrefixRestrictedColoring χ i) hsurj hrestricted⟩

/-- At an ACTUAL stage with FULL uncut tail edgeless,
restriction to its whole processed prefix retains ALL original colors and
gives q ≤ antiRamseyNum(Pk,m). No properness or k ≤ m is asserted. -/
theorem OriginalResidualCutStage.processed_prefix_color_count_le
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (i : Fin m ↪ Fin n)
    (hrange : Set.range i = Wᶜ ∪ componentSupport χ R x)
    (hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    q ≤ antiRamseyNum (pathGraph k) m := by
  have howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val := by
    intro c
    rw [hrange]
    exact S.owner_inside_processed_prefix htail c
  exact (originalPrefixRestrictedColoring_full_witness
    (pathGraph k) χ R i howners hno).2.2

/-- The retained order k-2 endpoint derives FULL-tail
edgelessness internally, then supplies the same original full-palette
anti-Ramsey witness on the processed prefix. -/
theorem OriginalResidualCutStage.processed_prefix_color_count_le_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (i : Fin m ↪ Fin n)
    (hrange : Set.range i = Wᶜ ∪ componentSupport χ R x) :
    q ≤ antiRamseyNum (pathGraph k) m :=
  S.processed_prefix_color_count_le
    (S.uncut_tail_edgeless_of_retained_path_order hk P hno) i hrange hno

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

def last_leaf_two_vertex_copy (G : SimpleGraph (Fin n))
    (ell h : Fin n) (hadj : G.Adj ell h) : (pathGraph 2).Copy G := by
  let f : Fin 2 → Fin n := fun i => if i = 0 then ell else h
  refine { toHom := { toFun := f, map_rel' := ?_ }, injective' := ?_ }
  · intro i j hij
    fin_cases i <;> fin_cases j
    · have h := pathGraph_adj.mp hij
      omega
    · simpa [f] using hadj
    · simpa [f] using hadj.symm
    · have h := pathGraph_adj.mp hij
      omega
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (G.ne_of_adj hadj (by simpa [f] using hij))
    · exact False.elim (G.ne_of_adj hadj (by simpa [f] using hij.symm))
    · rfl

theorem last_leaf_two_edge_value (d : (pathGraph 2).edgeSet) :
    d.val = s((0 : Fin 2), (1 : Fin 2)) := by
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective d.val
  change s(u, v) = d.val at huv
  have hadj : (pathGraph 2).Adj u v := by
    have hd := d.property
    rwa [← huv] at hd
  have hu := u.isLt
  have hv := v.isLt
  rcases pathGraph_adj.mp hadj with h | h
  · have hu0 : u = 0 := Fin.ext (by omega)
    have hv1 : v = 1 := Fin.ext (by omega)
    rw [← huv, hu0, hv1]
  · have hu1 : u = 1 := Fin.ext (by omega)
    have hv0 : v = 0 := Fin.ext (by omega)
    rw [← huv, hu1, hv0]
    exact Sym2.eq_swap

theorem last_leaf_path_edge_inside
    {a : ℕ} {G : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (P : (pathGraph a).Copy G) (hP : Set.range (fun u => P u) ⊆ X)
    (e : (pathGraph a).edgeSet) : EdgeInside X (P.mapEdgeSet e).val := by
  intro v hv
  change v ∈ Sym2.map P.toHom e.val at hv
  obtain ⟨u, _hu, huv⟩ := Sym2.mem_map.mp hv
  exact huv ▸ hP ⟨u, rfl⟩

/-- The literal connector from ANY selected inside edge to an uncut tail
path of order k-2 must have that selected edge's original color. Head leaf
uniqueness and NEW are not assumed for this implication. -/
theorem OriginalResidualCutStage.last_leaf_connector_color_eq
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow F.toHom χ)
    (ell h : Fin n) (head : HostEdge n)
    (hhead : head.val ∈ (selectedGraph χ R).edgeSet)
    (hheadval : head.val = s(ell, h))
    (hellX : ell ∈ componentSupport χ R x) (hhX : h ∈ componentSupport χ R x)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x)
    (join : HostEdge n) (hjoinval : join.val = s(h, Q ⟨0, by omega⟩)) :
    χ join = χ head := by
  classical
  by_contra hneq
  have hadj : (selectedGraph χ R).Adj ell h := by
    rw [hheadval] at hhead
    exact hhead
  let P := last_leaf_two_vertex_copy (selectedGraph χ R) ell h hadj
  let Ph : (pathGraph 2).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp P
  let Qh : (pathGraph (k - 2)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Q
  have hPX : Set.range (fun u => P u) ⊆ componentSupport χ R x := by
    rintro z ⟨u, rfl⟩
    change (if u = 0 then ell else h) ∈ componentSupport χ R x
    by_cases hu : u = 0
    · rw [ite_eq_left hu]
      exact hellX
    · rw [ite_eq_right hu]
      exact hhX
  have hdis : Disjoint (Set.range fun u : Fin 2 => Ph u)
      (Set.range fun v : Fin (k - 2) => Qh v) := by
    apply Set.disjoint_left.mpr
    intro v hvP hvQ
    exact (hQ hvQ).2 (hPX hvP)
  have hpal : ∀ d : (pathGraph 2).edgeSet, ∀ e : (pathGraph (k - 2)).edgeSet,
      χ (Ph.toHom.mapEdgeSet d) ≠ χ (Qh.toHom.mapEdgeSet e) := by
    intro d e heq
    have hselected : P.mapEdgeSet d = Q.mapEdgeSet e := by
      apply selectedColor_injective χ R
      change χ (Ph.toHom.mapEdgeSet d) = χ (Qh.toHom.mapEdgeSet e)
      exact heq
    have hval := congrArg (fun z : (selectedGraph χ R).edgeSet => z.val) hselected
    let v := (P.mapEdgeSet d).val.out.1
    have hv : v ∈ (P.mapEdgeSet d).val := Sym2.out_fst_mem _
    have hvX := last_leaf_path_edge_inside P hPX d v hv
    have hvQ := last_leaf_path_edge_inside Q hQ e v (hval ▸ hv)
    exact hvQ.2 hvX
  have hfreshP : ∀ d : (pathGraph 2).edgeSet,
      χ (Ph.toHom.mapEdgeSet d) ≠ χ join := by
    intro d
    have hhost : Ph.toHom.mapEdgeSet d = head := by
      apply Subtype.ext
      change Sym2.map Ph.toHom d.val = head.val
      rw [last_leaf_two_edge_value d, Sym2.map_mk]
      exact hheadval.symm
    rw [hhost]
    exact Ne.symm hneq
  have hcover : χ join ∈ U ∨ χ join ∈ S.A.image (fun c => c.val) := by
    have hdata := S.payload
    rcases hdata with ⟨_, _, _, _, _, _, hout, _⟩
    have hfirst := hQ ⟨(⟨0, by omega⟩ : Fin (k - 2)), rfl⟩
    rcases hout join h (Q ⟨0, by omega⟩) hjoinval hhX hfirst.1 hfirst.2 with
      hU | ⟨hc, hcA⟩
    · exact Or.inl hU
    · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ join, hc⟩, hcA, rfl⟩)
  have hfreshQ : ∀ e : (pathGraph (k - 2)).edgeSet,
      χ (Qh.toHom.mapEdgeSet e) ≠ χ join := by
    intro e
    have havoid := original_later_selected_edge_color_outside_removed_and_cut
      χ R U W S.partition x S.support_subset S.maximum S.A
      (Qh.toHom.mapEdgeSet e) (Q.mapEdgeSet e).property
      (last_leaf_path_edge_inside Q hQ e)
    intro heq
    rcases hcover with hU | hA
    · apply havoid.1
      rw [heq]
      exact hU
    · apply havoid.2
      rw [heq]
      exact hA
  have hjoin : join.val = s(Ph ⟨2 - 1, by omega⟩, Qh ⟨0, by omega⟩) := by
    change join.val = s(h, Q ⟨0, by omega⟩)
    exact hjoinval
  obtain ⟨F, hF, _hleft, _hright⟩ :=
    ErdosProblems.PathHighNewStageOne.rainbow_path_of_original_disjoint_paths_and_fresh_join
      (by omega) (by omega) χ Ph Qh (copy_in_selectedGraph_isRainbow χ R P)
      (copy_in_selectedGraph_isRainbow χ R Q) hdis hpal join hjoin hfreshP hfreshQ
  have hlen : 2 + (k - 2) = k := by omega
  have hbad : ∃ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow F.toHom χ := by
    exact Eq.mp
      (congrArg (fun t : ℕ => ∃ F : (pathGraph t).Copy (⊤ : SimpleGraph (Fin n)),
        IsRainbow F.toHom χ) hlen) ⟨F, hF⟩
  obtain ⟨F', hF'⟩ := hbad
  exact hno F' hF'

/-- The ordinary selected-neighbor uniqueness premise implies the exact
owner-color leaf premise. It makes no original NEW-color assertion. -/
theorem original_owner_color_of_unique_selected_neighbor
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (ell h : Fin n) (head : HostEdge n) (hheadval : head.val = s(ell, h))
    (hleaf : ∀ v : Fin n, (selectedGraph χ R).Adj ell v → v = h) :
    ∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head := by
  intro c hc
  obtain ⟨v, howner⟩ := Sym2.mem_iff_exists.mp hc
  have heG : (R.edge c).val ∈ (selectedGraph χ R).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, rfl⟩
  have hadj : (selectedGraph χ R).Adj ell v := by
    rw [howner] at heG
    exact heG
  have hv : v = h := hleaf v hadj
  have heq : R.edge c = head := by
    apply Subtype.ext
    rw [howner, hv]
    exact hheadval.symm
  exact (R.color_eq c).symm.trans (congrArg χ heq)

/-- Exact owner-leaf uniqueness is sufficient to remove every selected owner
from ell after replacing alpha with another original alpha edge avoiding ell. -/
theorem original_replace_avoids_selected_leaf
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (ell : Fin n) (head join : HostEdge n)
    (hleaf : ∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head)
    (hcolor : χ join = χ head) (havoid : ell ∉ join.val) :
    ∀ c : Fin q, ell ∉ ((R.replace join).edge c).val := by
  intro c
  by_cases hc : c = χ join
  · subst c
    rw [R.replace_edge_same join]
    exact havoid
  · rw [R.replace_edge_other join hc]
    intro hmem
    exact hc ((hleaf c hmem).trans hcolor.symm)

/-- A selected leaf inside an earlier WHOLE component can be omitted from
the host while retaining ALL q original colors, provided the literal uncut
outside path has k-2 vertices. The bound is antiRamseyNum on the m-vertex
restriction, not an assumed numerical formula or induction hypothesis. -/
theorem OriginalResidualCutStage.last_leaf_color_count_le
    {m : ℕ} {χ : TopEdgeLabeling (Fin (m + 1)) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin (m + 1))} {x : Fin (m + 1)} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin (m + 1))), ¬ IsRainbow F.toHom χ)
    (ell h : Fin (m + 1)) (head : HostEdge (m + 1))
    (hhead : head.val ∈ (selectedGraph χ R).edgeSet)
    (hheadval : head.val = s(ell, h))
    (hellX : ell ∈ componentSupport χ R x) (hhX : h ∈ componentSupport χ R x)
    (hleaf : ∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x)
    (join : HostEdge (m + 1)) (hjoinval : join.val = s(h, Q ⟨0, by omega⟩)) :
    q ≤ antiRamseyNum (pathGraph k) m := by
  have hcolor := S.last_leaf_connector_color_eq hk hno ell h head hhead hheadval
    hellX hhX Q hQ join hjoinval
  have hadj : (selectedGraph χ R).Adj ell h := by
    rw [hheadval] at hhead
    exact hhead
  have havoid : ell ∉ join.val := by
    intro hmem
    rw [hjoinval] at hmem
    rcases Sym2.mem_iff.mp hmem with heqh | heqQ
    · exact (selectedGraph χ R).ne_of_adj hadj heqh
    · have hfirst := hQ ⟨(⟨0, by omega⟩ : Fin (k - 2)), rfl⟩
      apply hfirst.2
      exact heqQ ▸ hellX
  have hav := original_replace_avoids_selected_leaf χ R ell head join hleaf hcolor havoid
  let i : Fin m ↪ Fin (m + 1) := ⟨ell.succAbove, Fin.succAbove_right_injective⟩
  have hrange : Set.range i = {ell}ᶜ := Fin.range_succAbove ell
  have howners : ∀ c : Fin q, EdgeInside (Set.range i) ((R.replace join).edge c).val := by
    intro c v hv
    rw [hrange]
    have hvne : v ≠ ell := by
      intro hveq
      subst v
      exact hav c hv
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvne
  exact (originalPrefixRestrictedColoring_full_witness
    (pathGraph k) χ (R.replace join) i howners hno).2.2

end ErdosProblems.PathUpperReduction

end

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

theorem choose_two_positive_cap
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    s.choose 2 + t.choose 2 ≤ (s + t - 1).choose 2 := by
  let x := s - 1
  let y := t - 1
  have hsx : s = x + 1 := by dsimp [x]; omega
  have hty : t = y + 1 := by dsimp [y]; omega
  have hshift : s + t - 1 = x + y + 1 := by omega
  have hx : (x + 1) * x = (x + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq x 1
  have hy : (y + 1) * y = (y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq y 1
  have hxy : (x + y + 1) * (x + y) = (x + y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq (x + y) 1
  rw [hshift, hsx, hty]
  nlinarith [Nat.zero_le (x * y)]

/-- A finite graph containing an ACTUAL bridge has at
most choose(m-1,2)+1 edges. Connectedness is not assumed; isolates are retained. -/
theorem edge_card_le_choose_pred_of_actual_bridge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V) (hf : f ∈ G.edgeSet) (hbridge : G.IsBridge f) :
    G.edgeFinset.card ≤ (Fintype.card V - 1).choose 2 + 1 := by
  classical
  revert hf hbridge
  refine Sym2.inductionOn f ?_
  intro a b hf hbridge
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 V))
  have hsep : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  let S : Finset V := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset V := Finset.univ \ S
  have hS (x : V) : x ∈ S ↔ D.Reachable a x := by simp [S]
  have hT (x : V) : x ∈ T ↔ x ∉ S := by simp [T]
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hparts : S ∪ T = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsum : S.card + T.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hST, hparts, Finset.card_univ]
  have hSpos : 0 < S.card :=
    Finset.card_pos.mpr ⟨a, (hS a).mpr (SimpleGraph.Reachable.refl _)⟩
  have hTpos : 0 < T.card := Finset.card_pos.mpr
    ⟨b, (hT b).mpr (fun hb => hsep ((hS b).mp hb))⟩
  have hSclosed : ∀ {x y : V}, D.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    exact (hS y).mpr (((hS x).mp hx).trans hxy.reachable)
  have hTclosed : ∀ {x y : V}, D.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    apply (hT y).mpr
    intro hy
    exact ((hT x).mp hx) (hSclosed hxy.symm hy)
  let ES := D.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := D.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  have hcover : D.edgeFinset ⊆ ES ∪ ET := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : D.Adj x y := D.mem_edgeSet.mp (D.mem_edgeFinset.mp he)
    by_cases hxS : x ∈ S
    · have hsub : s(x, y).toFinset ⊆ S := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxS (hSclosed hxy hxS)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hsub⟩))
    · have hxT : x ∈ T := (hT x).mpr hxS
      have hsub : s(x, y).toFinset ⊆ T := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxT (hTclosed hxy hxT)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))
  have hES : ES.card ≤ S.card.choose 2 := by
    calc
      ES.card = (D.induce (↑S : Set V)).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) S
      _ ≤ (Fintype.card S).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑S : Set V))
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hET : ET.card ≤ T.card.choose 2 := by
    calc
      ET.card = (D.induce (↑T : Set V)).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) T
      _ ≤ (Fintype.card T).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑T : Set V))
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hDcap : D.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 := by
    calc
      D.edgeFinset.card ≤ (ES ∪ ET).card := Finset.card_le_card hcover
      _ ≤ ES.card + ET.card := Finset.card_union_le ES ET
      _ ≤ S.card.choose 2 + T.card.choose 2 := Nat.add_le_add hES hET
  have hchoose : S.card.choose 2 + T.card.choose 2 ≤
      (Fintype.card V - 1).choose 2 := by
    simpa only [hsum] using choose_two_positive_cap S.card T.card hSpos hTpos
  have hdelete : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, Finset.coe_erase, D,
      SimpleGraph.edgeSet_deleteEdges]
  have hedge : D.edgeFinset.card + 1 = G.edgeFinset.card := by
    rw [hdelete]
    exact Finset.card_erase_add_one (G.mem_edgeFinset.mpr hf)
  omega

variable {n q : ℕ}

/-- All original owners inside X and a genuine bridge
of the literal induced selected graph give the ORIGINAL q-color bound. -/
theorem original_palette_le_choose_pred_of_inside_actual_bridge
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (X : Set (Fin n))
    (howners : ∀ c : Fin q, EdgeInside X (R.edge c).val)
    (f : Sym2 X) (hf : f ∈ ((selectedGraph χ R).induce X).edgeSet)
    (hbridge : ((selectedGraph χ R).induce X).IsBridge f) :
    q ≤ (Nat.card X - 1).choose 2 + 1 := by
  classical
  let G := selectedGraph χ R
  have hsupport : G.support ⊆ X := by
    intro v hv
    obtain ⟨w, hvw⟩ := (SimpleGraph.mem_support G).mp hv
    have hmem : s(v, w) ∈ (selectedGraph χ R).edgeSet := hvw
    rw [selectedGraph_edgeSet] at hmem
    obtain ⟨c, hc⟩ := hmem
    change (R.edge c).val = s(v, w) at hc
    apply howners c v
    rw [hc]
    exact Sym2.mem_mk_left v w
  have hcount : (G.induce X).edgeFinset.card = q := by
    have hinduce := G.card_edgeFinset_induce_of_support_subset hsupport
    have horiginal := selectedGraph_card_edgeFinset χ R
    simp only [SimpleGraph.edgeFinset_card, Fintype.card_eq_nat_card, G] at hinduce horiginal ⊢
    exact hinduce.trans horiginal
  have hcap := edge_card_le_choose_pred_of_actual_bridge (G.induce X) f hf hbridge
  rw [hcount] at hcap
  simpa only [Fintype.card_eq_nat_card] using hcap

/-- A high ORIGINAL palette excludes every too-small
whole head once confinement and an ACTUAL inside bridge have been derived. -/
theorem original_head_order_ge_of_high_palette_and_actual_bridge
    {k : ℕ} (hk : 2 ≤ k)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (X : Set (Fin n))
    (howners : ∀ c : Fin q, EdgeInside X (R.edge c).val)
    (f : Sym2 X) (hf : f ∈ ((selectedGraph χ R).induce X).edgeSet)
    (hbridge : ((selectedGraph χ R).induce X).IsBridge f)
    (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card X := by
  have hcap := original_palette_le_choose_pred_of_inside_actual_bridge
    χ R X howners f hf hbridge
  by_contra hnot
  have hsize : Nat.card X - 1 ≤ k - 2 := by omega
  have hchoose := Nat.choose_le_choose 2 hsize
  omega

/-- A proper FIRST actual stage has an original eligible
outside connector; its certificate then supplies a genuine inside bridge. Full-tail edgelessness confines ALL q owners to this whole head, so high q
forces its order at least k. No nonempty cut or numerical cap is a premise. -/
theorem OriginalResidualCutStage.first_head_order_ge_of_high_palette
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ)
    (htail : (selectedGraph χ R).induce
      (Set.univ \ componentSupport χ R x) = ⊥)
    (hk : 2 ≤ k) (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card (componentSupport χ R x) := by
  classical
  have hx : x ∈ componentSupport χ R x :=
    (mem_componentSupport χ R x x).mpr (SimpleGraph.Reachable.refl _)
  have hyexists : ∃ y : Fin n, y ∉ componentSupport χ R x := by
    by_contra h
    apply hproper
    apply Set.eq_univ_of_forall
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hyexists
  have hxy : x ≠ y := by
    intro h
    exact hy (h ▸ hx)
  let e : HostEdge n := ⟨s(x, y), (SimpleGraph.top_adj x y).mpr hxy⟩
  have hout : EligibleResidualOutgoing χ ∅ Set.univ (componentSupport χ R x) :=
    ⟨e, x, y, rfl, hx, Set.mem_univ y, hy, by simp⟩
  have hdata := S.payload
  rcases hdata with ⟨_, _, hBselected, hBbridges, _, _, _, _, _, houtne, _⟩
  obtain ⟨f, hf⟩ := houtne hout
  have howners : ∀ c : Fin q, EdgeInside (componentSupport χ R x) (R.edge c).val := by
    intro c
    simpa only [Set.compl_univ, Set.empty_union] using
      S.owner_inside_processed_prefix htail c
  exact original_head_order_ge_of_high_palette_and_actual_bridge
    hk χ R (componentSupport χ R x) howners f (hBselected hf) (hBbridges f hf) hq

/-- At a proper first retained order k-2 endpoint,
derive the full-tail condition internally and obtain the FULL induction lower
domain k ≤ m. Properness of the head remains explicit and implies m < n only
through a separate cardinality/embedding application. -/
theorem OriginalResidualCutStage.first_head_order_ge_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow F.toHom χ)
    (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card (componentSupport χ R x) :=
  S.first_head_order_ge_of_high_palette hproper
    (S.uncut_tail_edgeless_of_retained_path_order hk P hno) (by omega) hq

/-- A proper first retained order k-2 endpoint supplies
both literal FULL smaller-host induction domain bounds. The head carries all
original colors; no reduction of the palette or supplied size bound is used. -/
theorem OriginalResidualCutStage.first_head_full_induction_domain_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow F.toHom χ)
    (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card (componentSupport χ R x) ∧
      Nat.card (componentSupport χ R x) < n := by
  refine ⟨S.first_head_order_ge_of_retained_path_order hproper hk P hno hq, ?_⟩
  simpa only [← Nat.card_coe_set_eq, Nat.card_fin] using
    Set.ncard_lt_card hproper

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The admissible identity choice preserves ALL original slots. -/
theorem OriginalResidualCutStage.component_size_ge_of_mem_residual
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (y : Fin n) (hy : y ∈ W) :
    (componentSupport χ R y).ncard ≤ S.rootSupport.ncard := by
  let identityChoice : OriginalResidualChoice χ R U W :=
    { choice := R
      prefix_eq := by
        intro _ _
        rfl
      eligible_inside := S.partition.eligible_inside }
  simpa only [identityChoice, OriginalResidualCutStage.rootSupport] using
    S.maximum.1 identityChoice y hy

/-- Every later WHOLE selected component lies in this stage's literal uncut
tail, from the actual greedy sequence's unchanged whole-prefix recursion. -/
theorem OriginalResidualCutStage.later_component_support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin n} (hy : y ∈ xs) :
    componentSupport χ R y ⊆ W \ S.rootSupport := by
  have htail := hsequence.2.2.2
  have hcover := residualGreedySequence_covers χ R
    (U ∪ residualSelectedComponentColors χ R x)
    (W \ componentSupport χ R x) xs htail
  intro v hv
  exact (hcover v).mpr ⟨y, hy, hv⟩

/-- Actual later whole-component sizes are nonincreasing; no manufactured
ordering or desired component-size premise is supplied. -/
theorem OriginalResidualCutStage.later_component_size_le
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin n} (hy : y ∈ xs) :
    (componentSupport χ R y).ncard ≤ S.rootSupport.ncard := by
  have hyY : y ∈ componentSupport χ R y :=
    (mem_componentSupport χ R y y).mpr (SimpleGraph.Reachable.refl y)
  have hyW : y ∈ W := (S.later_component_support_subset hsequence hy hyY).1
  exact S.component_size_ge_of_mem_residual y hyW

/-- A FULL selected uncut-tail P(k-2), together with original no-rainbow Pk,
forces the earlier retained graph to be edgeless. The full original chi/R and
arbitrary U/W remain unchanged. No earlier edgelessness or tree is assumed. -/
theorem OriginalResidualCutStage.retained_edgeless_of_uncut_tail_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ S.rootSupport) :
    S.retainedGraph = ⊥ := by
  classical
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have hne : u ≠ v := S.retainedGraph.ne_of_adj huv
  let f : Fin 2 → componentSupport χ R x := fun i => if i = 0 then u else v
  let P : (pathGraph 2).Copy S.retainedGraph :=
    { toHom :=
        { toFun := f
          map_rel' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · have h := pathGraph_adj.mp hij
              omega
            · simpa [f] using huv
            · simpa [f] using huv.symm
            · have h := pathGraph_adj.mp hij
              omega }
      injective' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hne (by simpa [f] using hij))
        · exact False.elim (hne (by simpa [f] using hij.symm))
        · rfl }
  have hlt := S.uncut_tail_path_order_lt hno (a := 2) (b := k - 2)
    (by omega) (by omega) P Q hQ
  omega

/-- Any actual later-stage retained long path already supplies the FULL
uncut-tail path needed to derive this earlier stage's retained edgelessness.
The later stage uses the SAME original full R; its own U/W are not reset. -/
theorem OriginalResidualCutStage.retained_edgeless_of_later_component_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin n} (hy : y ∈ xs)
    {V : Set (Fin q)} {Z : Set (Fin n)} {k : ℕ}
    (T : OriginalResidualCutStage χ R V Z y) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy T.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ) :
    S.retainedGraph = ⊥ := by
  let Q : (pathGraph (k - 2)).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := fun u => (P u).val
          map_rel' := by
            intro u v huv
            exact (SimpleGraph.deleteEdges_adj.mp (P.toHom.map_rel' huv)).1 }
      injective' := by
        intro u v huv
        apply P.injective
        exact Subtype.ext huv }
  have hQ : Set.range (fun v => Q v) ⊆ W \ S.rootSupport := by
    rintro z ⟨v, rfl⟩
    exact S.later_component_support_subset hsequence hy (P v).property
  exact S.retained_edgeless_of_uncut_tail_path_order hk hno Q hQ

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n m q k : ℕ}

/-- A leaf of an actual finite tree component has a unique neighbor in the
WHOLE host graph. Component closure excludes neighbors outside its support. -/
theorem exists_host_leaf_of_actual_component_tree
    (G : SimpleGraph (Fin n)) (C : G.ConnectedComponent)
    (hTree : C.toSimpleGraph.IsTree) (hcard : 2 ≤ C.supp.ncard) :
    ∃ ell h : Fin n, ell ∈ C.supp ∧ h ∈ C.supp ∧ G.Adj ell h ∧
      (∀ v : Fin n, G.Adj ell v → v = h) := by
  classical
  let : Fintype C := Fintype.ofFinite C
  have hcard' : 1 < Fintype.card C := by
    rw [Fintype.card_eq_nat_card]
    change 1 < Nat.card C.supp
    rw [Nat.card_coe_set_eq]
    omega
  let : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp hcard'
  obtain ⟨ell, hell⟩ := hTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨h, hadj, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hell
  refine ⟨ell.val, h.val, ell.property, h.property, hadj, ?_⟩
  intro v hv
  have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp ell.property hv
  have hv' : C.toSimpleGraph.Adj ell ⟨v, hvC⟩ := hv
  exact congrArg Subtype.val (hunique ⟨v, hvC⟩ hv')

/-- Actual edgeless retained stage means that EVERY selected edge in its
whole component is one of the actual bridge cuts; hence the whole induced
selected component is a tree. -/
theorem OriginalResidualCutStage.root_tree_of_retained_edgeless
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) (hD : S.retainedGraph = ⊥) :
    ((selectedGraph χ R).induce (componentSupport χ R x)).IsTree := by
  classical
  have hdata := S.payload
  dsimp [OriginalResidualCutStagePayload] at hdata
  have hbridge := hdata.2.2.2.1
  have hdelete :
      ((selectedGraph χ R).induce (componentSupport χ R x)).deleteEdges
        (S.B : Set (Sym2 (componentSupport χ R x))) = ⊥ := by
    simpa only [OriginalResidualCutStage.retainedGraph,
      OriginalResidualRetainedGraph] using hD
  have hall : ((selectedGraph χ R).induce (componentSupport χ R x)).edgeSet ⊆
      (S.B : Set (Sym2 (componentSupport χ R x))) :=
    deleteEdges_eq_bot.mp hdelete
  have hacyclic : ((selectedGraph χ R).induce (componentSupport χ R x)).IsAcyclic :=
    isAcyclic_iff_forall_isBridge.mpr (fun _ he => hbridge _ (hall he))
  have hconnected : ((selectedGraph χ R).induce (componentSupport χ R x)).Connected := by
    change ((selectedGraph χ R).connectedComponentMk x).toSimpleGraph.Connected
    exact ((selectedGraph χ R).connectedComponentMk x).connected_toSimpleGraph
  exact ⟨hconnected, hacyclic⟩

/-- The actual edgeless stage constructs a literal original selected head
edge and the owner-color confinement required by last-leaf restriction. -/
theorem OriginalResidualCutStage.exists_original_owner_leaf_of_retained_edgeless
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) (hD : S.retainedGraph = ⊥)
    (hcard : 2 ≤ (componentSupport χ R x).ncard) :
    ∃ (ell h : Fin n) (head : HostEdge n),
      ell ∈ componentSupport χ R x ∧ h ∈ componentSupport χ R x ∧
      head.val = s(ell, h) ∧ head.val ∈ (selectedGraph χ R).edgeSet ∧
      (∀ v : Fin n, (selectedGraph χ R).Adj ell v → v = h) ∧
      (∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head) := by
  classical
  let C := (selectedGraph χ R).connectedComponentMk x
  have hTree : C.toSimpleGraph.IsTree := S.root_tree_of_retained_edgeless hD
  obtain ⟨ell, h, hell, hh, hadj, hunique⟩ :=
    exists_host_leaf_of_actual_component_tree (selectedGraph χ R) C hTree hcard
  let head : HostEdge n := ⟨s(ell, h),
    (top_adj ell h).mpr ((selectedGraph χ R).ne_of_adj hadj)⟩
  have hhead : head.val ∈ (selectedGraph χ R).edgeSet := hadj
  refine ⟨ell, h, head, hell, hh, rfl, hhead, hunique, ?_⟩
  exact original_owner_color_of_unique_selected_neighbor χ R ell h head rfl hunique

/-- Two DISTINCT actual components each large enough for a (k-2)-vertex path
force the leaf-deleted host into the original induction regime k <= n-1. -/
theorem leaf_deleted_host_domain_of_two_actual_components
    (G : SimpleGraph (Fin n)) (C D : G.ConnectedComponent) (hCD : C ≠ D)
    (hk : 5 ≤ k) (hC : k - 2 ≤ C.supp.ncard) (hD : k - 2 ≤ D.supp.ncard) :
    k ≤ n - 1 := by
  have hdisjoint : Disjoint C.supp D.supp :=
    G.pairwise_disjoint_supp_connectedComponent hCD
  have hsum : C.supp.ncard + D.supp.ncard ≤ n := by
    have hbound := Set.ncard_le_card (C.supp ∪ D.supp)
    rw [Set.ncard_union_eq hdisjoint] at hbound
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hbound
  omega

theorem leaf_deleted_host_domain_of_two_selected_components
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (x y : Fin n)
    (hxy : (selectedGraph χ R).connectedComponentMk x ≠
      (selectedGraph χ R).connectedComponentMk y)
    (hk : 5 ≤ k)
    (hx : k - 2 ≤ (componentSupport χ R x).ncard)
    (hy : k - 2 ≤ (componentSupport χ R y).ncard) : k ≤ n - 1 :=
  leaf_deleted_host_domain_of_two_actual_components (selectedGraph χ R)
    ((selectedGraph χ R).connectedComponentMk x)
    ((selectedGraph χ R).connectedComponentMk y) hxy hk hx hy

/-- Full original last-leaf caller: the actual uncut long tail derives the
earlier tree and selected leaf, and the two actual component orders derive
the induction domain. The conclusion uses literal antiRamseyNum on Fin m;
its numerical inductive bound remains a separate application. -/
theorem OriginalResidualCutStage.last_leaf_restriction_with_domain
    {χ : TopEdgeLabeling (Fin (m + 1)) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin (m + 1))} {x : Fin (m + 1)}
    (S : OriginalResidualCutStage χ R U W x) (hk : 5 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬ IsRainbow F.toHom χ)
    (y : Fin (m + 1))
    (hxy : (selectedGraph χ R).connectedComponentMk x ≠
      (selectedGraph χ R).connectedComponentMk y)
    (hx : k - 2 ≤ (componentSupport χ R x).ncard)
    (hy : k - 2 ≤ (componentSupport χ R y).ncard)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x) :
    k ≤ m ∧ q ≤ antiRamseyNum (pathGraph k) m := by
  classical
  have hk3 : 3 ≤ k := by omega
  have hD : S.retainedGraph = ⊥ :=
    S.retained_edgeless_of_uncut_tail_path_order hk3 hno Q hQ
  have hcard : 2 ≤ (componentSupport χ R x).ncard := by omega
  obtain ⟨ell, h, head, hell, hh, hheadval, hhead, _hunique, howner⟩ :=
    S.exists_original_owner_leaf_of_retained_edgeless hD hcard
  let first : Fin (k - 2) := ⟨0, by omega⟩
  have hne : h ≠ Q first := by
    intro heq
    have ht := hQ ⟨first, rfl⟩
    apply ht.2
    exact Eq.mp (congrArg (fun z => z ∈ componentSupport χ R x) heq) hh
  let join : HostEdge (m + 1) := ⟨s(h, Q first), (top_adj h (Q first)).mpr hne⟩
  have hcount : q ≤ antiRamseyNum (pathGraph k) m :=
    S.last_leaf_color_count_le hk3 hno ell h head hhead hheadval hell hh
      howner Q hQ join rfl
  have hdomain := leaf_deleted_host_domain_of_two_selected_components
    χ R x y hxy hk hx hy
  exact ⟨by simpa only [Nat.add_sub_cancel] using hdomain, hcount⟩

/-- A later ACTUAL retained long path in the SAME-R greedy sequence derives
all domain and leaf premises for the earlier-stage restriction. No component
order, distinctness, acyclicity, leaf or favorable-color premise is supplied. -/
theorem OriginalResidualCutStage.last_leaf_restriction_of_later_retained_long_path
    {χ : TopEdgeLabeling (Fin (m + 1)) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin (m + 1))} {x : Fin (m + 1)}
    {xs : List (Fin (m + 1))}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin (m + 1)} (hy : y ∈ xs)
    {V : Set (Fin q)} {Z : Set (Fin (m + 1))}
    (T : OriginalResidualCutStage χ R V Z y) (hk : 5 ≤ k)
    (P : (pathGraph (k - 2)).Copy T.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬ IsRainbow F.toHom χ) :
    k ≤ m ∧ q ≤ antiRamseyNum (pathGraph k) m := by
  classical
  let Q : (pathGraph (k - 2)).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := fun u => (P u).val
          map_rel' := by
            intro u v huv
            exact (deleteEdges_adj.mp (P.toHom.map_rel' huv)).1 }
      injective' := by
        intro u v huv
        apply P.injective
        exact Subtype.ext huv }
  have hQY : Set.range (fun v => Q v) ⊆ componentSupport χ R y := by
    rintro z ⟨v, rfl⟩
    exact (P v).property
  have hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x :=
    hQY.trans (S.later_component_support_subset hsequence hy)
  have hY : k - 2 ≤ (componentSupport χ R y).ncard := by
    have hbound := Set.ncard_le_ncard hQY
    rw [Set.ncard_range_of_injective (f := fun v => Q v) Q.injective] at hbound
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hbound
  have hX : k - 2 ≤ (componentSupport χ R x).ncard :=
    hY.trans (S.later_component_size_le hsequence hy)
  have hyY : y ∈ componentSupport χ R y :=
    (mem_componentSupport χ R y y).mpr (SimpleGraph.Reachable.refl y)
  have hyNotX : y ∉ componentSupport χ R x :=
    (S.later_component_support_subset hsequence hy hyY).2
  have hxy : (selectedGraph χ R).connectedComponentMk x ≠
      (selectedGraph χ R).connectedComponentMk y := by
    intro heq
    apply hyNotX
    change y ∈ ((selectedGraph χ R).connectedComponentMk x).supp
    rw [heq]
    exact hyY
  exact S.last_leaf_restriction_with_domain hk hno y hxy hX hY Q hQ

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open ErdosProblems.PathLemmaFourScalar

/-- The exact literal formula is nondecreasing in the complete-host order for
ALL natural parameters, including truncated subtraction below its usual regime. -/
theorem pathFormula_host_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    pathFormula m k ≤ pathFormula n k := by
  dsimp only [pathFormula]
  let ell : ℕ := (k - 1) / 2
  let epsilon : ℕ := if Odd k then 1 else 2
  have hsub : m - ell + 1 ≤ n - ell + 1 :=
    Nat.add_le_add_right (Nat.sub_le_sub_right hmn ell) 1
  have hmul : (ell - 1) * (m - ell + 1) ≤
      (ell - 1) * (n - ell + 1) := Nat.mul_le_mul_left (ell - 1) hsub
  exact max_le_max (le_refl _)
    (Nat.add_le_add_right (Nat.add_le_add_left hmul ((ell - 1).choose 2)) epsilon)

/-- The original first term is below the exact maximum, without any graph,
positivity, parity or induction-domain assumption. -/
theorem pathFormula_first_term_le (k n : ℕ) :
    (k - 2).choose 2 + 1 ≤ pathFormula n k := by
  dsimp only [pathFormula]
  exact le_max_left _ _

/-- Exact literal FC(ii) syntax: no shifted or rational surrogate expression. -/
theorem pathFormula_eq_literal_fc (k n : ℕ) :
    pathFormula n k =
      (let ell := (k - 1) / 2
       let epsilon := if Odd k then 1 else 2
       max ((k - 2).choose 2 + 1)
         ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + epsilon)) := rfl

/-- FULL smaller COMPLETE-host upper induction hypothesis at the fixed path
order k. The entire antiRamseyNum is bounded; no favorable coloring or selected
graph variant occurs. This is an explicit conditional input, not a new axiom. -/
def OriginalFullSmallerHostIH (k n : ℕ) : Prop :=
  ∀ m : ℕ, k ≤ m → m < n →
    antiRamseyNum (pathGraph k) m ≤ pathFormula m k

/-- An actual all-original-q smaller-host restriction in its genuine induction
domain combines with the FULL IH and exact host monotonicity. -/
theorem original_color_count_le_formula_of_full_smaller_host_IH
    (k n m q : ℕ) (hIH : OriginalFullSmallerHostIH k n)
    (hkm : k ≤ m) (hmn : m < n)
    (hq : q ≤ antiRamseyNum (pathGraph k) m) :
    q ≤ pathFormula n k :=
  hq.trans ((hIH m hkm hmn).trans (pathFormula_host_mono k hmn.le))

/-- The SAME original high palette contradicts an actual smaller-host
restriction in the FULL numerical induction domain. -/
theorem original_high_color_count_false_of_full_smaller_host_IH
    (k n m q : ℕ) (hIH : OriginalFullSmallerHostIH k n)
    (hkm : k ≤ m) (hmn : m < n)
    (hq : q ≤ antiRamseyNum (pathGraph k) m)
    (hhigh : pathFormula n k < q) : False :=
  (not_lt_of_ge (original_color_count_le_formula_of_full_smaller_host_IH
    k n m q hIH hkm hmn hq)) hhigh

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open ErdosProblems.PathLemmaFourScalar

variable {n q : ℕ}

/-- Canonical inclusion of a finite nonempty actual support, indexed by its
literal Nat.card. Positivity will be derived by the actual first-head caller. -/
noncomputable def originalHeadCardEmbedding
    (X : Set (Fin n)) (hcard : Nat.card X ≠ 0) :
    Fin (Nat.card X) ↪ Fin n :=
  (Nat.equivFinOfCardPos hcard).symm.toEmbedding.trans
    (Function.Embedding.subtype (fun v : Fin n => v ∈ X))

/-- The indexing inclusion covers exactly the actual support. -/
theorem originalHeadCardEmbedding_range
    (X : Set (Fin n)) (hcard : Nat.card X ≠ 0) :
    Set.range (originalHeadCardEmbedding X hcard) = X := by
  classical
  let e : X ≃ Fin (Nat.card X) := Nat.equivFinOfCardPos hcard
  apply Set.ext
  intro v
  constructor
  · rintro ⟨j, rfl⟩
    exact (e.symm j).property
  · intro hv
    refine ⟨e ⟨v, hv⟩, ?_⟩
    change (e.symm (e ⟨v, hv⟩)).val = v
    exact congrArg Subtype.val (e.symm_apply_apply ⟨v, hv⟩)

/-- From an ACTUAL proper first retained P(k-2), derive
an actual support-indexing embedding, ALL original colors, original no-rainbow
copies, the literal anti-Ramsey witness, and BOTH full smaller-host domains. No embedding, restricted palette, desired count, or domain is a premise. -/
theorem OriginalResidualCutStage.first_head_full_palette_induction_bundle
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (hq : (k - 2).choose 2 + 1 < q) :
    ∃ i : Fin (Nat.card (componentSupport χ R x)) ↪ Fin n,
      Set.range i = componentSupport χ R x ∧
      Function.Surjective (originalPrefixRestrictedColoring χ i) ∧
      (∀ F : (pathGraph k).Copy
        (⊤ : SimpleGraph (Fin (Nat.card (componentSupport χ R x)))),
        ¬ IsRainbow F.toHom (originalPrefixRestrictedColoring χ i)) ∧
      q ≤ antiRamseyNum (pathGraph k) (Nat.card (componentSupport χ R x)) ∧
      k ≤ Nat.card (componentSupport χ R x) ∧
      Nat.card (componentSupport χ R x) < n := by
  classical
  have hdomain :=
    S.first_head_full_induction_domain_of_retained_path_order hproper hk P hno hq
  have hcard : Nat.card (componentSupport χ R x) ≠ 0 := by omega
  let i := originalHeadCardEmbedding (componentSupport χ R x) hcard
  have hrange : Set.range i = componentSupport χ R x :=
    originalHeadCardEmbedding_range (componentSupport χ R x) hcard
  have htail := S.uncut_tail_edgeless_of_retained_path_order hk P hno
  have howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val := by
    intro c
    rw [hrange]
    simpa only [Set.compl_univ, Set.empty_union] using
      S.owner_inside_processed_prefix htail c
  have hfull := originalPrefixRestrictedColoring_full_witness
    (pathGraph k) χ R i howners hno
  exact ⟨i, hrange, hfull.1, hfull.2.1, hfull.2.2, hdomain.1, hdomain.2⟩

/-- The original high-color numerical hypothesis excludes
an actual long path in a proper FIRST retained piece, under FULL smaller-host IH. -/
theorem OriginalResidualCutStage.false_of_proper_first_retained_path_and_full_IH
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : pathFormula n k < q) : False := by
  have hq : (k - 2).choose 2 + 1 < q :=
    lt_of_le_of_lt (pathFormula_first_term_le k n) hhigh
  obtain ⟨_, _, _, _, hcount, hkm, hmn⟩ :=
    S.first_head_full_palette_induction_bundle hproper hk P hno hq
  exact original_high_color_count_false_of_full_smaller_host_IH
    k n (Nat.card (componentSupport χ R x)) q hIH hkm hmn hcount hhigh

/-- No favorable first-head path is supplied: every actual
retained P(k-2) is impossible in the literal original high-color induction step. The later-family caller may derive first-head properness from its actual tail. -/
theorem OriginalResidualCutStage.no_retained_long_path_of_proper_first_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : pathFormula n k < q) :
    ∀ _P : (pathGraph (k - 2)).Copy S.retainedGraph, False := by
  intro P
  exact S.false_of_proper_first_retained_path_and_full_IH
    hproper hk P hno hIH hhigh

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q k : ℕ}

/-- Every ACTUAL retained stage graph of this unchanged original cut family
excludes a path with k-2 vertices. Isolates and zero-cut stages are retained. -/
def OriginalResidualCutFamily.NoLongRetainedPath
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (k : ℕ) : Prop :=
  match F with
  | .nil _ _ => True
  | .cons stage tail =>
      (∀ _P : (pathGraph (k - 2)).Copy stage.retainedGraph, False) ∧
        OriginalResidualCutFamily.NoLongRetainedPath tail k

/-- Any ACTUAL later stage in the fixed first stage's SAME-R greedy sequence
is excluded by the FULL numerical IH. -/
theorem OriginalResidualCutStage.no_long_retained_path_of_roots_in_later_sequence
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    (hk : 5 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : ErdosProblems.PathLemmaFourScalar.pathFormula n k < q)
    {V : Set (Fin q)} {Z : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R V Z roots)
    (hroots : ∀ y ∈ roots, y ∈ xs) : F.NoLongRetainedPath k := by
  cases n with
  | zero => omega
  | succ m =>
      revert hroots
      induction F with
      | nil =>
          intro _
          trivial
      | @cons V Z y ys T tail ih =>
          intro hroots
          change (∀ _P : (pathGraph (k - 2)).Copy T.retainedGraph, False) ∧
            tail.NoLongRetainedPath k
          constructor
          · intro P
            have hy : y ∈ xs := hroots y (by simp)
            have hrestricted := S.last_leaf_restriction_of_later_retained_long_path
              hsequence hy T hk P hno
            exact original_high_color_count_false_of_full_smaller_host_IH
              k (m + 1) m q hIH hrestricted.1 (by omega) hrestricted.2 hhigh
          · apply ih
            intro z hz
            exact hroots z (List.mem_cons_of_mem y hz)

/-- Under the FULL smaller-host numerical IH and original high q, a proper
first component excludes a retained P(k-2) at EVERY actual stage. The initial
whole-prefix family supplies all later-stage ordering/membership data. -/
theorem OriginalResidualCutFamily.no_long_retained_path_of_proper_first_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 5 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n)
    (hhigh : ErdosProblems.PathLemmaFourScalar.pathFormula n k < q) :
    F.NoLongRetainedPath k := by
  cases F with
  | cons S tail =>
      change (∀ _P : (pathGraph (k - 2)).Copy S.retainedGraph, False) ∧
        tail.NoLongRetainedPath k
      constructor
      · exact S.no_retained_long_path_of_proper_first_component
          hproper (by omega) hno hIH hhigh
      · have hsequence := (OriginalResidualCutFamily.cons S tail).toGreedySequence
        exact S.no_long_retained_path_of_roots_in_later_sequence
          hsequence hk hkn hno hIH hhigh tail (fun _ hy => hy)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- A supplied graph on a finite carrier has a forbidden-free supergraph
such that every missing distinct pair creates an ordinary forbidden copy. -/
theorem exists_saturated_free_supergraph {V W : Type*} [Fintype V]
    (F : SimpleGraph W) (G : SimpleGraph V) (hG : F.Free G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ F.Free H ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v →
        Nonempty (F.Copy (H ⊔
          SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V)))) := by
  classical
  let : (J : SimpleGraph V) → Fintype J.edgeSet :=
    fun J => SimpleGraph.fintypeEdgeSet J
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun J => G ≤ J ∧ F.Free J)
  have hGmem : G ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ G, le_rfl, hG⟩
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image candidates (fun J => J.edgeFinset.card) ⟨G, hGmem⟩
  obtain ⟨hGH, hFH⟩ := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hGH, hFH, ?_⟩
  intro u v huv hmissing
  let J : SimpleGraph V :=
    H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))
  have hHJ : H ≤ J := le_sup_left
  have hnew : J.Adj u v := by
    exact (SimpleGraph.sup_adj H
      (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) u v).mpr
      (Or.inr ((SimpleGraph.fromEdgeSet_adj
        ({s(u, v)} : Set (Sym2 V))).mpr ⟨Set.mem_singleton _, huv⟩))
  have hstrict : H < J := by
    refine lt_of_le_of_ne hHJ ?_
    intro heq
    exact hmissing (heq.symm ▸ hnew)
  change Nonempty (F.Copy J)
  by_contra hnoCopy
  have hFJ : F.Free J := hnoCopy
  have hJmem : J ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ J, hGH.trans hHJ, hFJ⟩
  have hcard : H.edgeFinset.card < J.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)
  exact (Nat.not_lt_of_ge (hmax J hJmem)) hcard

-- Literal spanning-path application, for every natural k, without positivity.
example (k : ℕ) (G : SimpleGraph (Fin k)) (hG : (pathGraph k).Free G) :
    ∃ H : SimpleGraph (Fin k), G ≤ H ∧ (pathGraph k).Free H ∧
      ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
        Nonempty ((pathGraph k).Copy (H ⊔
          SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin k))))) :=
  exists_saturated_free_supergraph (pathGraph k) G hG

end ErdosProblems.PathUpperReduction
