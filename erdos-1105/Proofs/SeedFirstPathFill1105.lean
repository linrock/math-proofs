module

public import FixedCarrierFillGuards1105
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-!
Actual finite ordered seed-first fills on one Fin N. The public branch has N=2*d+2. Original seed/high degrees justify the first
family; the completed first family, not an assumed degree boost, justifies
the restored family. All residual adjacencies outside W remain ORIGINAL. No original-color upper theorem, count/star theorem, or carrier transport is
claimed.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.SeedFirstPathFill1105

open SimpleGraph
open ErdosProblems.PathSpanningNonedgeDeficit
open ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105
open ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105

/-- A literal finite ordered sequence of augmentations on the SAME carrier.
Already present pairs have no effect, so repeated orientations are harmless. -/
def fillOrdered {N : ℕ} (G : SimpleGraph (Fin N)) :
    List (Fin N × Fin N) → SimpleGraph (Fin N)
  | [] => G
  | p :: ps => fillOrdered (augment G p.1 p.2) ps

/-- The first internally constructed pair family. Diagonal pairs are omitted. -/
def seedPairs {N : ℕ} (K W : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (W ×ˢ K).filter (fun p => p.1 ≠ p.2)

/-- The second internally constructed family uses the literal complement of K. -/
def restoredPairs {N : ℕ} (K W : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (W ×ˢ (Finset.univ \ K)).filter (fun p => p.1 ≠ p.2)

def seedFilled {N : ℕ} (G : SimpleGraph (Fin N)) (K W : Finset (Fin N)) :=
  fillOrdered G (seedPairs K W).toList

def seedFirstFilled {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) :=
  fillOrdered (seedFilled G K W) (restoredPairs K W).toList

theorem augment_le {N : ℕ} (G J : SimpleGraph (Fin N))
    (u v : Fin N) (hGJ : G ≤ J) (huv : J.Adj u v) :
    augment G u v ≤ J := by
  apply sup_le hGJ
  intro x y hxy
  obtain ⟨hpair, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have heq : s(x,y) = s(u,v) := Set.mem_singleton_iff.mp hpair
  rcases Sym2.eq_iff.mp heq with h | h
  · simpa only [h.1, h.2] using huv
  · simpa only [h.1, h.2] using J.adj_symm huv

theorem augment_eq_of_adj {N : ℕ} (G : SimpleGraph (Fin N))
    (u v : Fin N) (huv : G.Adj u v) : augment G u v = G :=
  le_antisymm (augment_le G G u v le_rfl huv) le_sup_left

theorem augment_pair_adj {N : ℕ} (G : SimpleGraph (Fin N))
    (u v : Fin N) (hne : u ≠ v) : (augment G u v).Adj u v := by
  apply (SimpleGraph.sup_adj _ _ _ _).mpr
  right
  exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨by simp, hne⟩

theorem le_fillOrdered {N : ℕ} (G : SimpleGraph (Fin N))
    (L : List (Fin N × Fin N)) : G ≤ fillOrdered G L := by
  induction L generalizing G with
  | nil => exact le_rfl
  | cons p ps ih => exact le_trans le_sup_left (ih (augment G p.1 p.2))

theorem fillOrdered_le {N : ℕ} (G J : SimpleGraph (Fin N))
    (L : List (Fin N × Fin N)) (hGJ : G ≤ J)
    (hpairs : ∀ p ∈ L, J.Adj p.1 p.2) : fillOrdered G L ≤ J := by
  have haux : ∀ L : List (Fin N × Fin N), ∀ G : SimpleGraph (Fin N),
      G ≤ J → (∀ p ∈ L, J.Adj p.1 p.2) → fillOrdered G L ≤ J := by
    intro L
    induction L with
    | nil => intro G hGJ _; exact hGJ
    | cons p ps ih =>
        intro G hGJ hpairs
        exact ih (augment G p.1 p.2)
          (augment_le G J p.1 p.2 hGJ (hpairs p (by simp)))
          (fun q hq => hpairs q (by simp only [List.mem_cons]; exact Or.inr hq))
  exact haux L G hGJ hpairs

theorem fillOrdered_pair_adj {N : ℕ} (G : SimpleGraph (Fin N))
    (L : List (Fin N × Fin N)) (p : Fin N × Fin N)
    (hp : p ∈ L) (hne : p.1 ≠ p.2) : (fillOrdered G L).Adj p.1 p.2 := by
  have haux : ∀ L : List (Fin N × Fin N), ∀ G : SimpleGraph (Fin N),
      ∀ p ∈ L, p.1 ≠ p.2 → (fillOrdered G L).Adj p.1 p.2 := by
    intro L
    induction L with
    | nil => intro G p hp; simp at hp
    | cons q qs ih =>
        intro G p hp hne
        rcases List.mem_cons.mp hp with h | h
        · subst p
          exact le_fillOrdered (augment G q.1 q.2) qs
            (augment_pair_adj G q.1 q.2 hne)
        · exact ih (augment G q.1 q.2) p h hne
  exact haux L G p hp hne

/-- A finite sequence preserves P_N-freedom when every actual missing step
has the existing N-1 guard. The final seed caller DERIVES this guard. -/
theorem fillOrdered_free {N : ℕ} (hN : 3 ≤ N)
    (B : SimpleGraph (Fin N)) (L : List (Fin N × Fin N))
    (hne : ∀ p ∈ L, p.1 ≠ p.2)
    (hguard : ∀ J : SimpleGraph (Fin N), B ≤ J →
      ∀ p ∈ L, N-1 ≤ J.degree p.1 + J.degree p.2)
    (J : SimpleGraph (Fin N)) (hBJ : B ≤ J)
    (hfree : (pathGraph N).Free J) : (pathGraph N).Free (fillOrdered J L) := by
  classical
  have haux : ∀ L : List (Fin N × Fin N),
      (∀ p ∈ L, p.1 ≠ p.2) →
      (∀ J : SimpleGraph (Fin N), B ≤ J →
        ∀ p ∈ L, N-1 ≤ J.degree p.1 + J.degree p.2) →
      ∀ J : SimpleGraph (Fin N), B ≤ J → (pathGraph N).Free J →
        (pathGraph N).Free (fillOrdered J L) := by
    intro L
    induction L with
    | nil => intro _ _ J _ hfree; exact hfree
    | cons p ps ih =>
        intro hne hguard J hBJ hfree
        have hstep : (pathGraph N).Free (augment J p.1 p.2) := by
          by_cases hadj : J.Adj p.1 p.2
          · simpa only [augment_eq_of_adj J p.1 p.2 hadj] using hfree
          · exact pathGraph_free_after_adding_missing_pair hN J hfree p.1 p.2
              (hne p (by simp)) hadj (hguard J hBJ p (by simp))
        exact ih
          (fun q hq => hne q (by simp only [List.mem_cons]; exact Or.inr hq))
          (fun H hBH q hq => hguard H hBH q
            (by simp only [List.mem_cons]; exact Or.inr hq))
          (augment J p.1 p.2) (le_trans hBJ le_sup_left) hstep
  exact haux L hne hguard J hBJ hfree

theorem mem_seedPairs {N : ℕ} (K W : Finset (Fin N))
    (p : Fin N × Fin N) : p ∈ seedPairs K W ↔
      p.1 ∈ W ∧ p.2 ∈ K ∧ p.1 ≠ p.2 := by
  classical
  simp only [seedPairs, Finset.mem_filter, Finset.mem_product]
  tauto

theorem mem_restoredPairs {N : ℕ} (K W : Finset (Fin N))
    (p : Fin N × Fin N) : p ∈ restoredPairs K W ↔
      p.1 ∈ W ∧ p.2 ∉ K ∧ p.1 ≠ p.2 := by
  classical
  simp only [restoredPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

/-- The actual completed FIRST ordered family is exactly the existing
explicit seed fill graph. This equality is proved, never a fill oracle. -/
theorem seedFilled_eq {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) : seedFilled G K W = fillSeedPairs G K W := by
  classical
  apply le_antisymm
  · apply fillOrdered_le G (fillSeedPairs G K W) _ le_sup_left
    intro p hp
    obtain ⟨hw, hv, hne⟩ :=
      (mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)
    exact filled_seed_adj G K W p.1 p.2 hw hv hne
  · apply sup_le (le_fillOrdered G _)
    intro u v huv
    obtain ⟨⟨w, hw, x, hx, hne, heq⟩, _⟩ :=
      (SimpleGraph.fromEdgeSet_adj _).mp huv
    have hadj : (seedFilled G K W).Adj w x :=
      fillOrdered_pair_adj G _ (w,x)
        (Finset.mem_toList.mpr ((mem_seedPairs K W (w,x)).mpr ⟨hw,hx,hne⟩)) hne
    rcases Sym2.eq_iff.mp heq with h | h
    · simpa only [seedFilled, h.1, h.2] using hadj
    · simpa only [seedFilled, h.1, h.2] using (seedFilled G K W).adj_symm hadj

/-- Both finite families together add exactly ALL distinct W-incident pairs
on the same carrier, with no added residual edge outside W. -/
theorem seedFirstFilled_eq {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) :
    seedFirstFilled G K W = fillSeedPairs G Finset.univ W := by
  classical
  let H := fillSeedPairs G Finset.univ W
  have hseed : seedFilled G K W ≤ H := by
    apply fillOrdered_le G H _ le_sup_left
    intro p hp
    obtain ⟨hw, _, hne⟩ :=
      (mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)
    exact filled_seed_adj G Finset.univ W p.1 p.2 hw (Finset.mem_univ _) hne
  apply le_antisymm
  · apply fillOrdered_le (seedFilled G K W) H _ hseed
    intro p hp
    obtain ⟨hw, _, hne⟩ :=
      (mem_restoredPairs K W p).mp (Finset.mem_toList.mp hp)
    exact filled_seed_adj G Finset.univ W p.1 p.2 hw (Finset.mem_univ _) hne
  · apply sup_le
      (le_trans (le_fillOrdered G _) (le_fillOrdered (seedFilled G K W) _))
    intro u v huv
    obtain ⟨⟨w, hw, x, _, hne, heq⟩, _⟩ :=
      (SimpleGraph.fromEdgeSet_adj _).mp huv
    have hadj : (seedFirstFilled G K W).Adj w x := by
      by_cases hx : x ∈ K
      · apply le_fillOrdered (seedFilled G K W) _
        rw [seedFilled_eq]
        exact filled_seed_adj G K W w x hw hx hne
      · exact fillOrdered_pair_adj (seedFilled G K W) _ (w,x)
          (Finset.mem_toList.mpr
            ((mem_restoredPairs K W (w,x)).mpr ⟨hw,hx,hne⟩)) hne
    rcases Sym2.eq_iff.mp heq with h | h
    · simpa only [seedFirstFilled, h.1, h.2] using hadj
    · simpa only [seedFirstFilled, h.1, h.2] using (seedFirstFilled G K W).adj_symm hadj

theorem residual_original {N : ℕ} (G : SimpleGraph (Fin N))
    (K W : Finset (Fin N)) (u v : Fin N) (hu : u ∉ W) (hv : v ∉ W) :
    (seedFirstFilled G K W).Adj u v ↔ G.Adj u v := by
  rw [seedFirstFilled_eq]
  constructor
  · intro h
    rcases (SimpleGraph.sup_adj _ _ _ _).mp h with h | h
    · exact h
    · obtain ⟨⟨w, hw, x, _, _, heq⟩, _⟩ :=
        (SimpleGraph.fromEdgeSet_adj _).mp h
      rcases Sym2.eq_iff.mp heq with he | he
      · exact False.elim (hu (he.1.symm ▸ hw))
      · exact False.elim (hv (he.2.symm ▸ hw))
  · intro hadj
    exact (show G ≤ fillSeedPairs G Finset.univ W from le_sup_left) hadj

/-- Actual two-phase fixed-carrier path filling. Every degree guard comes
from ORIGINAL G degrees or the PROVED first-family completion. Restored
degree is on this very Fin(2*d+2), not ambient degree on a larger graph.
The caller must derive these retained degrees from its SAME actual trace. -/
theorem seed_first_path_free {d h : ℕ} (hd : 4 ≤ d) (_hlow : 3 ≤ h)
    (hh : h ≤ d) (G : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d+1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d-h+2 ≤ G.degree x)
    (hfree : (pathGraph (2*d+2)).Free G) :
    (pathGraph (2*d+2)).Free (seedFirstFilled G K W) ∧
      G ≤ seedFirstFilled G K W ∧
      (∀ w ∈ W, ∀ v, w ≠ v → (seedFirstFilled G K W).Adj w v) ∧
      (∀ u, u ∉ W → ∀ v, v ∉ W →
        ((seedFirstFilled G K W).Adj u v ↔ G.Adj u v)) := by
  classical
  have hN : 3 ≤ 2*d+2 := by omega
  have hfirst : (pathGraph (2*d+2)).Free (seedFilled G K W) := by
    apply fillOrdered_free hN G (seedPairs K W).toList
      (fun p hp => ((mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)).2.2)
      ?_ G le_rfl hfree
    intro J hGJ p hp
    obtain ⟨hw, hv, _⟩ :=
      (mem_seedPairs K W p).mp (Finset.mem_toList.mp hp)
    exact seed_pair_guard G J K p.1 p.2 hGJ (hhigh p.1 hw) (hmin p.2 hv)
  have hsecond : (pathGraph (2*d+2)).Free (seedFirstFilled G K W) := by
    apply fillOrdered_free hN (seedFilled G K W) (restoredPairs K W).toList
      (fun p hp => ((mem_restoredPairs K W p).mp (Finset.mem_toList.mp hp)).2.2)
      ?_ (seedFilled G K W) le_rfl hfirst
    intro J hseedJ p hp
    obtain ⟨hw, hx, _⟩ :=
      (mem_restoredPairs K W p).mp (Finset.mem_toList.mp hp)
    rw [seedFilled_eq] at hseedJ
    exact restoration_pair_guard G J K W p.1 p.2 hh horder hWK hw hseedJ
      (hrestored p.2 hx)
  refine ⟨hsecond, ?_, ?_, ?_⟩
  · exact le_trans (le_fillOrdered G _) (le_fillOrdered (seedFilled G K W) _)
  · intro w hw v hne
    rw [seedFirstFilled_eq]
    exact filled_seed_adj G Finset.univ W w v hw (Finset.mem_univ _) hne
  · intro u hu v hv
    exact residual_original G K W u v hu hv

/-- The explicit final graph is P_N-free; no filling sequence is supplied
by the caller. This is the direct interface for residual-block arguments. -/
theorem path_free_all_seed_incident_pairs {d h : ℕ} (hd : 4 ≤ d) (hlow : 3 ≤ h)
    (hh : h ≤ d) (G : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hmin : ∀ v ∈ K, d ≤ originalSeedDegree G K v)
    (hhigh : ∀ w ∈ W, d+1 ≤ originalSeedDegree G K w)
    (hrestored : ∀ x, x ∉ K → d-h+2 ≤ G.degree x)
    (hfree : (pathGraph (2*d+2)).Free G) :
    (pathGraph (2*d+2)).Free (fillSeedPairs G Finset.univ W) := by
  have hfilled := (seed_first_path_free hd hlow hh G K W horder hWK
    hmin hhigh hrestored hfree).1
  simpa only [seedFirstFilled_eq] using hfilled

end ErdosProblems.PathUpperReduction.SeedFirstPathFill1105

