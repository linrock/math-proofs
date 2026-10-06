module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

/-!
The standard anti-Ramsey lower-bound coloring: label an edge by its larger endpoint.
The smallest vertex is never used as a label, while every other vertex is used.
-/

namespace ErdosProblems.AntiRamseyTriangle

/-- The edge `s(a,b)` receives its larger endpoint as its color. -/
def maxEndpointColor (n : ℕ) : SimpleGraph.TopEdgeLabeling (Fin n) (Fin n) :=
  fun e => Sym2.lift ⟨fun a b => max a b, fun a b => max_comm a b⟩ e.1

@[simp] theorem maxEndpointColor_get {n : ℕ} (a b : Fin n)
    (hab : (⊤ : SimpleGraph (Fin n)).Adj a b) :
    (maxEndpointColor n).get a b hab = max a b := by
  rfl

/-- Every triangle has a repeated color in the larger-endpoint coloring. -/
theorem maxEndpointColor_noRainbowTriangle {n : ℕ} (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (maxEndpointColor n).get a b ((SimpleGraph.top_adj a b).2 hab) =
        (maxEndpointColor n).get b c ((SimpleGraph.top_adj b c).2 hbc) ∨
      (maxEndpointColor n).get b c ((SimpleGraph.top_adj b c).2 hbc) =
        (maxEndpointColor n).get c a ((SimpleGraph.top_adj c a).2 hca) ∨
      (maxEndpointColor n).get c a ((SimpleGraph.top_adj c a).2 hca) =
        (maxEndpointColor n).get a b ((SimpleGraph.top_adj a b).2 hab) := by
  simp only [maxEndpointColor_get]
  rcases le_total a b with hab' | hba'
  · rcases le_total b c with hbc' | hcb'
    · right; left
      rw [max_eq_right hbc', max_eq_left (le_trans hab' hbc')]
    · left
      rw [max_eq_right hab', max_eq_left hcb']
  · rcases le_total a c with hac' | hca'
    · right; left
      rw [max_eq_right (le_trans hba' hac'), max_eq_left hac']
    · right; right
      rw [max_eq_right hca', max_eq_left hba']

/-- The smallest vertex is not the color of any edge. -/
theorem maxEndpointColor_ne_zero {n : ℕ} [NeZero n]
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) : maxEndpointColor n e ≠ 0 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b :=
      (SimpleGraph.top_adj a b).1 (((⊤ : SimpleGraph (Fin n)).mem_edgeSet).1 he)
    change max a b ≠ 0
    intro hzero
    have ha : a = 0 := le_antisymm (by rw [← hzero]; exact le_max_left a b) (Fin.zero_le a)
    have hb : b = 0 := le_antisymm (by rw [← hzero]; exact le_max_right a b) (Fin.zero_le b)
    exact hab (ha.trans hb.symm)

/-- The colors used by the construction are precisely the vertices other than zero. -/
theorem maxEndpointColor_image_eq_erase_zero {n : ℕ} [NeZero n] :
    Finset.univ.image (maxEndpointColor n) = Finset.univ.erase (0 : Fin n) := by
  apply Finset.ext
  intro c
  constructor
  · intro hc
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_erase.mpr ⟨maxEndpointColor_ne_zero e, Finset.mem_univ _⟩
  · intro hc
    obtain ⟨hc, _⟩ := Finset.mem_erase.mp hc
    apply Finset.mem_image.mpr
    refine ⟨⟨s((0 : Fin n), c), ?_⟩, Finset.mem_univ _, ?_⟩
    · exact ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
        ((SimpleGraph.top_adj 0 c).2 (Ne.symm hc))
    · simp [maxEndpointColor]

/-- The lower-bound coloring uses exactly `n-1` colors. -/
theorem maxEndpointColor_image_card {n : ℕ} (hn : 3 ≤ n) :
    (Finset.univ.image (maxEndpointColor n)).card = n - 1 := by
  cases n with
  | zero => omega
  | succ m =>
      rw [maxEndpointColor_image_eq_erase_zero]
      simp [Finset.card_erase_of_mem]

/-- Relabel the used positive endpoints by `Fin m`; this uses every color. -/
def predEndpointColor (m : ℕ) [NeZero m] :
    SimpleGraph.TopEdgeLabeling (Fin (m + 1)) (Fin m) :=
  fun e => (0 : Fin m).predAbove (maxEndpointColor (m + 1) e)

@[simp] theorem predEndpointColor_get {m : ℕ} [NeZero m] (a b : Fin (m + 1))
    (hab : (⊤ : SimpleGraph (Fin (m + 1))).Adj a b) :
    (predEndpointColor m).get a b hab = (0 : Fin m).predAbove (max a b) := by
  rfl

/-- Each color occurs on the edge from vertex zero to its successor. -/
theorem predEndpointColor_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (predEndpointColor m) := by
  intro i
  refine ⟨⟨s((0 : Fin (m + 1)), i.succ), ?_⟩, ?_⟩
  · exact ((⊤ : SimpleGraph (Fin (m + 1))).mem_edgeSet).2
      ((SimpleGraph.top_adj 0 i.succ).2 (Ne.symm (Fin.succ_ne_zero i)))
  · simp [predEndpointColor, maxEndpointColor]

/-- The surjective `Fin m` relabeling also has no rainbow triangle. -/
theorem predEndpointColor_noRainbowTriangle {m : ℕ} [NeZero m]
    (a b c : Fin (m + 1)) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (predEndpointColor m).get a b ((SimpleGraph.top_adj a b).2 hab) =
        (predEndpointColor m).get b c ((SimpleGraph.top_adj b c).2 hbc) ∨
      (predEndpointColor m).get b c ((SimpleGraph.top_adj b c).2 hbc) =
        (predEndpointColor m).get c a ((SimpleGraph.top_adj c a).2 hca) ∨
      (predEndpointColor m).get c a ((SimpleGraph.top_adj c a).2 hca) =
        (predEndpointColor m).get a b ((SimpleGraph.top_adj a b).2 hab) := by
  simp only [predEndpointColor_get]
  have h := maxEndpointColor_noRainbowTriangle a b c hab hbc hca
  simp only [maxEndpointColor_get] at h
  rcases h with h | h | h
  · exact Or.inl (congrArg (Fin.predAbove (0 : Fin m)) h)
  · exact Or.inr (Or.inl (congrArg (Fin.predAbove (0 : Fin m)) h))
  · exact Or.inr (Or.inr (congrArg (Fin.predAbove (0 : Fin m)) h))

end ErdosProblems.AntiRamseyTriangle
