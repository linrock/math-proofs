module

public import CycleForcedTailAppendSuffixV3
public import CycleTwoSpliceSkipExtractionV2
public import CycleClosingColorEquality
public import CyclePartialSpliceClosing
public import CycleFirstPathExtensionV2

@[expose] public section

/-! rotating Claim2 assembly for k=m+3>=5. -/

namespace ErdosProblems.AntiRamseyCycleRotatingClaimTwo

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem numeric_ordered_of_steps {V : Type*} {t : ℕ}
    (G : SimpleGraph V) (p : Fin (t + 1) → V)
    (hstep : ∀ i : Fin t, G.Adj (p (Fin.castSucc i)) (p (Fin.succ i))) :
    ∀ a b : Fin (t + 1), a.val + 1 = b.val → G.Adj (p a) (p b) := by
  intro a b hab
  have ha : a.val < t := by have hb := b.isLt; omega
  let i : Fin t := ⟨a.val, ha⟩
  have hcast : Fin.castSucc i = a := Fin.ext rfl
  have hsucc : Fin.succ i = b := Fin.ext hab
  simpa only [hcast, hsucc] using hstep i

theorem no_endpoint_chord_of_local_cycle_exclusion
    {s : ℕ} (hs : 2 ≤ s) (G : SimpleGraph (Fin n))
    (p : Fin (s + 1) → Fin n) (hp : Function.Injective p)
    (hstep : ∀ i : Fin s, G.Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (s + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (s + 1)).Copy G,
      ¬∀ i : Fin (s + 1), f i ∈ D) :
    ¬ G.Adj (p 0) (p (Fin.last s)) := by
  intro hchord
  have : NeZero s := ⟨by omega⟩
  let H : SimpleGraph (Fin (s + 1)) := G.comap p
  have hfree :=
    ErdosProblems.AntiRamseyCyclePathOre.cycle_free_on_ordered_path_of_component
      G p hp D hpD hnoD
  have hHpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → H.Adj a b :=
    numeric_ordered_of_steps G p hstep
  have hA : H.Adj 0 (Fin.succ (0 : Fin s)) := hstep 0
  have hB : H.Adj (Fin.last s) (Fin.castSucc (0 : Fin s)) := hchord.symm
  exact hfree
    (ErdosProblems.AntiRamseyCyclePathOre.crossing_chords_force_cycle
      hs H hHpath 0 hA hB)

/-- An inward selected tail in the original high distinct-pair regime is
impossible under the exact host/local-cycle hypotheses, by rotating splice. -/
theorem inward_tail_contradiction
    {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (m + 2), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (m + 2), f i ∈ D)
    (hpair : ∀ u v : Fin n, u ≠ v →
      m + 2 ≤ (newColors χ u).card + (newColors χ v).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) : False := by
  classical
  have hpEnds : p 0 ≠ p (Fin.last (m + 1)) := hp.ne (by
    intro h
    have hv : 0 = m + 1 := congrArg Fin.val h
    omega)
  have hpairP := hpair (p 0) (p (Fin.last (m + 1))) hpEnds
  obtain ⟨w, _e, _hwImage, _hadj, _he, _hnew, hconfig⟩ :=
    ErdosProblems.AntiRamseyCycleForcedTailAppendSuffix.forced_tail_literal_append_and_suffix
      (by omega) χ r p hp hpath hnewLast hno D hpD hnoD hpairP hclosed
  dsimp only at hconfig
  obtain ⟨hRpath, hQpath, hR, _hRD, hQ, hQD, _hval, _hcolor, _hinner,
    _hsame, _hQold, hRnew, hQnew⟩ := hconfig
  let R : Fin (m + 3) → Fin n := Fin.snoc p w
  let Q : Fin (m + 2) → Fin n := fun i => R i.succ
  have hprefix : ∀ i : Fin (m + 2), R (Fin.castSucc i) = p i := by
    intro i
    simp only [R, Fin.snoc_castSucc]
  have hprefixMap : (fun i : Fin (m + 2) => R (Fin.castSucc i)) = p := funext hprefix
  have hRzero : R 0 = p 0 := hprefix 0
  have hQzero : Q 0 = R ⟨1, by omega⟩ := rfl
  have hprefixLast : R ⟨m + 1, by omega⟩ = p (Fin.last (m + 1)) := by
    have hidx : (⟨m + 1, by omega⟩ : Fin (m + 3)) =
        Fin.castSucc (Fin.last (m + 1)) := Fin.ext rfl
    rw [hidx]
    exact hprefix (Fin.last (m + 1))
  have hQLast : Q (Fin.last (m + 1)) = R (Fin.last (m + 2)) := by
    simp only [Q, Fin.succ_last]
  have hforbidLeft : ¬ (selectedGraph χ r).Adj (R 0) (R ⟨m + 1, by omega⟩) := by
    rw [hRzero, hprefixLast]
    exact no_endpoint_chord_of_local_cycle_exclusion (s := m + 1) (by omega)
      (selectedGraph χ r) p hp hpath D hpD hnoD
  have hforbidRight : ¬ (selectedGraph χ r).Adj
      (R ⟨1, by omega⟩) (R (Fin.last (m + 2))) := by
    rw [← hQzero, ← hQLast]
    exact no_endpoint_chord_of_local_cycle_exclusion (s := m + 1) (by omega)
      (selectedGraph χ r) Q hQ hQpath D hQD hnoD
  have hheadP :=
    ErdosProblems.AntiRamseyCycleHeadNewDominance.no_head_new_deficit_of_inward_tail
      (by omega) χ r p hp hpath hnewLast hno
  have hheadQ :=
    ErdosProblems.AntiRamseyCycleHeadNewDominance.no_head_new_deficit_of_inward_tail
      (by omega) χ r Q hQ hQpath hQnew hno
  have h01 : R 0 ≠ R ⟨1, by omega⟩ := hR.ne (by
    intro h
    have hv : 0 = 1 := congrArg Fin.val h
    omega)
  have hpairHeads := hpair (R 0) (R ⟨1, by omega⟩) h01
  have hdegreeP : (newColors χ (R 0)).card ≤
      ((selectedGraph χ r).neighborFinset (R 0) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.castSucc i))).card := by
    rw [hprefixMap, hRzero]
    exact hheadP
  have hdegreeQ : (newColors χ (R ⟨1, by omega⟩)).card ≤
      ((selectedGraph χ r).neighborFinset (R ⟨1, by omega⟩) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.succ i))).card := by
    change (newColors χ (Q 0)).card ≤
      ((selectedGraph χ r).neighborFinset (Q 0) ∩ Finset.univ.image Q).card
    exact hheadQ
  have hdegreeSum : m + 2 ≤
      ((selectedGraph χ r).neighborFinset (R 0) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.castSucc i))).card +
      ((selectedGraph χ r).neighborFinset (R ⟨1, by omega⟩) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.succ i))).card := by omega
  obtain ⟨a, ha2, ham, hskipLeft, hskipRight⟩ :=
    ErdosProblems.AntiRamseyCycleTwoSpliceSkipExtraction.exists_two_splice_skips
      hm (selectedGraph χ r) R hR hforbidLeft hforbidRight hdegreeSum
  have hRordered : ∀ x y : Fin (m + 3), x.val + 1 = y.val →
      (selectedGraph χ r).Adj (R x) (R y) :=
    numeric_ordered_of_steps (selectedGraph χ r) R hRpath
  let closing : HostEdge n :=
    ⟨s(R 0, R (Fin.last (m + 2))), (top_adj _ _).mpr (hR.ne
      (show (0 : Fin (m + 3)) ≠ Fin.last (m + 2) from by
        intro h
        have hv : 0 = m + 2 := congrArg Fin.val h
        omega))⟩
  let e0 : (selectedGraph χ r).edgeSet := selectedPathStep χ r R hRpath 0
  have he0 : e0.val = s(R 0, R ⟨1, by omega⟩) := rfl
  have hclosing : closing.val = s(R 0, R (Fin.last (m + 2))) := rfl
  have hcolor : χ closing = restrictedColor χ r e0 :=
    ErdosProblems.AntiRamseyCycleClosingColorEquality.no_rainbow_forces_first_closing_color
      (m := m + 1) (by omega) χ r R hR hRpath closing hclosing hRnew hno
  obtain ⟨f, hf⟩ :=
    ErdosProblems.AntiRamseyCyclePartialSpliceClosing.supplied_skips_and_first_closing_color_rainbow
      χ r R hR hRordered a ha2 ham hskipLeft hskipRight e0 he0 closing hclosing hcolor
  exact hno f hf

/-- No inward orientation is assumed for the old path: first extension and
literal suffix produce it before invoking the rotating contradiction. -/
theorem ordered_path_contradiction
    {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (m + 2), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (m + 2), f i ∈ D)
    (hpair : ∀ u v : Fin n, u ≠ v →
      m + 2 ≤ (newColors χ u).card + (newColors χ v).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) : False := by
  classical
  have hpEnds : p 0 ≠ p (Fin.last (m + 1)) := hp.ne (by
    intro h
    have hv : 0 = m + 1 := congrArg Fin.val h
    omega)
  have hpairP := hpair (p 0) (p (Fin.last (m + 1))) hpEnds
  obtain ⟨R, hRpath, hR, hRD, hRnew⟩ :=
    ErdosProblems.AntiRamseyCycleFirstPathExtension.exists_inward_new_ordered_path_extension
      (t := m + 1) (by omega) χ r p hp
      (numeric_ordered_of_steps (selectedGraph χ r) p hpath) D hpD hnoD hpairP hclosed
  let Q : Fin (m + 2) → Fin n := fun i => R i.succ
  obtain ⟨hQpath, hQ, hQD, _hsame, _hinner, hQnew⟩ :=
    ErdosProblems.AntiRamseyCycleForcedTailAppendSuffix.suffix_inward_new_terminal
      χ r R hR hRpath D hRD hRnew
  exact inward_tail_contradiction hm χ r Q hQ hQpath hQnew hno D hQD hnoD hpair hclosed

end ErdosProblems.AntiRamseyCycleRotatingClaimTwo
