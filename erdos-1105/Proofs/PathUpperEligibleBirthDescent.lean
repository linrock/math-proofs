module

public import PathUpperEligibleConnectedReplacement
public import PathUpperBridgeCrossingNonbridgeV2
public import PathUpperCrossedBridgeCut

@[expose] public section

/-!
All color values and `χ` are original; the entire inside palette excludes `U`,
and initial-slot deletions and current connectedness are retained.
-/

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
