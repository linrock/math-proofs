module

public import PathUpperEligibleCumulativeBirth
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
All color values and `χ` are original; the entire inside palette excludes `U`,
and initial-slot deletions and current connectedness are retained.
-/

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
