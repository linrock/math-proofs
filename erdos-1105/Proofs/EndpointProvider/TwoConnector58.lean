module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
Elementary two-path fans, for the structural equality direction of Erdős #58.
All witnesses are actual simple walks with explicitly controlled supports.
-/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace TwoConnector

/-- Stop a walk at its first visit to a set containing its end vertex. -/
theorem first_hit {a b : V} (p : G.Walk a b) (s : Set V) (hb : b ∈ s) :
    ∃ u ∈ s, ∃ q : G.Walk a u, ∃ r : G.Walk u b,
      p = q.append r ∧ ∀ z, z ∈ q.support → z ∈ s → z = u := by
  classical
  induction p with
  | nil =>
      exact ⟨_, hb, .nil, .nil, rfl, by simp⟩
  | @cons a c b hac p ih =>
      by_cases ha : a ∈ s
      · exact ⟨a, ha, .nil, .cons hac p, rfl, by simp⟩
      · obtain ⟨u, hu, q, r, hqr, hfirst⟩ := ih hb
        refine ⟨u, hu, .cons hac q, r, ?_, ?_⟩
        · simp only [Walk.cons_append, ← hqr]
        · intro z hz hzs
          rcases List.mem_cons.mp hz with hza | hzq
          · exact (ha (hza ▸ hzs)).elim
          · exact hfirst z hzq hzs

/-- The two halves of a simple path meet only at the splitting vertex. -/
theorem split_meet [DecidableEq V] {a b u : V} {p : G.Walk a b} (hp : p.IsPath)
    (hu : u ∈ p.support) {z : V}
    (hz₁ : z ∈ (p.takeUntil u hu).support)
    (hz₂ : z ∈ (p.dropUntil u hu).support) : z = u := by
  classical
  by_contra hzu
  have hpath : ((p.takeUntil u hu).append (p.dropUntil u hu)).IsPath := by
    simpa only [Walk.take_spec] using hp
  exact hpath.ne_of_mem_support_of_append hzu hz₁ hz₂ rfl

/-- A tripod consists of a stem and two branches, meeting only at the center. -/
structure Tripod (G : SimpleGraph V) (x b₁ b₂ v : V) where
  stem : G.Walk x v
  leg₁ : G.Walk v b₁
  leg₂ : G.Walk v b₂
  stem_path : stem.IsPath
  leg₁_path : leg₁.IsPath
  leg₂_path : leg₂.IsPath
  stem_leg₁ : ∀ z, z ∈ stem.support → z ∈ leg₁.support → z = v
  stem_leg₂ : ∀ z, z ∈ stem.support → z ∈ leg₂.support → z = v
  legs : ∀ z, z ∈ leg₁.support → z ∈ leg₂.support → z = v

theorem tripod_exists (hG : G.Connected) (x b₁ b₂ : V) :
    ∃ v, Nonempty (Tripod G x b₁ b₂ v) := by
  classical
  obtain ⟨p, hp⟩ := (hG b₁ b₂).exists_isPath
  obtain ⟨r, hr⟩ := (hG x b₁).exists_isPath
  obtain ⟨v, hv, q, t, hqt, hfirst⟩ :=
    first_hit r {z | z ∈ p.support} p.start_mem_support
  have hq : q.IsPath := by
    rw [hqt] at hr
    exact hr.of_append_left
  refine ⟨v, ⟨{
    stem := q
    leg₁ := (p.takeUntil v hv).reverse
    leg₂ := p.dropUntil v hv
    stem_path := hq
    leg₁_path := (hp.takeUntil hv).reverse
    leg₂_path := hp.dropUntil hv
    stem_leg₁ := ?_
    stem_leg₂ := ?_
    legs := ?_ }⟩⟩
  · intro z hzq hzp
    simp only [Walk.support_reverse, List.mem_reverse] at hzp
    exact hfirst z hzq (p.support_takeUntil_subset_support hv hzp)
  · intro z hzq hzp
    exact hfirst z hzq (p.support_dropUntil_subset_support hv hzp)
  · intro z hz₁ hz₂
    simp only [Walk.support_reverse, List.mem_reverse] at hz₁
    exact split_meet hp hv hz₁ hz₂

theorem path_avoiding_deleted
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b v : V} (hav : a ≠ v) (hbv : b ≠ v) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ z, z ∈ p.support → z ≠ v := by
  classical
  obtain ⟨p⟩ := hdel v ⟨a, hav⟩ ⟨b, hbv⟩
  let q : G.Walk a b := p.map (Embedding.induce {w | w ≠ v}).toHom
  refine ⟨q.bypass, q.bypass_isPath, ?_⟩
  intro z hz
  have hzq := q.support_bypass_subset_support hz
  change z ∈ (p.map (Embedding.induce {w | w ≠ v}).toHom).support at hzq
  rw [Walk.support_map] at hzq
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hzq
  exact u.property

def Tripod.swap {x b₁ b₂ v : V} (T : Tripod G x b₁ b₂ v) : Tripod G x b₂ b₁ v where
  stem := T.stem
  leg₁ := T.leg₂
  leg₂ := T.leg₁
  stem_path := T.stem_path
  leg₁_path := T.leg₂_path
  leg₂_path := T.leg₁_path
  stem_leg₁ := T.stem_leg₂
  stem_leg₂ := T.stem_leg₁
  legs := fun z hz₂ hz₁ => T.legs z hz₁ hz₂

/-- Repeated vertices in the spliced walks are bypassed. -/
theorem tripod_shift {x b₁ b₂ v w u : V} (T : Tripod G x b₁ b₂ v)
    (hw : w ∈ T.stem.support) (hu : u ∈ T.leg₁.support)
    (hwv : w ≠ v) (huv : u ≠ v) (s : G.Walk w u)
    (hsstem : ∀ z, z ∈ s.support → z ∈ T.stem.support → z = w)
    (hslegs : ∀ z, z ∈ s.support →
      (z ∈ T.leg₁.support ∨ z ∈ T.leg₂.support) → z = u) :
    ∃ U : Tripod G x b₁ b₂ w, U.stem.length < T.stem.length := by
  classical
  have hvpre : v ∉ (T.stem.takeUntil w hw).support :=
    Walk.endpoint_notMem_support_takeUntil T.stem_path hw hwv.symm
  have hvsuffix : v ∉ (T.leg₁.dropUntil u hu).support := by
    intro hv
    have heq := split_meet T.leg₁_path hu (T.leg₁.takeUntil u hu).start_mem_support hv
    exact huv heq.symm
  have hunot₂ : u ∉ T.leg₂.support := by
    intro hu₂
    exact huv (T.legs u hu hu₂)
  let p := T.stem.takeUntil w hw
  let q₁ := (s.append (T.leg₁.dropUntil u hu)).bypass
  let q₂ := ((T.stem.dropUntil w hw).append T.leg₂).bypass
  have hp : p.IsPath := T.stem_path.takeUntil hw
  have hpq₁ : ∀ z, z ∈ p.support → z ∈ q₁.support → z = w := by
    intro z hzp hzq
    have hzstem := T.stem.support_takeUntil_subset_support hw hzp
    rcases (Walk.mem_support_append_iff _ _).mp
        ((s.append (T.leg₁.dropUntil u hu)).support_bypass_subset_support hzq) with hzs | hzleg
    · exact hsstem z hzs hzstem
    · have hz₁ := T.leg₁.support_dropUntil_subset_support hu hzleg
      have hzv := T.stem_leg₁ z hzstem hz₁
      exact (hvsuffix (hzv ▸ hzleg)).elim
  have hpq₂ : ∀ z, z ∈ p.support → z ∈ q₂.support → z = w := by
    intro z hzp hzq
    change z ∈ (T.stem.takeUntil w hw).support at hzp
    rcases (Walk.mem_support_append_iff _ _).mp
        (((T.stem.dropUntil w hw).append T.leg₂).support_bypass_subset_support hzq)
        with hzstem | hzleg
    · exact split_meet T.stem_path hw hzp hzstem
    · have hzv := T.stem_leg₂ z (T.stem.support_takeUntil_subset_support hw hzp) hzleg
      exact (hvpre (hzv ▸ hzp)).elim
  have hq₁q₂ : ∀ z, z ∈ q₁.support → z ∈ q₂.support → z = w := by
    intro z hz₁ hz₂
    rcases (Walk.mem_support_append_iff _ _).mp
        ((s.append (T.leg₁.dropUntil u hu)).support_bypass_subset_support hz₁)
        with hzs | hzleg₁
    · rcases (Walk.mem_support_append_iff _ _).mp
          (((T.stem.dropUntil w hw).append T.leg₂).support_bypass_subset_support hz₂)
          with hzstem | hzleg₂
      · exact hsstem z hzs (T.stem.support_dropUntil_subset_support hw hzstem)
      · have hzu := hslegs z hzs (Or.inr hzleg₂)
        exact (hunot₂ (hzu ▸ hzleg₂)).elim
    · have hzleg := T.leg₁.support_dropUntil_subset_support hu hzleg₁
      rcases (Walk.mem_support_append_iff _ _).mp
          (((T.stem.dropUntil w hw).append T.leg₂).support_bypass_subset_support hz₂)
          with hzstem | hzleg₂
      · have hzv := T.stem_leg₁ z (T.stem.support_dropUntil_subset_support hw hzstem) hzleg
        exact (hvsuffix (hzv ▸ hzleg₁)).elim
      · have hzv := T.legs z hzleg hzleg₂
        exact (hvsuffix (hzv ▸ hzleg₁)).elim
  refine ⟨{
    stem := p
    leg₁ := q₁
    leg₂ := q₂
    stem_path := hp
    leg₁_path := (s.append (T.leg₁.dropUntil u hu)).bypass_isPath
    leg₂_path := ((T.stem.dropUntil w hw).append T.leg₂).bypass_isPath
    stem_leg₁ := hpq₁
    stem_leg₂ := hpq₂
    legs := hq₁q₂ }, ?_⟩
  exact Walk.length_takeUntil_lt_length hw hwv

theorem tripod_shortens_to_leg₁
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x b₁ b₂ v : V} (T : Tripod G x b₁ b₂ v)
    (hvx : v ≠ x) (hbv : b₁ ≠ v) :
    ∃ w, ∃ U : Tripod G x b₁ b₂ w, U.stem.length < T.stem.length := by
  classical
  obtain ⟨r, hr, havoid⟩ := path_avoiding_deleted hdel hvx.symm hbv
  obtain ⟨u, hu, q, l, hq, hfirst⟩ :=
    first_hit r {z | z ∈ T.leg₁.support ∨ z ∈ T.leg₂.support}
      (Or.inl T.leg₁.end_mem_support)
  have hqsub : ∀ z, z ∈ q.support → z ∈ r.support := by
    intro z hz
    rw [hq]
    exact Walk.support_subset_support_append_left _ _ hz
  have huv : u ≠ v := havoid u (hqsub u q.end_mem_support)
  obtain ⟨w, hw, t, k, ht, hstem⟩ :=
    first_hit q.reverse {z | z ∈ T.stem.support} T.stem.start_mem_support
  let s := t.reverse
  have hssub : ∀ z, z ∈ s.support → z ∈ q.support := by
    intro z hz
    have hzt : z ∈ t.support := by
      simpa only [s, Walk.support_reverse, List.mem_reverse] using hz
    have hzq : z ∈ q.reverse.support := by
      rw [ht]
      exact Walk.support_subset_support_append_left _ _ hzt
    simpa only [Walk.support_reverse, List.mem_reverse] using hzq
  have hwv : w ≠ v := havoid w (hqsub w (hssub w s.start_mem_support))
  have hsstem : ∀ z, z ∈ s.support → z ∈ T.stem.support → z = w := by
    intro z hz hs
    apply hstem z _ hs
    simpa only [s, Walk.support_reverse, List.mem_reverse] using hz
  have hslegs : ∀ z, z ∈ s.support →
      (z ∈ T.leg₁.support ∨ z ∈ T.leg₂.support) → z = u := by
    intro z hz hlegs
    exact hfirst z (hssub z hz) hlegs
  rcases hu with hu₁ | hu₂
  · obtain ⟨U, hU⟩ := tripod_shift T hw hu₁ hwv huv s hsstem hslegs
    exact ⟨w, U, hU⟩
  · obtain ⟨U, hU⟩ := tripod_shift T.swap hw hu₂ hwv huv s hsstem
      (fun z hz hlegs => hslegs z hz hlegs.symm)
    exact ⟨w, U.swap, hU⟩

theorem tripod_shortens
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x b₁ b₂ v : V} (T : Tripod G x b₁ b₂ v)
    (hvx : v ≠ x) (hb : b₁ ≠ b₂) :
    ∃ w, ∃ U : Tripod G x b₁ b₂ w, U.stem.length < T.stem.length := by
  by_cases hbv : b₁ = v
  · obtain ⟨w, U, hU⟩ := tripod_shortens_to_leg₁ hdel T.swap hvx (by
      intro hb₂v
      exact hb (hbv.trans hb₂v.symm))
    exact ⟨w, U.swap, hU⟩
  · exact tripod_shortens_to_leg₁ hdel T hvx hbv

end TwoConnector

/-- Two simple paths from a vertex to two distinct targets meet only at their
common starting vertex. The proof uses only connectivity after each deletion. -/
theorem twoFan (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (x b₁ b₂ : V) (hb : b₁ ≠ b₂) :
    ∃ p₁ : G.Walk x b₁, ∃ p₂ : G.Walk x b₂,
      p₁.IsPath ∧ p₂.IsPath ∧
      ∀ z, z ∈ p₁.support → z ∈ p₂.support → z = x := by
  classical
  obtain ⟨v, ⟨T⟩⟩ := TwoConnector.tripod_exists hG x b₁ b₂
  have hex : ∃ m : ℕ, ∃ v, ∃ T : TwoConnector.Tripod G x b₁ b₂ v,
      T.stem.length = m := ⟨T.stem.length, v, T, rfl⟩
  obtain ⟨v, T, hT⟩ := Nat.find_spec hex
  have hv : v = x := by
    by_contra hvx
    obtain ⟨w, U, hU⟩ := TwoConnector.tripod_shortens hdel T hvx hb
    have hmin := Nat.find_min' hex (show
      ∃ v, ∃ T : TwoConnector.Tripod G x b₁ b₂ v, T.stem.length = U.stem.length
      from ⟨w, U, rfl⟩)
    omega
  subst v
  exact ⟨T.leg₁, T.leg₂, T.leg₁_path, T.leg₂_path, T.legs⟩

namespace TwoConnector

/-- Trim a simple walk so that it visits either endpoint set only at its
corresponding endpoint. The trimmed support is contained in the original one. -/
theorem trim_between_sets {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (A B : Set V) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ a' ∈ A, ∃ b' ∈ B, ∃ q : G.Walk a' b', q.IsPath ∧
      (∀ z, z ∈ q.support → z ∈ p.support) ∧
      (∀ z, z ∈ q.support → z ∈ A → z = a') ∧
      (∀ z, z ∈ q.support → z ∈ B → z = b') := by
  classical
  obtain ⟨b', hb', q, r, hqr, hB⟩ := first_hit p B hb
  have hq : q.IsPath := by
    rw [hqr] at hp
    exact hp.of_append_left
  obtain ⟨a', ha', t, k, htk, hA⟩ := first_hit q.reverse A ha
  have ht : t.IsPath := by
    have hrev := hq.reverse
    rw [htk] at hrev
    exact hrev.of_append_left
  have hsub : ∀ z, z ∈ t.reverse.support → z ∈ q.support := by
    intro z hz
    have hzt : z ∈ t.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hz
    have hzq : z ∈ q.reverse.support := by
      rw [htk]
      exact Walk.support_subset_support_append_left _ _ hzt
    simpa only [Walk.support_reverse, List.mem_reverse] using hzq
  refine ⟨a', ha', b', hb', t.reverse, ht.reverse, ?_, ?_, ?_⟩
  · intro z hz
    rw [hqr]
    exact Walk.support_subset_support_append_left _ _ (hsub z hz)
  · intro z hz hza
    apply hA z _ hza
    simpa only [Walk.support_reverse, List.mem_reverse] using hz
  · intro z hz hzb
    exact hB z (hsub z hz) hzb

/-- Attach a path reaching one branch of a fan to that branch. -/
theorem attach_fan_leg {x c b₁ b₂ u : V}
    (p₁ : G.Walk x b₁) (p₂ : G.Walk x b₂) (hp₁ : p₁.IsPath)
    (hmeet : ∀ z, z ∈ p₁.support → z ∈ p₂.support → z = x)
    (hu : u ∈ p₁.support) (hux : u ≠ x) (q : G.Walk c u)
    (hfirst : ∀ z, z ∈ q.support →
      (z ∈ p₁.support ∨ z ∈ p₂.support) → z = u) :
    ∃ r : G.Walk c b₁, r.IsPath ∧
      ∀ z, z ∈ p₂.support → z ∈ r.support → False := by
  classical
  have hunot : u ∉ p₂.support := fun hu₂ => hux (hmeet u hu hu₂)
  have hxdrop : x ∉ (p₁.dropUntil u hu).support := by
    intro hx
    have heq := split_meet hp₁ hu (p₁.takeUntil u hu).start_mem_support hx
    exact hux heq.symm
  let r := (q.append (p₁.dropUntil u hu)).bypass
  refine ⟨r, (q.append (p₁.dropUntil u hu)).bypass_isPath, ?_⟩
  intro z hz₂ hzr
  rcases (Walk.mem_support_append_iff _ _).mp
      ((q.append (p₁.dropUntil u hu)).support_bypass_subset_support hzr)
      with hzq | hzdrop
  · have hzu := hfirst z hzq (Or.inr hz₂)
    exact hunot (hzu ▸ hz₂)
  · have hz₁ := p₁.support_dropUntil_subset_support hu hzdrop
    have hzx := hmeet z hz₁ hz₂
    exact hxdrop (hzx ▸ hzdrop)

end TwoConnector

/-- Two disjoint sets containing distinct pairs admit two vertex-disjoint
simple connectors. Each connector meets the endpoint sets only at its ends. -/
theorem twoConnectors (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (A B : Set V) (hAB : Disjoint A B)
    (hA : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂)
    (hB : ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      ∃ p₁ : G.Walk a₁ b₁, ∃ p₂ : G.Walk a₂ b₂,
        p₁.IsPath ∧ p₂.IsPath ∧
        (∀ z, z ∈ p₁.support → z ∈ p₂.support → False) ∧
        (∀ z, z ∈ p₁.support → z ∈ A → z = a₁) ∧
        (∀ z, z ∈ p₁.support → z ∈ B → z = b₁) ∧
        (∀ z, z ∈ p₂.support → z ∈ A → z = a₂) ∧
        (∀ z, z ∈ p₂.support → z ∈ B → z = b₂) := by
  classical
  obtain ⟨a₁, ha₁, a₂, ha₂, haa⟩ := hA
  obtain ⟨b₁, hb₁, b₂, hb₂, hbb⟩ := hB
  obtain ⟨p₁, p₂, hp₁, hp₂, hmeet⟩ := twoFan hG hdel a₁ b₁ b₂ hbb
  have hb₁a₁ : b₁ ≠ a₁ := by
    intro h
    subst b₁
    exact Set.disjoint_left.mp hAB ha₁ hb₁
  obtain ⟨r, hr, havoid⟩ := TwoConnector.path_avoiding_deleted hdel haa.symm hb₁a₁
  obtain ⟨u, hu, q, l, hq, hfirst⟩ :=
    TwoConnector.first_hit r {z | z ∈ p₁.support ∨ z ∈ p₂.support}
      (Or.inl p₁.end_mem_support)
  have hqsub : ∀ z, z ∈ q.support → z ∈ r.support := by
    intro z hz
    rw [hq]
    exact Walk.support_subset_support_append_left _ _ hz
  have hux : u ≠ a₁ := havoid u (hqsub u q.end_mem_support)
  have hpair : ∃ y₁ ∈ B, ∃ y₂ ∈ B,
      ∃ t₁ : G.Walk a₁ y₁, ∃ t₂ : G.Walk a₂ y₂,
        t₁.IsPath ∧ t₂.IsPath ∧
        ∀ z, z ∈ t₁.support → z ∈ t₂.support → False := by
    rcases hu with hu₁ | hu₂
    · obtain ⟨t, ht, hdisj⟩ :=
        TwoConnector.attach_fan_leg p₁ p₂ hp₁ hmeet hu₁ hux q hfirst
      exact ⟨b₂, hb₂, b₁, hb₁, p₂, t, hp₂, ht, hdisj⟩
    · obtain ⟨t, ht, hdisj⟩ :=
        TwoConnector.attach_fan_leg p₂ p₁ hp₂
          (fun z hz₂ hz₁ => hmeet z hz₁ hz₂) hu₂ hux q
          (fun z hz hlegs => hfirst z hz hlegs.symm)
      exact ⟨b₁, hb₁, b₂, hb₂, p₁, t, hp₁, ht, hdisj⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, t₁, t₂, ht₁, ht₂, hdisj⟩ := hpair
  obtain ⟨a₁', ha₁', b₁', hb₁', q₁, hq₁, hsub₁, hA₁, hB₁⟩ :=
    TwoConnector.trim_between_sets t₁ ht₁ A B ha₁ hy₁
  obtain ⟨a₂', ha₂', b₂', hb₂', q₂, hq₂, hsub₂, hA₂, hB₂⟩ :=
    TwoConnector.trim_between_sets t₂ ht₂ A B ha₂ hy₂
  have hd : ∀ z, z ∈ q₁.support → z ∈ q₂.support → False := by
    intro z hz₁ hz₂
    exact hdisj z (hsub₁ z hz₁) (hsub₂ z hz₂)
  have ha' : a₁' ≠ a₂' := by
    intro h
    exact hd a₁' q₁.start_mem_support (h.symm ▸ q₂.start_mem_support)
  have hb' : b₁' ≠ b₂' := by
    intro h
    exact hd b₁' q₁.end_mem_support (h.symm ▸ q₂.end_mem_support)
  exact ⟨a₁', ha₁', a₂', ha₂', b₁', hb₁', b₂', hb₂', ha', hb',
    q₁, q₂, hq₁, hq₂, hd, hA₁, hB₁, hA₂, hB₂⟩

end Erdos58
