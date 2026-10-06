module

public import SpliceProvider.CycleJoin58
public import VineProvider.ActualBridgeFamily

@[expose] public section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.VineCycle
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem interval_getVert (P : G.Walk u v) (i j n : ℕ) (hij : i ≤ j)
    (hn : i + n ≤ j) :
    (Erdos58.pathInterval P i j hij).getVert n = P.getVert (i + n) := by
  simp only [Erdos58.pathInterval, Walk.getVert_copy, Walk.drop_getVert,
    Walk.take_getVert, Nat.min_eq_right hn]

theorem interval_support (P : G.Walk u v) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ P.length) (z : V) :
    z ∈ (Erdos58.pathInterval P i j hij).support ↔
      ∃ k, i ≤ k ∧ k ≤ j ∧ P.getVert k = z := by
  constructor
  · intro hz
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    rw [Erdos58.pathInterval_length P i j hij hj] at hnl
    have hsum : i + n ≤ j := by omega
    exact ⟨i + n, by omega, hsum, (interval_getVert P i j n hij hsum).symm.trans hn⟩
  · rintro ⟨k, hik, hkj, hk⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨k - i, ?_, ?_⟩
    · rw [interval_getVert P i j (k - i) hij (by omega)]
      simpa [Nat.add_sub_of_le hik] using hk
    · rw [Erdos58.pathInterval_length P i j hij hj]
      omega

def Interior (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l))) (l : α) : Set V :=
  {z | z ∈ (Q l).support ∧ z ≠ P.getVert (L l) ∧ z ≠ P.getVert (R l)}

theorem interval_contacts (P : G.Walk u v) (hp : P.IsPath) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ P.length) (k : ℕ) (hk : k ≤ P.length)
    (hmem : P.getVert k ∈ (Erdos58.pathInterval P i j hij).support) : i ≤ k ∧ k ≤ j := by
  obtain ⟨m, him, hmj, hmk⟩ := (interval_support P i j hij hj (P.getVert k)).mp hmem
  have : m = k := hp.getVert_injOn (show m ≤ P.length from le_trans hmj hj) hk hmk
  omega

def Rails (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (previous reach : ℕ)
    (U : G.Walk (P.getVert 0) (P.getVert previous))
    (W : G.Walk (P.getVert 0) (P.getVert reach)) : Prop :=
  U.IsPath ∧ W.IsPath ∧
  (∀ k, k ≤ P.length → P.getVert k ∈ U.support → k ≤ previous) ∧
  (∀ k, k ≤ P.length → P.getVert k ∈ W.support → k = 0 ∨ k < previous ∨ k = reach) ∧
  (∀ z, z ∈ U.support → z ∈ W.support → z = P.getVert 0) ∧
  (∀ z, z ∈ U.support ∨ z ∈ W.support → z ∉ P.support →
    ∃ l, R l ≤ reach ∧ z ∈ Interior P L R Q l)

theorem fresh_meet (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    {previous reach : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert reach)}
    (h : Rails P L R Q previous reach U W) (n : α) (hr : reach < R n)
    (z : V) (hz : z ∈ U.support ∨ z ∈ W.support) (hzn : z ∈ (Q n).support) :
    z = P.getVert (L n) ∨ z = P.getVert (R n) := by
  by_cases hpz : z ∈ P.support
  · obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hpz
    have hc := contact n k hkl (hk.symm ▸ hzn)
    rcases hc with hc | hc <;> subst k <;> simp_all
  · by_contra he
    push Not at he
    obtain ⟨l, hl, hzl⟩ := h.2.2.2.2.2 z hz hpz
    exact Set.disjoint_left.mp (separate l n (by omega)) hzl ⟨hzn, he.1, he.2⟩

theorem rails_close (P : G.Walk u v) (hp : P.IsPath) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    {previous : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert P.length)}
    (h : Rails P L R Q previous P.length U W)
    (hprev : previous < P.length) (hs : 2 ≤ P.length) :
    let S := Erdos58.pathInterval P previous P.length hprev.le
    ((U.append S).append W.reverse).IsCycle ∧
    (∀ z, z ∈ ((U.append S).append W.reverse).support ↔
      z ∈ U.support ∨ z ∈ S.support ∨ z ∈ W.support) := by
  dsimp only
  let S := Erdos58.pathInterval P previous P.length hprev.le
  have hS : S.IsPath := Erdos58.pathInterval_isPath P hp previous P.length hprev.le
  have hUS : (U.append S).IsPath := by
    apply Erdos58.path_append_of_meet_only U S h.1 hS
    intro z hz hzS
    obtain ⟨k, hkprev, hks, hk⟩ := (interval_support P previous P.length hprev.le (by omega) z).mp hzS
    have hkU := h.2.2.1 k hks (hk.symm ▸ hz)
    have : k = previous := by omega
    simpa [this] using hk.symm
  have hmeet : ∀ z, z ∈ (U.append S).support → z ∈ W.support →
      z = P.getVert 0 ∨ z = P.getVert P.length := by
    intro z hz hzW
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzU | hzS
    · exact Or.inl (h.2.2.2.2.1 z hzU hzW)
    · obtain ⟨k, hkprev, hks, hk⟩ := (interval_support P previous P.length hprev.le (by omega) z).mp hzS
      rcases h.2.2.2.1 k hks (hk.symm ▸ hzW) with hk0 | hkp | hkl
      · exact Or.inl (by simpa [hk0] using hk.symm)
      · omega
      · exact Or.inr (by simpa [hkl] using hk.symm)
  have hWpos : 1 ≤ W.length := by
    by_contra hn
    have he := Walk.eq_of_length_eq_zero (p := W) (by omega)
    have hi := hp.getVert_injOn (by simp) (by simp) he
    omega
  have hUpos : previous ≠ 0 → 1 ≤ U.length := by
    intro hne
    by_contra hn
    have he := Walk.eq_of_length_eq_zero (p := U) (by omega)
    have hi := hp.getVert_injOn (show 0 ≤ P.length from Nat.zero_le _) (show previous ≤ P.length from hprev.le) he
    omega
  have hlenS : S.length = P.length - previous :=
    Erdos58.pathInterval_length P previous P.length hprev.le (by omega)
  have hlen : 3 ≤ (U.append S).length + W.length := by
    rw [Walk.length_append, hlenS]
    by_cases he : previous = 0
    · omega
    · have := hUpos he
      omega
  refine ⟨Erdos58.cycle_of_two_paths (U.append S) W hUS h.2.1 hmeet hlen, ?_⟩
  intro z
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
  tauto

theorem rails_step (P : G.Walk u v) (hp : P.IsPath) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    {previous reach : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert reach)}
    (h : Rails P L R Q previous reach U W) (n : α)
    (ha : previous ≤ L n) (har : L n < reach) (hrb : reach < R n)
    (hb : R n ≤ P.length) :
    let S := Erdos58.pathInterval P previous (L n) ha
    Rails P L R Q reach (R n) W ((U.append S).append (Q n)) := by
  dsimp only
  let S := Erdos58.pathInterval P previous (L n) ha
  have hS : S.IsPath := Erdos58.pathInterval_isPath P hp previous (L n) ha
  have haP : L n ≤ P.length := by omega
  have hUS : (U.append S).IsPath := by
    apply Erdos58.path_append_of_meet_only U S h.1 hS
    intro z hz hzS
    obtain ⟨k, hpk, hka, hkz⟩ := (interval_support P previous (L n) ha haP z).mp hzS
    have hku := h.2.2.1 k (by omega) (hkz.symm ▸ hz)
    have : k = previous := by omega
    simpa [this] using hkz.symm
  have hUScontact : ∀ k, k ≤ P.length → P.getVert k ∈ (U.append S).support → k ≤ L n := by
    intro k hk hmem
    rcases (Walk.mem_support_append_iff _ _).mp hmem with hu | hs
    · have := h.2.2.1 k hk hu
      omega
    · exact (interval_contacts P hp previous (L n) ha haP k hk hs).2
  have hUSQ : ∀ z, z ∈ (U.append S).support → z ∈ (Q n).support → z = P.getVert (L n) := by
    intro z hz hzn
    have he : z = P.getVert (L n) ∨ z = P.getVert (R n) := by
      rcases (Walk.mem_support_append_iff _ _).mp hz with hu | hs
      · exact fresh_meet P L R Q contact separate h n hrb z (Or.inl hu) hzn
      · obtain ⟨k, hpk, hka, hkz⟩ := (interval_support P previous (L n) ha haP z).mp hs
        rcases contact n k (by omega) (hkz.symm ▸ hzn) with he | he
        · exact Or.inl (by simpa [he] using hkz.symm)
        · omega
    rcases he with he | he
    · exact he
    · have := hUScontact (R n) hb (he ▸ hz)
      omega
  have hnew : ((U.append S).append (Q n)).IsPath :=
    Erdos58.path_append_of_meet_only (U.append S) (Q n) hUS (paths n) hUSQ
  refine ⟨h.2.1, hnew, ?_, ?_, ?_, ?_⟩
  · intro k hk hmem
    rcases h.2.2.2.1 k hk hmem with he | he | he <;> omega
  · intro k hk hmem
    rcases (Walk.mem_support_append_iff _ _).mp hmem with hmem | hmem
    · have := hUScontact k hk hmem
      exact Or.inr (Or.inl (by omega))
    · rcases contact n k hk hmem with he | he
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr he)
  · intro z hzW hznew
    rcases (Walk.mem_support_append_iff _ _).mp hznew with hzUS | hzQ
    · rcases (Walk.mem_support_append_iff _ _).mp hzUS with hzU | hzS
      · exact h.2.2.2.2.1 z hzU hzW
      · obtain ⟨k, hpk, hka, hkz⟩ := (interval_support P previous (L n) ha haP z).mp hzS
        rcases h.2.2.2.1 k (by omega) (hkz.symm ▸ hzW) with he | he | he
        · simpa [he] using hkz.symm
        · omega
        · omega
    · rcases fresh_meet P L R Q contact separate h n hrb z (Or.inr hzW) hzQ with he | he
      · rcases h.2.2.2.1 (L n) haP (he ▸ hzW) with he0 | hep | her
        · simpa [he0] using he
        · omega
        · omega
      · rcases h.2.2.2.1 (R n) hb (he ▸ hzW) with he0 | hep | her <;> omega
  · intro z hz hzP
    rcases hz with hzW | hznew
    · obtain ⟨l, hl, hzl⟩ := h.2.2.2.2.2 z (Or.inr hzW) hzP
      exact ⟨l, by omega, hzl⟩
    · rcases (Walk.mem_support_append_iff _ _).mp hznew with hzUS | hzQ
      · rcases (Walk.mem_support_append_iff _ _).mp hzUS with hzU | hzS
        · obtain ⟨l, hl, hzl⟩ := h.2.2.2.2.2 z (Or.inl hzU) hzP
          exact ⟨l, by omega, hzl⟩
        · exact (hzP (Erdos58.pathInterval_support_subset P previous (L n) ha hzS)).elim
      · refine ⟨n, le_rfl, hzQ, ?_, ?_⟩
        · intro he
          exact hzP (he ▸ Walk.getVert_mem_support P (L n))
        · intro he
          exact hzP (he ▸ Walk.getVert_mem_support P (R n))

def Chain (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (previous reach : ℕ) : List α → Prop
  | [] => reach = P.length ∧ previous < reach
  | n :: ns => previous ≤ L n ∧ L n < reach ∧ reach < R n ∧ R n ≤ P.length ∧
      Chain P L R reach (R n) ns

def Covered (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (previous reach : ℕ) : List α → V → Prop
  | [], z => ∃ k, previous ≤ k ∧ k ≤ P.length ∧ P.getVert k = z
  | n :: ns, z => (∃ k, previous ≤ k ∧ k ≤ L n ∧ P.getVert k = z) ∨
      z ∈ (Q n).support ∨ Covered P L R Q reach (R n) ns z

theorem rails_finish (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (labels : List α) (previous reach : ℕ)
    (hc : Chain P L R previous reach labels)
    (U : G.Walk (P.getVert 0) (P.getVert previous))
    (W : G.Walk (P.getVert 0) (P.getVert reach))
    (h : Rails P L R Q previous reach U W) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      ∀ z, z ∈ C.support ↔ z ∈ U.support ∨ z ∈ W.support ∨
        Covered P L R Q previous reach labels z := by
  induction labels generalizing previous reach with
  | nil =>
    obtain ⟨he, hprev⟩ := hc
    subst reach
    obtain ⟨hcycle, heq⟩ := rails_close P hp L R Q h hprev hs
    refine ⟨(U.append (Erdos58.pathInterval P previous P.length hprev.le)).append W.reverse,
      hcycle, ?_⟩
    intro z
    rw [heq]
    rw [interval_support P previous P.length hprev.le le_rfl z]
    simp only [Covered]
    simp only [or_comm]
  | cons n ns ih =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    have hn := rails_step P hp L R Q paths contact separate h n ha har hrb hb
    obtain ⟨C, hC, heq⟩ := ih reach (R n) ht W
      ((U.append (Erdos58.pathInterval P previous (L n) ha)).append (Q n)) hn
    refine ⟨C, hC, ?_⟩
    intro z
    rw [heq]
    simp only [Walk.mem_support_append_iff, Covered]
    rw [interval_support P previous (L n) ha (by omega) z]
    simp only [or_assoc, or_left_comm, or_comm]

theorem rails_initial (P : G.Walk u v) (hp : P.IsPath) {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (n : α) (hL : L n = 0) :
    Rails P L R Q 0 (R n) Walk.nil ((Q n).copy (by rw [hL]) rfl) := by
  refine ⟨Walk.IsPath.nil, (by simpa only [Walk.isPath_copy] using paths n), ?_, ?_, ?_, ?_⟩
  · intro k hk hmem
    simp only [Walk.support_nil, List.mem_singleton] at hmem
    have := hp.getVert_injOn hk (show 0 ≤ P.length from Nat.zero_le _) hmem
    omega
  · intro k hk hmem
    simp only [Walk.support_copy] at hmem
    rcases contact n k hk hmem with he | he
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr he)
  · intro z hz _
    simpa only [Walk.support_nil, List.mem_singleton] using hz
  · intro z hz hzP
    rcases hz with hz | hz
    · simp only [Walk.support_nil, List.mem_singleton] at hz
      exact (hzP (hz ▸ Walk.getVert_mem_support P 0)).elim
    · simp only [Walk.support_copy] at hz
      refine ⟨n, le_rfl, hz, ?_, ?_⟩
      · intro he
        exact hzP (he ▸ Walk.getVert_mem_support P (L n))
      · intro he
        exact hzP (he ▸ Walk.getVert_mem_support P (R n))

theorem exists_spliced_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (first : α) (hL : L first = 0) (rest : List α)
    (hc : Chain P L R 0 (R first) rest) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      ∀ z, z ∈ C.support ↔ z ∈ (Q first).support ∨ Covered P L R Q 0 (R first) rest z := by
  have hi := rails_initial P hp L R Q paths contact first hL
  obtain ⟨C, hC, heq⟩ := rails_finish P hp hs L R Q paths contact separate rest 0 (R first)
    hc Walk.nil ((Q first).copy (by rw [hL]) rfl) hi
  refine ⟨C, hC, ?_⟩
  intro z
  rw [heq]
  simp only [Walk.support_nil, List.mem_singleton, Walk.support_copy]
  have hroot : P.getVert 0 ∈ (Q first).support := by
    simpa [hL] using (Q first).start_mem_support
  constructor
  · rintro (he | hz | hz)
    · exact Or.inl (he.symm ▸ hroot)
    · exact Or.inl hz
    · exact Or.inr hz
  · intro hz
    exact Or.inr hz

theorem chain_of_greedy (P : G.Walk u v) {α : Type*} (L R : α → ℕ)
    (F : Finset IntervalVine.Interval) (labels : List α) (previous certificatePrevious reach : ℕ)
    (ht : IntervalVine.GreedyTail F P.length certificatePrevious reach
      (labels.map (fun l => (L l, R l))))
    (hle : previous ≤ certificatePrevious) (hpr : previous < reach) :
    Chain P L R previous reach labels := by
  induction labels generalizing previous certificatePrevious reach with
  | nil =>
    cases ht
    exact ⟨rfl, hpr⟩
  | cons n ns ih =>
    cases ht with
    | step cp reach I rest hmem hleft hcross hadv hbound hmax htie tail =>
      refine ⟨le_trans hle hleft, hcross, hadv, hbound, ?_⟩
      exact ih reach reach (R n) tail le_rfl hadv

theorem actual_family_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    (L R : ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val) →
      Fin (P.length + 1))
    (Q : ∀ l, G.Walk (P.getVert (L l).val) (P.getVert (R l).val))
    (hd : ActualBridgeFamily.Data (fun j : Fin (P.length + 1) => P.getVert j.val) L R Q)
    (first : ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val))
    (hL : (L first).val = 0)
    (rest : List (ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val)))
    (F : Finset IntervalVine.Interval)
    (ht : IntervalVine.GreedyTail F P.length 1 (R first).val
      (rest.map (fun l => ((L l).val, (R l).val)))) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      ∀ z, z ∈ C.support ↔ z ∈ (Q first).support ∨
        Covered P (fun l => (L l).val) (fun l => (R l).val) Q 0 (R first).val rest z := by
  have hpositive : 0 < (R first).val := by
    have := (hd.1 first)
    change (L first).val < (R first).val at this
    omega
  apply exists_spliced_cycle P hp hs (fun l => (L l).val) (fun l => (R l).val) Q
    (fun l => (hd.2.1 l).1) ?_ ?_ first hL rest
    (chain_of_greedy P (fun l => (L l).val) (fun l => (R l).val) F rest 0 1
      (R first).val ht (by omega) hpositive)
  · intro l k hk hmem
    have he := (hd.2.1 l).2 (⟨k, by omega⟩ : Fin (P.length + 1)) hmem
    rcases he with he | he
    · exact Or.inl (congrArg Fin.val he)
    · exact Or.inr (congrArg Fin.val he)
  · intro l r hlr
    simpa only [Interior] using hd.2.2.2.2.2 l r hlr

theorem exists_actual_vine_cycle [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hs : 2 ≤ P.length)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (a b : Fin (P.length + 1)) (ha : 0 < a) (hb : b < Fin.last P.length)
    (hfirstEdge : G.Adj (P.getVert 0) (P.getVert a.val))
    (hlastEdge : G.Adj (P.getVert b.val) (P.getVert P.length)) :
    ∃ L R : ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val) →
      Fin (P.length + 1),
    ∃ Q : ∀ l, G.Walk (P.getVert (L l).val) (P.getVert (R l).val),
    ∃ first, ∃ rest : List (ActualBridgeFamily.Label (fun j : Fin (P.length + 1) => P.getVert j.val)),
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0),
      ActualBridgeFamily.Data (fun j : Fin (P.length + 1) => P.getVert j.val) L R Q ∧
      (L first).val = 0 ∧ C.IsCycle ∧
      (∀ z, z ∈ C.support ↔ z ∈ (Q first).support ∨
        Covered P (fun l => (L l).val) (fun l => (R l).val) Q 0 (R first).val rest z) := by
  have hinj : Function.Injective (fun j : Fin (P.length + 1) => P.getVert j.val) := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) he
  obtain ⟨L, R, Q, hd, F, fi, intervals, labels, _, _, _, _, hzero, _, _, ht, hmap, _⟩ :=
    ActualBridgeFamily.exists_actual_interval_vine (G := G)
      (fun j : Fin (P.length + 1) => P.getVert j.val) hinj hs hdel a b ha hb
      hfirstEdge hlastEdge
  cases labels with
  | nil => simp at hmap
  | cons first rest =>
    simp only [List.map_cons] at hmap
    obtain ⟨hfi, hrest⟩ := List.cons.inj hmap
    have hL : (L first).val = 0 := (congrArg Prod.fst hfi).trans hzero
    have htail : IntervalVine.GreedyTail F P.length 1 (R first).val
        (rest.map (fun l => ((L l).val, (R l).val))) := by
      have hR : (R first).val = fi.2 := congrArg Prod.snd hfi
      rw [hrest, hR]
      exact ht
    obtain ⟨C, hC, hsupport⟩ := actual_family_cycle P hp hs L R Q hd first hL rest F htail
    exact ⟨L, R, Q, first, rest, C, hd, hL, hC, hsupport⟩

end ErdosProblems.PathUpperReduction.VineCycle
