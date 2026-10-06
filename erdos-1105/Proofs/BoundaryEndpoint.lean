module

public import CrossingProvider.VineCycle
public import Mathlib.Order.Interval.Finset.Nat
public import CrossingEndpoint

@[expose] public section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.BoundaryEndpoint
open VineCycle CrossingEndpoint
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem terminal_fusion (P : G.Walk u v) (hp : P.IsPath) {α : Type*}
    (L R : α → ℕ) (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    {previous reach : ℕ} {U : G.Walk (P.getVert 0) (P.getVert previous)}
    {W : G.Walk (P.getVert 0) (P.getVert reach)}
    (h : Rails P L R Q previous reach U W)
    (hpr : previous < reach) (hrs : reach < P.length) (b : ℕ)
    (hpb : previous ≤ b) (hbr : b < reach)
    (he : G.Adj (P.getVert b) (P.getVert P.length)) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ z, z ∈ U.support ∨ z ∈ W.support → z ∈ C.support) ∧
      (∀ k, (previous ≤ k ∧ k ≤ b) ∨ (reach ≤ k ∧ k ≤ P.length) →
        P.getVert k ∈ C.support) := by
  let S := Erdos58.pathInterval P previous b hpb
  let T := Erdos58.pathInterval P reach P.length hrs.le
  let E := he.toWalk
  have hS : S.IsPath := Erdos58.pathInterval_isPath P hp previous b hpb
  have hT : T.IsPath := Erdos58.pathInterval_isPath P hp reach P.length hrs.le
  have hbP : b ≤ P.length := by omega
  have hUS : (U.append S).IsPath := by
    apply Erdos58.path_append_of_meet_only U S h.1 hS
    intro z hz hzS
    obtain ⟨k, hpk, hkb, hkz⟩ := (interval_support P previous b hpb hbP z).mp hzS
    have := h.2.2.1 k (by omega) (hkz.symm ▸ hz)
    have : k = previous := by omega
    simpa [this] using hkz.symm
  have hUScontact : ∀ k, k ≤ P.length → P.getVert k ∈ (U.append S).support → k ≤ b := by
    intro k hk hmem
    rcases (Walk.mem_support_append_iff _ _).mp hmem with hmem | hmem
    · have := h.2.2.1 k hk hmem
      omega
    · exact (interval_contacts P hp previous b hpb hbP k hk hmem).2
  have hUSE : ((U.append S).append E).IsPath := by
    apply Erdos58.path_append_of_meet_only (U.append S) E hUS he.isPath_toWalk
    intro z hz hzE
    simp only [E, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
    rcases hzE with hzE | hzE
    · exact hzE
    · have := hUScontact P.length le_rfl (hzE ▸ hz)
      omega
  have hWT : (W.append T).IsPath := by
    apply Erdos58.path_append_of_meet_only W T h.2.1 hT
    intro z hz hzT
    obtain ⟨k, hrk, hks, hkz⟩ := (interval_support P reach P.length hrs.le le_rfl z).mp hzT
    rcases h.2.2.2.1 k hks (hkz.symm ▸ hz) with he0 | hep | her
    · omega
    · omega
    · simpa [her] using hkz.symm
  let A := (U.append S).append E
  let B := W.append T
  have hmeet : ∀ z, z ∈ A.support → z ∈ B.support →
      z = P.getVert 0 ∨ z = P.getVert P.length := by
    intro z hzA hzB
    rcases (Walk.mem_support_append_iff _ _).mp hzA with hzUS | hzE
    · rcases (Walk.mem_support_append_iff _ _).mp hzB with hzW | hzT
      · rcases (Walk.mem_support_append_iff _ _).mp hzUS with hzU | hzS
        · exact Or.inl (h.2.2.2.2.1 z hzU hzW)
        · obtain ⟨k, hpk, hkb, hkz⟩ := (interval_support P previous b hpb hbP z).mp hzS
          rcases h.2.2.2.1 k (by omega) (hkz.symm ▸ hzW) with he0 | hep | her
          · exact Or.inl (by simpa [he0] using hkz.symm)
          · omega
          · omega
      · obtain ⟨k, hrk, hks, hkz⟩ := (interval_support P reach P.length hrs.le le_rfl z).mp hzT
        have := hUScontact k hks (hkz.symm ▸ hzUS)
        omega
    · simp only [E, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
      rcases hzE with hzE | hzE
      · rcases (Walk.mem_support_append_iff _ _).mp hzB with hzW | hzT
        · rcases h.2.2.2.1 b hbP (hzE ▸ hzW) with he0 | hep | her
          · exact Or.inl (by simpa [he0] using hzE)
          · omega
          · omega
        · have := (interval_contacts P hp reach P.length hrs.le le_rfl b hbP (hzE ▸ hzT)).1
          omega
      · exact Or.inr hzE
  have hWpos : 1 ≤ W.length := by
    by_contra hn
    have heq := Walk.eq_of_length_eq_zero (p := W) (by omega)
    have := hp.getVert_injOn (show 0 ≤ P.length from Nat.zero_le _) hrs.le heq
    omega
  have hTlen : T.length = P.length - reach :=
    Erdos58.pathInterval_length P reach P.length hrs.le le_rfl
  have hlen : 3 ≤ A.length + B.length := by
    simp only [A, B, E, Walk.length_append, Adj.length_toWalk]
    omega
  let C := A.append B.reverse
  refine ⟨C, Erdos58.cycle_of_two_paths A B hUSE hWT hmeet hlen, ?_, ?_⟩
  · intro z hz
    simp only [C, A, B, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
    tauto
  · intro k hk
    rcases hk with hk | hk
    · have hm : P.getVert k ∈ S.support :=
        (interval_support P previous b hpb hbP (P.getVert k)).mpr ⟨k, hk.1, hk.2, rfl⟩
      simp only [C, A, B, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
      tauto
    · have hm : P.getVert k ∈ T.support :=
        (interval_support P reach P.length hrs.le le_rfl (P.getVert k)).mpr ⟨k, hk.1, hk.2, rfl⟩
      simp only [C, A, B, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
      tauto

theorem boundary_finish (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (B : Finset ℕ) (hBP : ∀ b ∈ B, b < P.length)
    (hedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (n : α) (ns : List α) (previous reach : ℕ)
    (hc : Chain P L R previous reach (n :: ns))
    (hterminal : ∀ l ∈ n :: ns, R l = P.length → ∀ b ∈ B, L l ≤ b)
    (U : G.Walk (P.getVert 0) (P.getVert previous))
    (W : G.Walk (P.getVert 0) (P.getVert reach))
    (h : Rails P L R Q previous reach U W) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ z, z ∈ U.support ∨ z ∈ W.support → z ∈ C.support) ∧
      (∀ b ∈ B, P.getVert b ∈ C.support) ∧
      (∀ k, previous ≤ k ∧ k ≤ L n → P.getVert k ∈ C.support) ∧
      P.getVert P.length ∈ C.support := by
  classical
  induction ns generalizing n previous reach with
  | nil =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    have hlast : R n = P.length := ht.1
    have hpr : previous < reach := by omega
    have hrs : reach < P.length := by omega
    let F := B.filter (fun b => b < reach)
    by_cases hF : F.Nonempty
    · obtain ⟨b, hbF, hmax⟩ := Finset.exists_max_image F id hF
      obtain ⟨hbB, hbr⟩ := Finset.mem_filter.mp hbF
      have hnb : L n ≤ b := hterminal n (by simp) hlast b hbB
      obtain ⟨C, hC, hold, hindex⟩ := terminal_fusion P hp L R Q h hpr hrs b
        (by omega) hbr (hedge b hbB)
      refine ⟨C, hC, hold, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hkr : k < reach
        · have hkb : k ≤ b := hmax k (Finset.mem_filter.mpr ⟨hk, hkr⟩)
          have hnk := hterminal n (by simp) hlast k hk
          exact hindex k (Or.inl ⟨by omega, hkb⟩)
        · exact hindex k (Or.inr ⟨by omega, (hBP k hk).le⟩)
      · intro k hk
        exact hindex k (Or.inl ⟨hk.1, le_trans hk.2 hnb⟩)
      · exact hindex P.length (Or.inr ⟨hrs.le, le_rfl⟩)
    · obtain ⟨C, hC, hsupport⟩ := rails_finish P hp hs L R Q paths contact separate
        [n] previous reach ⟨ha, har, hrb, hb, ht⟩ U W h
      refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
      · intro z hz
        apply (hsupport z).mpr
        tauto
      · intro b hbB
        have hrb' : reach ≤ b := by
          by_contra he
          apply hF
          exact ⟨b, Finset.mem_filter.mpr ⟨hbB, by omega⟩⟩
        apply (hsupport (P.getVert b)).mpr
        right; right; right; right
        exact ⟨b, hrb', (hBP b hbB).le, rfl⟩
      · intro k hk
        apply (hsupport (P.getVert k)).mpr
        right; right; left
        exact ⟨k, hk.1, hk.2, rfl⟩
      · apply (hsupport (P.getVert P.length)).mpr
        right; right; right; right
        exact ⟨P.length, hrs.le, le_rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    let S := Erdos58.pathInterval P previous (L n) ha
    have hn := rails_step P hp L R Q paths contact separate h n ha har hrb hb
    have htail : ∀ l ∈ m :: ms, R l = P.length → ∀ b ∈ B, L l ≤ b := by
      intro l hl he b hbB
      exact hterminal l (List.mem_cons_of_mem n hl) he b hbB
    obtain ⟨C, hC, hold, hB, _, hend⟩ := ih m reach (R n) ht htail W
      ((U.append S).append (Q n)) hn
    refine ⟨C, hC, ?_, hB, ?_, hend⟩
    · intro z hz
      apply hold z
      rcases hz with hzU | hzW
      · right
        simp only [Walk.mem_support_append_iff]
        tauto
      · exact Or.inl hzW
    · intro k hk
      have hm : P.getVert k ∈ S.support :=
        (interval_support P previous (L n) ha (by omega) (P.getVert k)).mpr
          ⟨k, hk.1, hk.2, rfl⟩
      apply hold (P.getVert k)
      right
      simp only [Walk.mem_support_append_iff]
      tauto

theorem first_modified_rails (P : G.Walk u v) (hp : P.IsPath) {α : Type*}
    (L R : α → ℕ) (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (first second : α) (hL : L first = 0)
    (hcross : L second < R first) (hrr : R first < R second) (hb : R second ≤ P.length)
    (a : ℕ) (hla : L second < a) (har : a ≤ R first)
    (he : G.Adj (P.getVert 0) (P.getVert a)) :
    ∃ U : G.Walk (P.getVert 0) (P.getVert (R first)),
    ∃ W : G.Walk (P.getVert 0) (P.getVert (R second)),
      Rails P L R Q (R first) (R second) U W ∧
      ∀ k, k ≤ L second ∨ (a ≤ k ∧ k ≤ R first) →
        P.getVert k ∈ U.support ∨ P.getVert k ∈ W.support := by
  let S := Erdos58.pathInterval P 0 (L second) (Nat.zero_le _)
  let W := (Walk.nil.append S).append (Q second)
  let T := Erdos58.pathInterval P a (R first) har
  let U := he.toWalk.append T
  have hrP : R first ≤ P.length := by omega
  have hlP : L second ≤ P.length := by omega
  have haP : a ≤ P.length := by omega
  have ha0 : 0 < a := by omega
  have hi := rails_initial P hp L R Q paths contact first hL
  have hbase : Rails P L R Q (R first) (R second)
      ((Q first).copy (by rw [hL]) rfl) W :=
    rails_step P hp L R Q paths contact separate hi second (Nat.zero_le _) hcross hrr hb
  have hT : T.IsPath := Erdos58.pathInterval_isPath P hp a (R first) har
  have hU : U.IsPath := by
    apply Erdos58.path_append_of_meet_only he.toWalk T he.isPath_toWalk hT
    intro z hz hzT
    simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · obtain ⟨k, hak, hkr, hkz⟩ := (interval_support P a (R first) har hrP z).mp hzT
      have := hp.getVert_injOn (show k ≤ P.length from le_trans hkr hrP)
        (show 0 ≤ P.length from Nat.zero_le _) (hkz.trans hz)
      omega
    · exact hz
  have hUsupport : ∀ z, z ∈ U.support →
      z = P.getVert 0 ∨ ∃ k, a ≤ k ∧ k ≤ R first ∧ P.getVert k = z := by
    intro z hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzE | hzT
    · simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hzE
      rcases hzE with hzE | hzE
      · exact Or.inl hzE
      · exact Or.inr ⟨a, le_rfl, har, hzE.symm⟩
    · exact Or.inr ((interval_support P a (R first) har hrP z).mp hzT)
  have hWcontact : ∀ k, k ≤ P.length → P.getVert k ∈ W.support →
      k ≤ L second ∨ k = R second := by
    intro k hk hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzS | hzQ
    · rcases (Walk.mem_support_append_iff _ _).mp hzS with hz0 | hzS
      · simp only [Walk.support_nil, List.mem_singleton] at hz0
        have := hp.getVert_injOn hk (show 0 ≤ P.length from Nat.zero_le _) hz0
        exact Or.inl (by omega)
      · exact Or.inl ((interval_contacts P hp 0 (L second) (Nat.zero_le _) hlP k hk hzS).2)
    · rcases contact second k hk hzQ with heL | heR
      · exact Or.inl heL.le
      · exact Or.inr heR
  refine ⟨U, W, ⟨hU, hbase.2.1, ?_, hbase.2.2.2.1, ?_, ?_⟩, ?_⟩
  · intro k hk hz
    rcases hUsupport (P.getVert k) hz with he0 | ⟨j, haj, hjr, hjk⟩
    · have := hp.getVert_injOn hk (show 0 ≤ P.length from Nat.zero_le _) he0
      omega
    · have := hp.getVert_injOn (show j ≤ P.length from le_trans hjr hrP) hk hjk
      omega
  · intro z hzU hzW
    rcases hUsupport z hzU with he0 | ⟨k, hak, hkr, hkz⟩
    · exact he0
    · rcases hWcontact k (by omega) (hkz.symm ▸ hzW) with hkL | hkR <;> omega
  · intro z hz hzP
    rcases hz with hzU | hzW
    · rcases hUsupport z hzU with he0 | ⟨k, _, _, hkz⟩
      · exact (hzP (he0 ▸ Walk.getVert_mem_support P 0)).elim
      · exact (hzP (hkz ▸ Walk.getVert_mem_support P k)).elim
    · exact hbase.2.2.2.2.2 z (Or.inr hzW) hzP
  · intro k hk
    rcases hk with hkL | hkA
    · have hm : P.getVert k ∈ S.support :=
        (interval_support P 0 (L second) (Nat.zero_le _) hlP (P.getVert k)).mpr
          ⟨k, Nat.zero_le _, hkL, rfl⟩
      right
      simp only [W, Walk.mem_support_append_iff]
      tauto
    · have hm : P.getVert k ∈ T.support :=
        (interval_support P a (R first) har hrP (P.getVert k)).mpr ⟨k, hkA.1, hkA.2, rfl⟩
      left
      exact (Walk.mem_support_append_iff _ _).mpr (Or.inr hm)

theorem noncrossing_vine_cycle (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    {α : Type*} (L R : α → ℕ)
    (Q : ∀ l, G.Walk (P.getVert (L l)) (P.getVert (R l)))
    (paths : ∀ l, (Q l).IsPath)
    (contact : ∀ l k, k ≤ P.length → P.getVert k ∈ (Q l).support → k = L l ∨ k = R l)
    (separate : ∀ l r, R l < R r → Disjoint (Interior P L R Q l) (Interior P L R Q r))
    (first : α) (hL : L first = 0) (rest : List α)
    (hc : Chain P L R 0 (R first) rest)
    (A B : Finset ℕ) (hreach : ∀ a ∈ A, a ≤ R first)
    (hBP : ∀ b ∈ B, b < P.length)
    (hAedge : ∀ a ∈ A, G.Adj (P.getVert 0) (P.getVert a))
    (hBedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (hterminal : ∀ l ∈ rest, R l = P.length → ∀ b ∈ B, L l ≤ b) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ a ∈ A, P.getVert a ∈ C.support) ∧
      (∀ b ∈ B, P.getVert b ∈ C.support) ∧ P.getVert P.length ∈ C.support := by
  classical
  cases rest with
  | nil =>
    have hright : R first = P.length := hc.1
    obtain ⟨C, hC, hsupport⟩ := exists_spliced_cycle P hp hs L R Q paths contact separate
      first hL [] hc
    have hall : ∀ k, k ≤ P.length → P.getVert k ∈ C.support := by
      intro k hk
      apply (hsupport (P.getVert k)).mpr
      right
      exact ⟨k, Nat.zero_le _, hk, rfl⟩
    refine ⟨C, hC, ?_, ?_, hall P.length le_rfl⟩
    · intro a ha
      exact hall a (by have := hreach a ha; omega)
    · intro b hb
      exact hall b (hBP b hb).le
  | cons second ns =>
    obtain ⟨ha, har, hrb, hb, ht⟩ := hc
    let F := A.filter (fun a => L second < a)
    by_cases hF : F.Nonempty
    · obtain ⟨a, haF, hmin⟩ := Finset.exists_min_image F id hF
      obtain ⟨haA, hla⟩ := Finset.mem_filter.mp haF
      have ham : ∀ k ∈ A, L second < k → a ≤ k := by
        intro k hk hkl
        exact hmin k (Finset.mem_filter.mpr ⟨hk, hkl⟩)
      obtain ⟨U, W, hrails, hcover⟩ := first_modified_rails P hp L R Q paths contact separate
        first second hL har hrb hb a hla (hreach a haA) (hAedge a haA)
      cases ns with
      | nil =>
        have hright : R second = P.length := ht.1
        let W' := W.copy rfl (congrArg P.getVert hright)
        have hrails' : Rails P L R Q (R first) P.length U W' := by
          simpa only [Rails, W', Walk.support_copy, Walk.isPath_copy, hright] using hrails
        have hprev : R first < P.length := by omega
        let S := Erdos58.pathInterval P (R first) P.length hprev.le
        let C := (U.append S).append W'.reverse
        obtain ⟨hC, hsupport⟩ := rails_close P hp L R Q hrails' hprev hs
        have hkeep : ∀ k, k ≤ L second ∨ (a ≤ k ∧ k ≤ R first) → P.getVert k ∈ C.support := by
          intro k hk
          rcases hcover k hk with hu | hw
          · exact (hsupport (P.getVert k)).mpr (Or.inl hu)
          · have hw' : P.getVert k ∈ W'.support := by simpa only [W', Walk.support_copy] using hw
            exact (hsupport (P.getVert k)).mpr (Or.inr (Or.inr hw'))
        have hsuffix : ∀ k, R first ≤ k → k ≤ P.length → P.getVert k ∈ C.support := by
          intro k hk hkP
          apply (hsupport (P.getVert k)).mpr
          right; left
          exact (interval_support P (R first) P.length hprev.le le_rfl (P.getVert k)).mpr
            ⟨k, hk, hkP, rfl⟩
        refine ⟨C, hC, ?_, ?_, hsuffix P.length hprev.le le_rfl⟩
        · intro k hk
          by_cases hkL : k ≤ L second
          · exact hkeep k (Or.inl hkL)
          · exact hkeep k (Or.inr ⟨ham k hk (by omega), hreach k hk⟩)
        · intro b hbB
          by_cases hbr : b ≤ R first
          · exact hkeep b (Or.inr ⟨hAB a haA b hbB, hbr⟩)
          · exact hsuffix b (by omega) (hBP b hbB).le
      | cons n ns =>
        have hterm : ∀ l ∈ n :: ns, R l = P.length → ∀ b ∈ B, L l ≤ b := by
          intro l hl he b hbB
          exact hterminal l (List.mem_cons_of_mem second hl) he b hbB
        obtain ⟨C, hC, hold, hB, _, hend⟩ := boundary_finish P hp hs L R Q paths contact separate
          B hBP hBedge n ns (R first) (R second) ht hterm U W hrails
        refine ⟨C, hC, ?_, hB, hend⟩
        intro k hk
        apply hold (P.getVert k)
        by_cases hkL : k ≤ L second
        · exact hcover k (Or.inl hkL)
        · exact hcover k (Or.inr ⟨ham k hk (by omega), hreach k hk⟩)
    · let W := (Q first).copy (by rw [hL]) rfl
      have hi := rails_initial P hp L R Q paths contact first hL
      obtain ⟨C, hC, _, hB, hprefix, hend⟩ := boundary_finish P hp hs L R Q paths contact separate
        B hBP hBedge second ns 0 (R first) ⟨ha, har, hrb, hb, ht⟩ hterminal Walk.nil W hi
      refine ⟨C, hC, ?_, hB, hend⟩
      intro a haA
      apply hprefix a
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra he
      exact hF ⟨a, Finset.mem_filter.mpr ⟨haA, by omega⟩⟩

theorem exists_actual_noncrossing_cycle [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hs : 2 ≤ P.length)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAP : ∀ a ∈ A, 0 < a ∧ a < P.length)
    (hBP : ∀ b ∈ B, 0 < b ∧ b < P.length)
    (hAedge : ∀ a ∈ A, G.Adj (P.getVert 0) (P.getVert a))
    (hBedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧
      (∀ a ∈ A, P.getVert a ∈ C.support) ∧
      (∀ b ∈ B, P.getVert b ∈ C.support) ∧ P.getVert P.length ∈ C.support := by
  classical
  obtain ⟨a, haA, hmax⟩ := Finset.exists_max_image A id hA
  obtain ⟨b, hbB, hmin⟩ := Finset.exists_min_image B id hB
  let af : Fin (P.length + 1) := ⟨a, by have := hAP a haA; omega⟩
  let bf : Fin (P.length + 1) := ⟨b, by have := hBP b hbB; omega⟩
  have haf : 0 < af := by exact (hAP a haA).1
  have hbf : bf < Fin.last P.length := by exact (hBP b hbB).2
  have hinj : Function.Injective (fun j : Fin (P.length + 1) => P.getVert j.val) := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) he
  obtain ⟨L, R, Q, hd, F, fi, intervals, labels, _, _, _, _, hzero, hreach, _,
    ht, hmap, _, _, _, _, _, hterminal⟩ :=
    ActualBridgeFamily.exists_actual_interval_vine (G := G)
      (fun j : Fin (P.length + 1) => P.getVert j.val) hinj hs hdel af bf haf hbf
      (hAedge a haA) (hBedge b hbB)
  cases labels with
  | nil => simp at hmap
  | cons first rest =>
    simp only [List.map_cons] at hmap
    obtain ⟨hfi, hrest⟩ := List.cons.inj hmap
    have hL : (L first).val = 0 := (congrArg Prod.fst hfi).trans hzero
    have hR : (R first).val = fi.2 := congrArg Prod.snd hfi
    have htail : IntervalVine.GreedyTail F P.length 1 (R first).val
        (rest.map (fun l => ((L l).val, (R l).val))) := by
      rw [hrest, hR]
      exact ht
    have hpositive : 0 < (R first).val := by
      have hlt := hd.1 first
      change (L first).val < (R first).val at hlt
      omega
    have hc := chain_of_greedy P (fun l => (L l).val) (fun l => (R l).val)
      F rest 0 1 (R first).val htail (by omega) hpositive
    have hfirst : ∀ k ∈ A, k ≤ (R first).val := by
      intro k hk
      have hkmax : k ≤ a := hmax k hk
      change a ≤ fi.2 at hreach
      omega
    have hterm : ∀ l ∈ rest, (R l).val = P.length → ∀ k ∈ B, (L l).val ≤ k := by
      intro l hl he k hk
      have hleft := hterminal l (List.mem_cons_of_mem first hl) he
      change (L l).val ≤ b at hleft
      have hbmin : b ≤ k := hmin k hk
      omega
    apply noncrossing_vine_cycle P hp hs (fun l => (L l).val) (fun l => (R l).val) Q
      (fun l => (hd.2.1 l).1) ?_ ?_ first hL rest hc A B hfirst
      (fun k hk => (hBP k hk).2) hAedge hBedge hAB hterm
    · intro l k hk hmem
      have he := (hd.2.1 l).2 (⟨k, by omega⟩ : Fin (P.length + 1)) hmem
      rcases he with he | he
      · exact Or.inl (congrArg Fin.val he)
      · exact Or.inr (congrArg Fin.val he)
    · intro l r hlr
      simpa only [Interior] using hd.2.2.2.2.2 l r hlr

theorem cycle_vertex_card {x : V} (C : G.Walk x x) (hC : C.IsCycle) :
    letI := Classical.decEq V
    C.support.toFinset.card = C.length := by
  classical
  have heq : C.support.toFinset = C.tail.support.toFinset := by
    rw [← Walk.cons_support_tail (p := C) hC.not_nil]
    simp only [List.toFinset_cons]
    exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr C.tail.end_mem_support)
  rw [heq, List.toFinset_card_of_nodup hC.isPath_tail.support_nodup, Walk.length_support,
    Walk.length_tail_add_one hC.not_nil]

theorem protected_neighbor_count (P : G.Walk u v) (hp : P.IsPath) (hs : 2 ≤ P.length)
    (A B : Finset ℕ) (hAP : ∀ a ∈ A, 0 < a ∧ a < P.length)
    (hBP : ∀ b ∈ B, 0 < b ∧ b < P.length)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (C : G.Walk (P.getVert 0) (P.getVert 0)) (hC : C.IsCycle)
    (hA : ∀ a ∈ A, P.getVert a ∈ C.support)
    (hB : ∀ b ∈ B, P.getVert b ∈ C.support)
    (hend : P.getVert P.length ∈ C.support) :
    A.card + B.card + 1 ≤ C.length := by
  classical
  have hinter : (A ∩ B).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haA, haB⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbA, hbB⟩ := Finset.mem_inter.mp hb
    exact Nat.le_antisymm (hAB a haA b hbB) (hAB b hbA a haB)
  have hzero : 0 ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have := hAP 0 hz
      omega
    · have := hBP 0 hz
      omega
  have hlast : P.length ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have := hAP P.length hz
      omega
    · have := hBP P.length hz
      omega
  let E := insert 0 (insert P.length (A ∪ B))
  have hcard : E.card = (A ∪ B).card + 2 := by
    have hzero' : 0 ∉ insert P.length (A ∪ B) := by simp [hzero]; omega
    simp only [E, Finset.card_insert_of_notMem hzero', Finset.card_insert_of_notMem hlast]
  have hbound : ∀ k ∈ E, k ≤ P.length := by
    intro k hk
    rcases Finset.mem_insert.mp hk with he0 | hk
    · omega
    · rcases Finset.mem_insert.mp hk with hes | hk
      · omega
      · rcases Finset.mem_union.mp hk with hk | hk
        · exact (hAP k hk).2.le
        · exact (hBP k hk).2.le
  have himage : (E.image P.getVert).card = E.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact hp.getVert_injOn (hbound i hi) (hbound j hj) he
  have hsubset : E.image P.getVert ⊆ C.support.toFinset := by
    intro z hz
    obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
    apply List.mem_toFinset.mpr
    subst z
    rcases Finset.mem_insert.mp hk with he0 | hk
    · exact he0 ▸ C.start_mem_support
    · rcases Finset.mem_insert.mp hk with hes | hk
      · exact hes ▸ hend
      · rcases Finset.mem_union.mp hk with hk | hk
        · exact hA k hk
        · exact hB k hk
  have hle := Finset.card_le_card hsubset
  rw [himage, hcard, cycle_vertex_card C hC] at hle
  have hledger := Finset.card_union_add_card_inter A B
  omega

theorem exists_actual_noncrossing_threshold [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hs : 2 ≤ P.length)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAP : ∀ a ∈ A, 0 < a ∧ a < P.length)
    (hBP : ∀ b ∈ B, 0 < b ∧ b < P.length)
    (hAedge : ∀ a ∈ A, G.Adj (P.getVert 0) (P.getVert a))
    (hBedge : ∀ b ∈ B, G.Adj (P.getVert b) (P.getVert P.length))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ A.card + B.card + 1 ≤ C.length := by
  obtain ⟨C, hC, hAcover, hBcover, hend⟩ := exists_actual_noncrossing_cycle P hp hs hdel
    A B hA hB hAP hBP hAedge hBedge hAB
  exact ⟨C, hC, protected_neighbor_count P hp hs A B hAP hBP hAB C hC hAcover hBcover hend⟩

theorem uniform_endpoint_threshold [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1)
    (hKD : K ≤ (LeftNeighbors P).card + (RightNeighbors P).card) :
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  have hs : 2 ≤ P.length := by omega
  by_cases he : G.Adj (P.getVert 0) (P.getVert P.length)
  · exact endpoint_crossing_branch P hp K hK hKs hKD (Or.inl he)
  · by_cases hcross : ∃ i ∈ LeftNeighbors P, ∃ j ∈ RightNeighbors P, j < i
    · exact endpoint_crossing_branch P hp K hK hKs hKD (Or.inr hcross)
    · obtain ⟨hAinternal, hBinternal⟩ := neighbors_internal P he
      have hA : (LeftNeighbors P).Nonempty := by
        refine ⟨1, (mem_left P 1).mpr ⟨by omega, ?_⟩⟩
        exact P.adj_getVert_succ (i := 0) (by omega)
      have hB : (RightNeighbors P).Nonempty := by
        refine ⟨P.length - 1, (mem_right P (P.length - 1)).mpr ⟨by omega, ?_⟩⟩
        have hedge := P.adj_getVert_succ (i := P.length - 1) (by omega)
        have hindex : P.length - 1 + 1 = P.length := by omega
        simpa only [hindex] using hedge.symm
      have hAedge : ∀ a ∈ LeftNeighbors P, G.Adj (P.getVert 0) (P.getVert a) := by
        intro a ha
        exact ((mem_left P a).mp ha).2
      have hBedge : ∀ b ∈ RightNeighbors P, G.Adj (P.getVert b) (P.getVert P.length) := by
        intro b hb
        exact ((mem_right P b).mp hb).2.symm
      have hAB : ∀ a ∈ LeftNeighbors P, ∀ b ∈ RightNeighbors P, a ≤ b := by
        intro a ha b hb
        by_contra hba
        exact hcross ⟨a, ha, b, hb, by omega⟩
      obtain ⟨C, hC, hlen⟩ := exists_actual_noncrossing_threshold P hp hs hdel
        (LeftNeighbors P) (RightNeighbors P) hA hB hAinternal hBinternal hAedge hBedge hAB
      exact ⟨C, hC, by omega⟩

theorem uniform_endpoint_vertex_threshold [Finite V] (P : G.Walk u v) (hp : P.IsPath)
    (hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected)
    (K : ℕ) (hK : 5 ≤ K) (hKs : K ≤ P.length + 1) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    K ≤ (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card →
    ∃ C : G.Walk (P.getVert 0) (P.getVert 0), C.IsCycle ∧ K ≤ C.length := by
  classical
  intro hKD
  apply uniform_endpoint_threshold P hp hdel K hK hKs
  rw [left_neighbor_count P hp, right_neighbor_count P hp]
  exact hKD

end ErdosProblems.PathUpperReduction.BoundaryEndpoint
