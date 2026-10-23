module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

@[expose] public section

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-! ## Common-contact arithmetic

Numeric form of the common-contact odd-cycle argument (Gyárfás Lemma 7).
The memberships below are supplied by actual cycle constructions elsewhere.
No longest-cycle bound or graph-theoretic assumption is hidden in this module.
-/

namespace Erdos58

private theorem commonContacts_card_insert (P O : Finset ℕ) (x : ℕ)
    (hsub : P ⊆ O) (hx : x ∈ O) (hnot : x ∉ P) :
    P.card + 1 ≤ O.card := by
  have h := Finset.card_le_card (show insert x P ⊆ O by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact hx
    · exact hsub hn)
  simpa only [Finset.card_insert_of_notMem hnot] using h

private theorem commonContacts_card_shift (P O : Finset ℕ) {s k : ℕ}
    (hs : 0 < s) (hk : 0 < k) (hcard : k ≤ P.card)
    (hsub : P ⊆ O) (hshift : ∀ n ∈ P, n + s ∈ O) :
    k + 1 ≤ O.card := by
  have hp : P.Nonempty := Finset.card_pos.mp (by omega)
  let m := P.max' hp
  have hm : m ∈ P := P.max'_mem hp
  have hnot : m + s ∉ P := by
    intro hn
    have hle := P.le_max' (m + s) hn
    omega
  have h := commonContacts_card_insert P O (m + s) hsub (hshift m hm) hnot
  omega

private theorem commonContacts_reflect_image_card (A : Finset ℕ) {L c : ℕ}
    (hA : ∀ d ∈ A, d < L) :
    (A.image (fun d => L - d + c)).card = A.card := by
  apply Finset.card_image_of_injOn
  intro d hd e he h
  have hdL := hA d hd
  have heL := hA e he
  change L - d + c = L - e + c at h
  omega

/-- Contact positions relative to one common cycle contact. Every other
contact is positive and strictly below the odd cycle length. The short and
exterior cycle memberships imply at least k+1 distinct odd cycle lengths. -/
public theorem common_contacts_lengths_card {L s k : ℕ} (D O : Finset ℕ)
    (_hL : Odd L) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hD : ∀ d ∈ D, 0 < d ∧ d < L) (hsize : 2 * k ≤ D.card + 1)
    (hshort : ∀ d ∈ D, Odd d → d + 2 ∈ O)
    (hshort_rev : ∀ d ∈ D, Even d → L - d + 2 ∈ O)
    (hlong : ∀ d ∈ D, Odd (d + s) → d + s + 2 ∈ O)
    (hlong_rev : ∀ d ∈ D, Even (d + s) → L - d + s + 2 ∈ O)
    (hshared : Odd s → s + 2 ∈ O) :
    k + 1 ≤ O.card := by
  classical
  let A := D.filter Odd
  let B := D.filter (fun d => ¬ Odd d)
  have hpart : A.card + B.card = D.card :=
    Finset.card_filter_add_card_filter_not (s := D) Odd
  have hmajority : k ≤ A.card ∨ k ≤ B.card := by omega
  have hA : ∀ d ∈ A, d ∈ D ∧ Odd d := by
    intro d hd
    exact Finset.mem_filter.mp hd
  have hB : ∀ d ∈ B, d ∈ D ∧ Even d := by
    intro d hd
    obtain ⟨hdD, hd⟩ := Finset.mem_filter.mp hd
    exact ⟨hdD, Nat.not_odd_iff_even.mp hd⟩
  rcases Nat.even_or_odd s with hse | hso
  · rcases hmajority with hmajor | hmajor
    · let P := A.image (fun d => d + 2)
      have hPc : P.card = A.card := Finset.card_image_of_injective _ (by
        intro d e h
        change d + 2 = e + 2 at h
        omega)
      apply commonContacts_card_shift P O (s := s) (k := k) (by omega) (by omega) (by omega)
      · intro n hn
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        exact hshort d (hA d hd).1 (hA d hd).2
      · intro n hn
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        have hm := hlong d (hA d hd).1 ((hA d hd).2.add_even hse)
        simpa only [Nat.add_assoc, Nat.add_comm 2 s] using hm
    · let P := B.image (fun d => L - d + 2)
      have hPc : P.card = B.card := commonContacts_reflect_image_card B
        (fun d hd => (hD d (hB d hd).1).2)
      apply commonContacts_card_shift P O (s := s) (k := k) (by omega) (by omega) (by omega)
      · intro n hn
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        exact hshort_rev d (hB d hd).1 (hB d hd).2
      · intro n hn
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        have hm := hlong_rev d (hB d hd).1 ((hB d hd).2.add hse)
        simpa only [Nat.add_assoc, Nat.add_comm 2 s] using hm
  · rcases hmajority with hmajor | hmajor
    · let P := A.image (fun d => L - d + (s + 2))
      have hPc : P.card = A.card := commonContacts_reflect_image_card A
        (fun d hd => (hD d (hA d hd).1).2)
      have hsub : P ⊆ O := by
        intro n hn
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        exact (Nat.add_assoc _ _ _).symm ▸
          hlong_rev d (hA d hd).1 ((hA d hd).2.add_odd hso)
      have hnot : s + 2 ∉ P := by
        intro hn
        obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
        have hdL := (hD d (hA d hd).1).2
        omega
      have hc := commonContacts_card_insert P O (s + 2) hsub (hshared hso) hnot
      omega
    · let P := B.image (fun d => d + s + 2)
      have hPc : P.card = B.card := Finset.card_image_of_injective _ (by
        intro d e h
        change d + s + 2 = e + s + 2 at h
        omega)
      have hsub : P ⊆ O := by
        intro n hn
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        exact hlong d (hB d hd).1 ((hB d hd).2.add_odd hso)
      have hnot : s + 2 ∉ P := by
        intro hn
        obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
        have hdpos := (hD d (hB d hd).1).1
        omega
      have hc := commonContacts_card_insert P O (s + 2) hsub (hshared hso) hnot
      omega

/-- The finite cyclic coordinate contract with exactly 2k common contacts,
including the normalized base contact at position zero. -/
public theorem common_contacts_cyclic_card {L s k : ℕ} (hL₃ : 3 ≤ L)
    (hL : Odd L) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (X : Finset (Fin L)) (O : Finset ℕ)
    (hzero : (⟨0, by omega⟩ : Fin L) ∈ X) (hsize : X.card = 2 * k)
    (hshort : ∀ d ∈ X.erase ⟨0, by omega⟩, Odd d.val → d.val + 2 ∈ O)
    (hshort_rev : ∀ d ∈ X.erase ⟨0, by omega⟩, Even d.val → L - d.val + 2 ∈ O)
    (hlong : ∀ d ∈ X.erase ⟨0, by omega⟩, Odd (d.val + s) → d.val + s + 2 ∈ O)
    (hlong_rev : ∀ d ∈ X.erase ⟨0, by omega⟩,
      Even (d.val + s) → L - d.val + s + 2 ∈ O)
    (hshared : Odd s → s + 2 ∈ O) :
    k + 1 ≤ O.card := by
  classical
  let z : Fin L := ⟨0, by omega⟩
  let D := (X.erase z).image Fin.val
  have hDc : D.card = (X.erase z).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hcount : D.card + 1 = 2 * k := by
    rw [hDc, Finset.card_erase_add_one hzero, hsize]
  have hD : ∀ d ∈ D, 0 < d ∧ d < L := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    have hxne : x ≠ z := (Finset.mem_erase.mp hx).1
    have hxval : x.val ≠ 0 := by
      intro h
      exact hxne (Fin.ext h)
    exact ⟨Nat.pos_of_ne_zero hxval, x.isLt⟩
  apply common_contacts_lengths_card D O hL hs hk hD (by omega)
  · intro d hd hodd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact hshort x hx hodd
  · intro d hd heven
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact hshort_rev x hx heven
  · intro d hd hodd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact hlong x hx hodd
  · intro d hd heven
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact hlong_rev x hx heven
  · exact hshared

/-! ## Contact offset contradiction

Finite arithmetic for the contact-offset step in Gyárfás Lemma 6. Every
membership in the length set is an explicit input; no graph or simple-cycle
construction is encoded as an unproved implication.
-/

def contactOffsetSums (P Q : Finset ℕ) : Finset ℕ :=
  P.biUnion (fun p => Q.image (fun q => p + q))

theorem contact_offset_sums_subset (P Q O : Finset ℕ)
    (hcycles : ∀ p ∈ P, ∀ q ∈ Q, p + q ∈ O) :
    contactOffsetSums P Q ⊆ O := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  exact hcycles p hp q hq

/-- The elementary ordered-integer sumset bound, with both nonempty
assumptions explicit. -/
theorem contact_offset_sums_card (P Q : Finset ℕ)
    (hP : P.Nonempty) (hQ : Q.Nonempty) :
    P.card + Q.card ≤ (contactOffsetSums P Q).card + 1 := by
  classical
  let p₀ := P.max' hP
  let q₀ := Q.min' hQ
  have hp₀ : p₀ ∈ P := P.max'_mem hP
  have hq₀ : q₀ ∈ Q := Q.min'_mem hQ
  let X := P.image (fun p => p + q₀)
  let Y := (Q.erase q₀).image (fun q => p₀ + q)
  have hXcard : X.card = P.card := Finset.card_image_of_injective P (by
    intro p r h
    change p + q₀ = r + q₀ at h
    omega)
  have hYcard : Y.card = Q.card - 1 := by
    rw [Finset.card_image_of_injective (Q.erase q₀) (by
      intro q r h
      change p₀ + q = p₀ + r at h
      omega), Finset.card_erase_of_mem hq₀]
  have hdisjoint : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hy
    have hple : p ≤ p₀ := P.le_max' p hp
    have hqle : q₀ ≤ q := Q.min'_le q (Finset.mem_erase.mp hq).2
    have hqne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
    change p + q₀ = x at hpx
    change p₀ + q = x at hqx
    omega
  have hsubset : X ∪ Y ⊆ contactOffsetSums P Q := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨q₀, hq₀, rfl⟩⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_biUnion.mpr
        ⟨p₀, hp₀, Finset.mem_image.mpr ⟨q, (Finset.mem_erase.mp hq).2, rfl⟩⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisjoint, hXcard, hYcard] at hcard
  have hQpos : 0 < Q.card := Finset.card_pos.mpr hQ
  omega

theorem contact_offset_sums_with_small {r : ℕ} (P Q O : Finset ℕ)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hcycles : ∀ p ∈ P, ∀ q ∈ Q, p + q ∈ O)
    (hr : r ∈ O) (hbelow : ∀ p ∈ P, ∀ q ∈ Q, r < p + q) :
    P.card + Q.card ≤ O.card := by
  classical
  have hrnot : r ∉ contactOffsetSums P Q := by
    intro hrmem
    obtain ⟨p, hp, hrmem⟩ := Finset.mem_biUnion.mp hrmem
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hrmem
    have hlt := hbelow p hp q hq
    omega
  have hsub : insert r (contactOffsetSums P Q) ⊆ O :=
    Finset.insert_subset hr (contact_offset_sums_subset P Q O hcycles)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hrnot] at hcard
  have hsum := contact_offset_sums_card P Q hP hQ
  omega

theorem contact_offset_sums_with_two_small {r s : ℕ} (P Q O : Finset ℕ)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hcycles : ∀ p ∈ P, ∀ q ∈ Q, p + q ∈ O)
    (hr : r ∈ O) (hs : s ∈ O) (hrs : r < s)
    (hbelow : ∀ p ∈ P, ∀ q ∈ Q, s < p + q) :
    P.card + Q.card + 1 ≤ O.card := by
  classical
  have hsnot : s ∉ contactOffsetSums P Q := by
    intro hsmem
    obtain ⟨p, hp, hsmem⟩ := Finset.mem_biUnion.mp hsmem
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hsmem
    have hlt := hbelow p hp q hq
    omega
  have hrnot : r ∉ insert s (contactOffsetSums P Q) := by
    intro hrmem
    rcases Finset.mem_insert.mp hrmem with heq | hrmem
    · omega
    · obtain ⟨p, hp, hrmem⟩ := Finset.mem_biUnion.mp hrmem
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hrmem
      have hlt := hbelow p hp q hq
      omega
  have hsub : insert r (insert s (contactOffsetSums P Q)) ⊆ O :=
    Finset.insert_subset hr (Finset.insert_subset hs
      (contact_offset_sums_subset P Q O hcycles))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hrnot, Finset.card_insert_of_notMem hsnot] at hcard
  have hsum := contact_offset_sums_card P Q hP hQ
  omega

/-- Four distinct offsets at least two contradict a length budget of k.
The proper-distance set has k−1 distances of each parity, and its even
distances are at least twice the odd positive minimum d. -/
theorem contact_four_offsets {k d : ℕ} (D T O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hTcard : 4 ≤ T.card) (hTlower : ∀ t ∈ T, 2 ≤ t) (hTwo : 2 ∈ T)
    (hcycles : ∀ e ∈ D, ∀ t ∈ T, Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have hDodd : (D.filter Odd).Nonempty := Finset.card_pos.mp (by omega)
  have hDeven : (D.filter Even).Nonempty := Finset.card_pos.mp (by omega)
  by_cases hTodd : 2 ≤ (T.filter Odd).card
  · have hQ : (T.filter Odd).Nonempty := Finset.card_pos.mp (by omega)
    have hbase : d + 2 ∈ O := hcycles d hd 2 hTwo (hdodd.add_even (by decide))
    have hsum := contact_offset_sums_with_small (D.filter Even) (T.filter Odd) O
      hDeven hQ (by
        intro e he t ht
        exact hcycles e (Finset.mem_filter.mp he).1 t (Finset.mem_filter.mp ht).1
          ((Finset.mem_filter.mp he).2.add_odd (Finset.mem_filter.mp ht).2)) hbase (by
        intro e he t ht
        have helo := hevenlower e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
        have htlo := hTlower t (Finset.mem_filter.mp ht).1
        have htmod := Nat.odd_iff.mp (Finset.mem_filter.mp ht).2
        omega)
    omega
  · have hpartition : (T.filter Even).card + (T.filter Odd).card = T.card := by
      simpa only [Nat.not_even_iff_odd] using T.card_filter_add_card_filter_not Even
    have hTeven : 3 ≤ (T.filter Even).card := by omega
    have hQ : (T.filter Even).Nonempty := Finset.card_pos.mp (by omega)
    have hsum := contact_offset_sums_card (D.filter Odd) (T.filter Even) hDodd hQ
    have hsub := contact_offset_sums_subset (D.filter Odd) (T.filter Even) O (by
      intro e he t ht
      exact hcycles e (Finset.mem_filter.mp he).1 t (Finset.mem_filter.mp ht).1
        ((Finset.mem_filter.mp he).2.add_even (Finset.mem_filter.mp ht).2))
    have hcard := Finset.card_le_card hsub
    omega

/-- The unit crossing exception has offsets 2, 4, and b+4. For odd b,
the minimum supplies two small lengths and the even distances supply the
remaining k−1 lengths. -/
theorem contact_unit_odd_exception {k d b : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hbpos : 0 < b) (hbodd : Odd b)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hcycles : ∀ e ∈ D, ∀ t ∈ ({2, 4, b + 4} : Finset ℕ),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have hE : (D.filter Even).Nonempty := Finset.card_pos.mp (by omega)
  have hbase₂ : d + 2 ∈ O := hcycles d hd 2 (by simp) (hdodd.add_even (by decide))
  have hbase₄ : d + 4 ∈ O := hcycles d hd 4 (by simp) (hdodd.add_even (by decide))
  have hsum := contact_offset_sums_with_two_small (D.filter Even) {b + 4} O
    hE (Finset.singleton_nonempty _) (by
      intro e he t ht
      have hteq : t = b + 4 := Finset.mem_singleton.mp ht
      subst t
      exact hcycles e (Finset.mem_filter.mp he).1 (b + 4) (by simp)
        ((Finset.mem_filter.mp he).2.add_odd (hbodd.add_even (by decide))))
    hbase₂ hbase₄ (by omega) (by
      intro e he t ht
      have hteq : t = b + 4 := Finset.mem_singleton.mp ht
      have helo := hevenlower e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
      omega)
  simp only [Finset.card_singleton] at hsum
  omega

theorem contact_three_even_offsets {k : ℕ} (D T O : Finset ℕ)
    (hk : 2 ≤ k) (hoddcard : (D.filter Odd).card = k - 1)
    (hTcard : 3 ≤ T.card) (hTeven : ∀ t ∈ T, Even t)
    (hcycles : ∀ e ∈ D, ∀ t ∈ T, Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have hP : (D.filter Odd).Nonempty := Finset.card_pos.mp (by omega)
  have hQ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hsum := contact_offset_sums_card (D.filter Odd) T hP hQ
  have hsub := contact_offset_sums_subset (D.filter Odd) T O (by
    intro e he t ht
    exact hcycles e (Finset.mem_filter.mp he).1 t ht
      ((Finset.mem_filter.mp he).2.add_even (hTeven t ht)))
  have hcard := Finset.card_le_card hsub
  omega

theorem contact_two_odd_offsets {k d t u : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (ht : 3 ≤ t) (hu : 3 ≤ u) (htodd : Odd t) (huodd : Odd u) (htu : t ≠ u)
    (hcycles : ∀ e ∈ D, ∀ q ∈ ({2, t, u} : Finset ℕ),
      Odd (e + q) → e + q ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have hP : (D.filter Even).Nonempty := Finset.card_pos.mp (by omega)
  have hbase : d + 2 ∈ O := hcycles d hd 2 (by simp) (hdodd.add_even (by decide))
  have hsum := contact_offset_sums_with_small (D.filter Even) {t, u} O
    hP (Finset.insert_nonempty _ _) (by
      intro e he q hq
      have hqodd : Odd q := by
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact htodd
        · exact (Finset.mem_singleton.mp hq) ▸ huodd
      exact hcycles e (Finset.mem_filter.mp he).1 q (by simp_all)
        ((Finset.mem_filter.mp he).2.add_odd hqodd)) hbase (by
      intro e he q hq
      have helo := hevenlower e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
      have hqlo : 3 ≤ q := by
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ht
        · exact (Finset.mem_singleton.mp hq) ▸ hu
      omega)
  have hQcard : ({t, u} : Finset ℕ).card = 2 := Finset.card_pair htu
  omega

/-- At least three distinct positive A–B path lengths give at least four
distinct offsets after adjoining the ordinary two-edge contact path. -/
theorem contact_many_path_offsets {k d : ℕ} (D R O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hRcard : 3 ≤ R.card) (hRpositive : ∀ r ∈ R, 0 < r)
    (hcycles : ∀ e ∈ D, ∀ t ∈ insert 2 (R.image (fun r => r + 2)),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have htwo : 2 ∉ R.image (fun r => r + 2) := by
    intro hmem
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hmem
    have hrpos := hRpositive r hr
    omega
  have hcard : 4 ≤ (insert 2 (R.image (fun r => r + 2))).card := by
    rw [Finset.card_insert_of_notMem htwo, Finset.card_image_of_injective R (by
      intro r s h
      change r + 2 = s + 2 at h
      omega)]
    omega
  apply contact_four_offsets D _ O hk hdpos hd hdodd hoddcard hevencard hevenlower hcard
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · omega
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
      omega
  · exact Finset.mem_insert_self _ _
  · exact hcycles

theorem contact_balanced_exception {k d b : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hbpos : 0 < b)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hcycles : ∀ e ∈ D, ∀ t ∈ ({2, b + 4, 3 * b + 4} : Finset ℕ),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  by_cases hb : Even b
  · apply contact_three_even_offsets D {2, b + 4, 3 * b + 4} O hk hoddcard
    · have hcard : ({2, b + 4, 3 * b + 4} : Finset ℕ).card = 3 :=
        Finset.card_triple_eq_three_iff.mpr ⟨by omega, by omega, by omega⟩
      omega
    · intro t ht
      have hbmod := Nat.even_iff.mp hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      apply Nat.even_iff.mpr
      rcases ht with rfl | rfl | rfl <;> omega
    · exact hcycles
  · have hbodd := Nat.not_even_iff_odd.mp hb
    have htodd : Odd (b + 4) := hbodd.add_even (by decide)
    have huodd : Odd (3 * b + 4) := by
      apply Nat.odd_iff.mpr
      have hbmod := Nat.odd_iff.mp hbodd
      omega
    exact contact_two_odd_offsets D O hk hdpos hd hdodd hevencard hevenlower
      (by omega) (by omega) htodd huodd (by omega) hcycles

theorem contact_unit_exception {k d b : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hbpos : 0 < b)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hcycles : ∀ e ∈ D, ∀ t ∈ ({2, 4, b + 4} : Finset ℕ),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  by_cases hb : Even b
  · apply contact_three_even_offsets D {2, 4, b + 4} O hk hoddcard
    · have hcard : ({2, 4, b + 4} : Finset ℕ).card = 3 :=
        Finset.card_triple_eq_three_iff.mpr ⟨by omega, by omega, by omega⟩
      omega
    · intro t ht
      have hbmod := Nat.even_iff.mp hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      apply Nat.even_iff.mpr
      rcases ht with rfl | rfl | rfl <;> omega
    · exact hcycles
  · exact contact_unit_odd_exception D O hk hdpos hd hdodd hbpos
      (Nat.not_even_iff_odd.mp hb) hevencard hevenlower hcycles

theorem contact_shared_ab_odd {k d s : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hs : 3 ≤ s) (hsodd : Odd s)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hcycles : ∀ e ∈ D, ∀ t ∈ ({2, 3, s + 2} : Finset ℕ),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  exact contact_two_odd_offsets D O hk hdpos hd hdodd hevencard hevenlower
    (by omega) (by omega) (by decide) (hsodd.add_even (by decide)) (by omega) hcycles

/-- The four-edge third-contact path is an explicit additional input. -/
theorem contact_shared_ab_even_large {k s : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hs : 4 ≤ s) (hseven : Even s)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hthird_contact : ∀ e ∈ D, Odd e → e + 4 ∈ O)
    (hcycles : ∀ e ∈ D, ∀ t ∈ ({2, 3, s + 2} : Finset ℕ),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  apply contact_three_even_offsets D {2, 4, s + 2} O hk hoddcard
  · have hcard : ({2, 4, s + 2} : Finset ℕ).card = 3 :=
      Finset.card_triple_eq_three_iff.mpr ⟨by omega, by omega, by omega⟩
    omega
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · decide
    · decide
    · exact hseven.add (by decide)
  · intro e he t ht hodd
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hcycles e he 2 (by simp) hodd
    · apply hthird_contact e he
      apply Nat.odd_iff.mpr
      have hemod := Nat.odd_iff.mp hodd
      omega
    · exact hcycles e he (s + 2) (by simp) hodd

/-- The shared A–B chord with exterior path length two additionally supplies
an actual triangle. Reflection, difference closure and the longest-length
cap force d≥3, so the contact lengths from offsets 2 and 4 are all above it. -/
theorem contact_shared_ab_two {n k d : ℕ} (D O : Finset ℕ)
    (hk : 2 ≤ k) (hnodd : Odd n) (hdpos : 0 < d) (hd : d ∈ D) (hdodd : Odd d)
    (hbound : ∀ e ∈ D, e < n) (hminimum : ∀ e ∈ D, d ≤ e)
    (hevenlower : ∀ e ∈ D, Even e → 2 * d ≤ e)
    (hreflect : ∀ e ∈ D, n - e ∈ D)
    (hdiff : ∀ a ∈ D, ∀ b ∈ D, a < b → b - a ∈ D)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hcap : ∀ o ∈ O, o ≤ n) (htriangle : 3 ∈ O)
    (hcycles : ∀ e ∈ D, ∀ t ∈ ({2, 3, 4} : Finset ℕ),
      Odd (e + t) → e + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have hdlt : d < n := hbound d hd
  have hnmod := Nat.odd_iff.mp hnodd
  have hdmod := Nat.odd_iff.mp hdodd
  have hr : n - d ∈ D := hreflect d hd
  have hreven : Even (n - d) := Nat.even_iff.mpr (by omega)
  have hrlower := hevenlower (n - d) hr hreven
  have hstrict : d < n - d := by omega
  have hsub := hdiff d hd (n - d) hr hstrict
  have he : n - 2 * d ∈ D := by
    convert hsub using 1
    omega
  have heodd : Odd (n - 2 * d) := Nat.odd_iff.mpr (by omega)
  have hcycle : n - 2 * d + 4 ∈ O :=
    hcycles (n - 2 * d) he 4 (by simp) (heodd.add_even (by decide))
  have hle := hcap (n - 2 * d + 4) hcycle
  have hdthree : 3 ≤ d := by omega
  have hP : (D.filter Odd).Nonempty := Finset.card_pos.mp (by omega)
  have hsum := contact_offset_sums_with_small (D.filter Odd) {2, 4} O hP
    (Finset.insert_nonempty _ _) (by
      intro e he t ht
      have hteven : Even t := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> decide
      exact hcycles e (Finset.mem_filter.mp he).1 t (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
        rcases ht with rfl | rfl <;> simp)
        ((Finset.mem_filter.mp he).2.add_even hteven)) htriangle (by
      intro e he t ht
      have helo := hminimum e (Finset.mem_filter.mp he).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> omega)
  have hQcard : ({2, 4} : Finset ℕ).card = 2 := by decide
  omega

/-! ## Contact and offset arithmetic

One arithmetic contract for the repaired common-AB case of Gyárfás Lemma 6.

If k≥2, |S|=s is even and s≥4, odd contact gaps provide k−1 distinct
odd proper arc lengths. Each such arc must be closed geometrically by three
paths of lengths 2, 4, and s+2. The length-4 path uses a third common contact
outside the arc; it is not inferred from any numerical A–B path-length set.

This module assumes those three memberships explicitly and proves their
counting consequence. It does not construct contact positions, infer gap
parity, or prove the required simple cycles.
-/

/-- The common-AB case with an even exterior path of length at least four
contributes at least k+1 distinct odd lengths. `hthird_contact` is the explicit
cycle membership supplied by the repaired four-edge third-contact bridge.
The result counts the odd part of O, so O need not contain only odd numbers. -/
theorem shared_ab_even_contact_offsets {k s : ℕ} (P O : Finset ℕ)
    (hk : 2 ≤ k) (hs : 4 ≤ s) (hseven : Even s)
    (hodd : ∀ n ∈ P, Odd n) (hsize : k - 1 ≤ P.card)
    (hshort : ∀ n ∈ P, n + 2 ∈ O)
    (hthird_contact : ∀ n ∈ P, n + 4 ∈ O)
    (hlong : ∀ n ∈ P, n + s + 2 ∈ O) :
    k + 1 ≤ (O.filter Odd).card := by
  classical
  have hnonempty : P.Nonempty := Finset.card_pos.mp (by omega)
  let m := P.max' hnonempty
  have hm : m ∈ P := P.max'_mem hnonempty
  let X := P.image (fun n => n + 2)
  have hXcard : X.card = P.card := Finset.card_image_of_injective P (by
    intro n q h
    change n + 2 = q + 2 at h
    omega)
  have hshort_odd : ∀ n ∈ P, Odd (n + 2) := by
    intro n hn
    obtain ⟨q, hq⟩ := hodd n hn
    exact ⟨q + 1, by omega⟩
  have hthird_odd : Odd (m + 4) := by
    obtain ⟨q, hq⟩ := hodd m hm
    exact ⟨q + 2, by omega⟩
  have hlong_odd : Odd (m + s + 2) := by
    obtain ⟨q, hq⟩ := hodd m hm
    obtain ⟨r, hr⟩ := hseven
    exact ⟨q + r + 1, by omega⟩
  have hthird_not : m + 4 ∉ X := by
    intro hn
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hn
    have hle : n ≤ m := P.le_max' n hn
    change n + 2 = m + 4 at heq
    omega
  have hlong_not : m + s + 2 ∉ insert (m + 4) X := by
    intro hn
    rcases Finset.mem_insert.mp hn with heq | hn
    · omega
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hn
      have hle : n ≤ m := P.le_max' n hn
      change n + 2 = m + s + 2 at heq
      omega
  have hsub : insert (m + s + 2) (insert (m + 4) X) ⊆ O.filter Odd := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Finset.mem_filter.mpr ⟨hlong m hm, hlong_odd⟩
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Finset.mem_filter.mpr ⟨hthird_contact m hm, hthird_odd⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨hshort q hq, hshort_odd q hq⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hlong_not,
    Finset.card_insert_of_notMem hthird_not, hXcard] at hcard
  omega

/-! ## Distinct-contact arithmetic

Numeric form of the different-contact argument, with an explicit second
contact at the other endpoint. Membership hypotheses represent actual simple
cycles; no degenerate pair is admitted. The longest odd-cycle cap is explicit.
-/

private theorem differentContacts_same_even {s d e : ℕ}
    (hd : Odd (s + d)) (he : Odd (s + e)) : Even (Nat.dist d e) := by
  rw [Nat.odd_iff] at hd he
  rw [Nat.even_iff]
  simp only [Nat.dist]
  omega

private theorem differentContacts_cross_odd {L s d e : ℕ}
    (hL : Odd L) (heL : e < L)
    (hd : Odd (s + d)) (he : Odd (s + e)) : Odd (Nat.dist d (L - e)) := by
  rw [Nat.odd_iff] at hL hd he ⊢
  simp only [Nat.dist]
  omega

private theorem differentContacts_cross_gap {L b t r : ℕ}
    (hbt : b + t = L) (hrL : r < L) :
    Nat.dist b (L - r) = Nat.dist r t := by
  simp only [Nat.dist]
  omega

/-- Two B-contacts suffice for the repaired numeric Lemma 8. Position zero is
a B-contact outside all 2k selected A-contacts. All cycle memberships include
the two attachment edges, and only distinct contact pairs are used. -/
public theorem different_contacts_lengths_card {L s k : ℕ} (D Z O : Finset ℕ)
    (_hL₃ : 3 ≤ L) (hL : Odd L) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hD : ∀ d ∈ D, 0 < d ∧ d < L) (hDcard : D.card = 2 * k)
    (hZ : ∀ z ∈ Z, z < L) (hzero : 0 ∈ Z) (hZcard : 2 ≤ Z.card)
    (hcycle : L ∈ O) (hcap : ∀ n ∈ O, n ≤ L)
    (hfan : ∀ d ∈ D, ∀ e ∈ D, d ≠ e →
      Odd (Nat.dist d e) → Nat.dist d e + 2 ∈ O)
    (hfan_rev : ∀ d ∈ D, ∀ e ∈ D, d ≠ e →
      Even (Nat.dist d e) → L - Nat.dist d e + 2 ∈ O)
    (hexterior : ∀ d ∈ D, ∀ z ∈ Z, d ≠ z →
      Odd (s + Nat.dist d z) → s + Nat.dist d z + 2 ∈ O)
    (hexterior_rev : ∀ d ∈ D, ∀ z ∈ Z, d ≠ z →
      Even (s + Nat.dist d z) → s + (L - Nat.dist d z) + 2 ∈ O) :
    k + 1 ≤ O.card := by
  classical
  by_contra hn
  have hOcard : O.card ≤ k := by omega
  let t := s + 2
  have ht : 3 ≤ t := by dsimp [t]; omega
  let R := D.filter (fun d => Odd (s + d))
  let Q := D.filter (fun d => ¬ Odd (s + d))
  let F := R.image (fun d => d + t)
  let B := Q.image (fun d => L - d + t)
  have hR : ∀ r ∈ R, r ∈ D ∧ Odd (s + r) := by
    intro r hr
    exact Finset.mem_filter.mp hr
  have hQ : ∀ q ∈ Q, q ∈ D ∧ Even (s + q) := by
    intro q hq
    obtain ⟨hqD, hq⟩ := Finset.mem_filter.mp hq
    exact ⟨hqD, Nat.not_odd_iff_even.mp hq⟩
  have hpart : R.card + Q.card = 2 * k := by
    rw [← hDcard]
    exact Finset.card_filter_add_card_filter_not (s := D) (fun d => Odd (s + d))
  have hFc : F.card = R.card := Finset.card_image_of_injective _ (by
    intro d e h
    change d + t = e + t at h
    omega)
  have hBc : B.card = Q.card := by
    apply Finset.card_image_of_injOn
    intro d hd e he h
    have hdL := (hD d (hQ d hd).1).2
    have heL := (hD e (hQ e he).1).2
    change L - d + t = L - e + t at h
    omega
  have hFsub : F ⊆ O := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    have hdpos := (hD d (hR d hd).1).1
    have hm := hexterior d (hR d hd).1 0 hzero (by omega)
      (by simpa [Nat.dist] using (hR d hd).2)
    simpa [Nat.dist, t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
  have hBsub : B ⊆ O := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    have hdpos := (hD d (hQ d hd).1).1
    have hm := hexterior_rev d (hQ d hd).1 0 hzero (by omega)
      (by simpa [Nat.dist] using (hQ d hd).2)
    simpa [Nat.dist, t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
  have hFle := Finset.card_le_card hFsub
  have hBle := Finset.card_le_card hBsub
  have hRc : R.card = k := by omega
  have hQc : Q.card = k := by omega
  have hFeq : F = O := Finset.eq_of_subset_of_card_le hFsub (by omega)
  have hBeq : B = O := Finset.eq_of_subset_of_card_le hBsub (by omega)
  have hpoint : ∀ r ∈ R, r + t ∈ O := by
    intro r hr
    exact hFsub (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hreflect : ∀ r ∈ R, L - r ∈ D := by
    intro r hr
    have hm : r + t ∈ B := hBeq.symm ▸ hpoint r hr
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hm
    have hrL := (hD r (hR r hr).1).2
    have hqL := (hD q (hQ q hq).1).2
    change L - q + t = r + t at heq
    have hqr : q = L - r := by omega
    exact hqr ▸ (hQ q hq).1
  have hRn : R.Nonempty := Finset.card_pos.mp (by omega)
  let a := R.min' hRn
  let b := R.max' hRn
  have ha : a ∈ R := R.min'_mem hRn
  have hb : b ∈ R := R.max'_mem hRn
  have hapos := (hD a (hR a ha).1).1
  have hbpos := (hD b (hR b hb).1).1
  have hbt : b + t = L := by
    have hle := hcap _ (hpoint b hb)
    have hLF : L ∈ F := hFeq.symm ▸ hcycle
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hLF
    change r + t = L at heq
    have hrb := R.le_max' r hr
    omega
  have hmin : ∀ n ∈ O, a + t ≤ n := by
    intro n hn
    have hnF : n ∈ F := hFeq.symm ▸ hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hnF
    have har := R.min'_le r hr
    omega
  have hcross : ∀ r ∈ R, Nat.dist r t + 2 ∈ O := by
    intro r hr
    have hrL := (hD r (hR r hr).1).2
    have hodd := differentContacts_cross_odd hL hrL (hR b hb).2 (hR r hr).2
    have hne : b ≠ L - r := by
      intro heq
      simp [heq] at hodd
    have hm := hfan b (hR b hb).1 (L - r) (hreflect r hr) hne hodd
    rw [differentContacts_cross_gap hbt hrL] at hm
    exact hm
  have haone : a = 1 := by
    have hbound := hmin _ (hcross a ha)
    simp only [Nat.dist] at hbound
    omega
  have honeR : 1 ∈ R := haone ▸ ha
  have hseven : Even s := by
    have ho := (hR 1 honeR).2
    rw [Nat.odd_iff] at ho
    rw [Nat.even_iff]
    omega
  have hbone : b = 1 := by
    by_contra hne
    have hgt : 1 < b := by omega
    have heven := differentContacts_same_even (hR 1 honeR).2 (hR b hb).2
    have hm := hfan_rev 1 (hR 1 honeR).1 b (hR b hb).1 (by omega) heven
    have heq : L - Nat.dist 1 b + 2 = t + 3 := by
      simp only [Nat.dist]
      omega
    rw [heq] at hm
    have hmF : t + 3 ∈ F := hFeq.symm ▸ hm
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hmF
    change r + t = t + 3 at heq
    have hrthree : r = 3 := by omega
    have hthreeR : 3 ∈ R := hrthree ▸ hr
    have hbound := hmin _ (hcross 3 hthreeR)
    simp only [Nat.dist] at hbound
    omega
  have hLs : L = s + 3 := by dsimp [t] at hbt; omega
  have hsmod : s % 2 = 0 := Nat.even_iff.mp hseven
  have hLfive : 5 ≤ L := by omega
  have honeD : 1 ∈ D := (hR 1 honeR).1
  have hlastD : L - 1 ∈ D := hreflect 1 honeR
  obtain ⟨z, hz, hzne⟩ := Z.exists_mem_ne (by omega) 0
  have hzL := hZ z hz
  have hnear : ∀ d ∈ D, d ≠ z →
      Nat.dist d z = 1 ∨ Nat.dist d z = L - 1 := by
    intro d hd hne
    have hdL := (hD d hd).2
    have hgapL : Nat.dist d z < L := by simp only [Nat.dist]; omega
    have hgappos : 0 < Nat.dist d z := by simp only [Nat.dist]; omega
    rcases Nat.even_or_odd (Nat.dist d z) with he | ho
    · have hm := hexterior_rev d hd z hz hne (hseven.add he)
      have hbound := hcap _ hm
      right
      omega
    · have hm := hexterior d hd z hz hne (hseven.add_odd ho)
      have hbound := hcap _ hm
      left
      omega
  have hnearone : z = 1 ∨ Nat.dist 1 z = 1 ∨ Nat.dist 1 z = L - 1 := by
    by_cases heq : 1 = z
    · exact Or.inl heq.symm
    · exact Or.inr (hnear 1 honeD heq)
  have hnearlast : z = L - 1 ∨ Nat.dist (L - 1) z = 1 ∨
      Nat.dist (L - 1) z = L - 1 := by
    by_cases heq : L - 1 = z
    · exact Or.inl heq.symm
    · exact Or.inr (hnear (L - 1) hlastD heq)
  simp only [Nat.dist] at hnearone hnearlast
  omega

/-! ## Endpoint degree arithmetic -/

/-! Exact natural-number arithmetic for the degree/contact split in
Gyárfás's endpoint argument. No graph or structural assumptions occur. -/

/-- The degree lower bound and the local fan inequality leave exactly
zero or one exterior continuation. In the one-continuation case, the
stronger inequality from an absent opposing contact is impossible. -/
theorem endpoint_degree_contact_cases {k p q : ℕ} (hk : 1 ≤ k)
    (hdegree : 2 * k ≤ p + q) (hfan : q + p / 2 ≤ k) :
    (q = 0 ∧ 2 * k ≤ p) ∨
      (q = 1 ∧ p = 2 * k - 1 ∧ ¬ (q + (p + 1) / 2 ≤ k)) := by
  omega

/-! ## Contact two-path contradiction -/

/-! A short numeric saturated-contact contradiction. Two distinct positive
exterior path lengths suffice after contact-distance invariance and the
actual four-contact cycle have been established. -/

theorem contact_two_paths_lengths_card {n k e : ℕ} (D R O : Finset ℕ)
    (hn₃ : 3 ≤ n) (hn : Odd n) (hk : 2 ≤ k)
    (he : e ∈ D) (hepos : 0 < e) (heodd : Odd e)
    (hoddcard : (D.filter Odd).card = k - 1)
    (hevencard : (D.filter Even).card = k - 1)
    (hevenlower : ∀ d ∈ D, Even d → 2 * e ≤ d)
    (hreflect : ∀ d ∈ D, n - d ∈ D)
    (hdiff : ∀ d ∈ D, ∀ d' ∈ D, d < d' → d' - d ∈ D)
    (hRpos : ∀ h ∈ R, 1 ≤ h) (hRcard : 2 ≤ R.card)
    (hfour : e + 4 ∈ O) (hcap : ∀ l ∈ O, l ≤ n)
    (hcycles : ∀ d ∈ D, ∀ t ∈ insert 2 (R.image (fun h => h + 2)),
      Odd (d + t) → d + t ∈ O) :
    k + 1 ≤ O.card := by
  classical
  have hshift : ∀ h ∈ R, h + 2 ∈ insert 2 (R.image (fun h => h + 2)) := by
    intro h hh
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h, hh, rfl⟩)
  by_cases heone : e = 1
  · subst e
    have hnear : n - 1 ∈ D := hreflect 1 he
    have hfar : n - 2 ∈ D := by
      have h := hdiff 1 he (n - 1) hnear (by omega)
      simpa only [Nat.sub_sub, Nat.reduceAdd] using h
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨h, hh⟩ := hRne
    have hpos := hRpos h hh
    have hnmod := Nat.odd_iff.mp hn
    rcases Nat.even_or_odd h with heven | hodd
    · have hm := hcycles (n - 2) hfar (h + 2) (hshift h hh) (by
        rw [Nat.odd_iff]
        have hmod := Nat.even_iff.mp heven
        omega)
      have hbound := hcap _ hm
      omega
    · have hm := hcycles (n - 1) hnear (h + 2) (hshift h hh) (by
        rw [Nat.odd_iff]
        have hmod := Nat.odd_iff.mp hodd
        omega)
      have hbound := hcap _ hm
      omega
  · have he₃ : 3 ≤ e := by have := Nat.odd_iff.mp heodd; omega
    by_cases hRodd : ∃ h ∈ R, Odd h
    · obtain ⟨h, hh, hodd⟩ := hRodd
      have hpos := hRpos h hh
      have hEne : (D.filter Even).Nonempty := Finset.card_pos.mp (by omega)
      have hbase : e + 2 ∈ O := hcycles e he 2 (by simp) (heodd.add_even (by decide))
      have hsum := contact_offset_sums_with_two_small (D.filter Even) {h + 2} O
        hEne (Finset.singleton_nonempty _) (by
          intro d hd t ht
          have htval : t = h + 2 := Finset.mem_singleton.mp ht
          subst t
          exact hcycles d (Finset.mem_filter.mp hd).1 (h + 2) (hshift h hh)
            ((Finset.mem_filter.mp hd).2.add_odd (hodd.add_even (by decide))))
        hbase hfour (by omega) (by
          intro d hd t ht
          have hdlower := hevenlower d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
          have htval : t = h + 2 := Finset.mem_singleton.mp ht
          omega)
      simp only [Finset.card_singleton, hevencard] at hsum
      omega
    · let T := insert 2 (R.image (fun h => h + 2))
      have hnot : 2 ∉ R.image (fun h => h + 2) := by
        intro hm
        obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp hm
        have hpos := hRpos h hh
        omega
      have hTcard : 3 ≤ T.card := by
        rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective R (by
          intro h h' heq
          change h + 2 = h' + 2 at heq
          omega)]
        omega
      have hTeven : ∀ t ∈ T, Even t := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · decide
        · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ht
          have heven : Even h := Nat.not_odd_iff_even.mp (fun hodd => hRodd ⟨h, hh, hodd⟩)
          exact heven.add (by decide)
      exact contact_three_even_offsets D T O hk hoddcard hTcard hTeven hcycles

/-! ## Exact contact gaps

Exact contact-distance invariance for the first counting step in Gyárfás
Lemma 6. Contacts are positions in `ZMod n`; a proper directed arc from a to
b has numerical length `(b-a).val`. The two arc-plus-offset cycle-length
memberships are explicit hypotheses. No graph paths or cycles are inferred.

This module stops at invariance and the exact parity-class cardinalities;
it does not classify the contact subgroup or construct equal cyclic gaps.
-/

/-- All nonzero directed contact distances from one anchor. -/
public def contactAnchorDistances {n : ℕ} (S : Finset (ZMod n)) (a : ZMod n) : Finset ℕ :=
  (S.erase a).image (fun b => (b - a).val)

/-- The union of the proper directed distance sets of all contacts. -/
public def contactAllDistances {n : ℕ} (S : Finset (ZMod n)) : Finset ℕ :=
  S.biUnion (contactAnchorDistances S)

private theorem contactDistances_bounds {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) {d : ℕ} (hd : d ∈ contactAllDistances S) :
    0 < d ∧ d < n := by
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1
  exact ⟨ZMod.val_pos.mpr hba, ZMod.val_lt _⟩

private theorem contactDistances_reflect {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) {d : ℕ} (hd : d ∈ contactAllDistances S) :
    n - d ∈ contactAllDistances S := by
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1
  let : NeZero (b - a) := ⟨hba⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b, (Finset.mem_erase.mp hb).2, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1.symm, ha⟩, ?_⟩
  rw [show a - b = -(b - a) by abel, ZMod.val_neg_of_ne_zero]

private theorem contactDistances_anchor_card {n k : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (a : ZMod n) (ha : a ∈ S)
    (hsize : S.card = 2 * k - 1) (hk : 2 ≤ k) :
    (contactAnchorDistances S a).card = 2 * k - 2 := by
  have hcard : (contactAnchorDistances S a).card = (S.erase a).card := by
    apply Finset.card_image_of_injective
    intro b c h
    have hsub : b - a = c - a := ZMod.val_injective n h
    have hadd := congrArg (fun z : ZMod n => z + a) hsub
    simpa only [sub_add_cancel] using hadd
  have herase := Finset.card_erase_add_one ha
  omega

private theorem contactOffsets_card_plus_one (P O : Finset ℕ) {t u : ℕ}
    (hP : P.Nonempty) (htu : t < u)
    (ht : ∀ d ∈ P, d + t ∈ O) (hu : ∀ d ∈ P, d + u ∈ O) :
    P.card + 1 ≤ O.card := by
  let m := P.max' hP
  have hm : m ∈ P := P.max'_mem hP
  let X := P.image (fun d => d + t)
  have hXcard : X.card = P.card := Finset.card_image_of_injective P (by
    intro d e heq
    change d + t = e + t at heq
    omega)
  have hnot : m + u ∉ X := by
    intro hn
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
    have hle : d ≤ m := P.le_max' d hd
    change d + t = m + u at heq
    omega
  have hsub : insert (m + u) X ⊆ O := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hu m hm
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact ht e he
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hXcard] at hcard
  exact hcard

/-- If an odd n-cycle has 2k−1 contacts and two distinct offsets of the same
parity, at most k supplied odd cycle lengths force every anchor to see the
entire proper distance set. Each parity class has exactly k−1 values.

`hcycles` is the sole numerical cycle-length contract: every proper directed
contact arc plus either offset belongs to O whenever the resulting sum is odd.
Actual simple-cycle constructions must establish this input separately. -/
public theorem contact_distance_invariance {n k t u : ℕ}
    (S : Finset (ZMod n)) (O : Finset ℕ)
    (hn : Odd n) (hk : 2 ≤ k) (hsize : S.card = 2 * k - 1)
    (htune : t ≠ u) (htuparity : t % 2 = u % 2) (hO : O.card ≤ k)
    (hcycles : ∀ d ∈ contactAllDistances S, ∀ q ∈ ({t, u} : Finset ℕ),
      Odd (d + q) → d + q ∈ O) :
    (∀ a ∈ S, contactAnchorDistances S a = contactAllDistances S) ∧
      ((contactAllDistances S).filter Odd).card = k - 1 ∧
      ((contactAllDistances S).filter Even).card = k - 1 := by
  classical
  have hnmod : n % 2 = 1 := Nat.odd_iff.mp hn
  have hnne : n ≠ 0 := by omega
  let : NeZero n := ⟨hnne⟩
  let A := contactAllDistances S
  let E := A.filter (fun d => d % 2 = 0)
  let U := A.filter (fun d => d % 2 = 1)
  let P := A.filter (fun d => d % 2 ≠ t % 2)
  have hbounds : ∀ d ∈ A, 0 < d ∧ d < n := fun d hd => contactDistances_bounds S hd
  have hreflect : ∀ d ∈ A, n - d ∈ A := fun d hd => contactDistances_reflect S hd
  have hreflect_card (p : ℕ) (hp : p ≤ 1) :
      (A.filter (fun d => d % 2 = p)).card ≤
        (A.filter (fun d => d % 2 = 1 - p)).card := by
    apply Finset.card_le_card_of_injOn (fun d => n - d)
    · intro d hd
      obtain ⟨hdA, hdp⟩ := Finset.mem_filter.mp hd
      refine Finset.mem_filter.mpr ⟨hreflect d hdA, ?_⟩
      have hdlt := (hbounds d hdA).2
      change (n - d) % 2 = 1 - p
      omega
    · intro d hd e he heq
      have hdlt := (hbounds d (Finset.mem_filter.mp hd).1).2
      have helt := (hbounds e (Finset.mem_filter.mp he).1).2
      change n - d = n - e at heq
      omega
  have hE_U : E.card = U.card := by
    apply Nat.le_antisymm
    · exact hreflect_card 0 (by omega)
    · exact hreflect_card 1 (by omega)
  have hshift_t : ∀ d ∈ P, d + t ∈ O := by
    intro d hd
    obtain ⟨hdA, hdp⟩ := Finset.mem_filter.mp hd
    apply hcycles d hdA t (by simp)
    apply Nat.odd_iff.mpr
    omega
  have hshift_u : ∀ d ∈ P, d + u ∈ O := by
    intro d hd
    obtain ⟨hdA, hdp⟩ := Finset.mem_filter.mp hd
    apply hcycles d hdA u (by simp)
    apply Nat.odd_iff.mpr
    omega
  have hPbound : P.card ≤ k - 1 := by
    by_contra hfail
    have hP : P.Nonempty := Finset.card_pos.mp (by omega)
    have hcount : P.card + 1 ≤ O.card := by
      by_cases htu : t < u
      · exact contactOffsets_card_plus_one P O hP htu hshift_t hshift_u
      · exact contactOffsets_card_plus_one P O hP (by omega) hshift_u hshift_t
    omega
  have hEbound : E.card ≤ k - 1 := by
    by_cases htzero : t % 2 = 0
    · have hPU : P = U := by
        ext d
        simp only [P, U, Finset.mem_filter]
        constructor <;> rintro ⟨hA, hm⟩ <;> exact ⟨hA, by omega⟩
      rw [hPU] at hPbound
      omega
    · have hPE : P = E := by
        ext d
        simp only [P, E, Finset.mem_filter]
        constructor <;> rintro ⟨hA, hm⟩ <;> exact ⟨hA, by omega⟩
      simpa only [hPE] using hPbound
  have hUbound : U.card ≤ k - 1 := by omega
  have hnot : A.filter (fun d => ¬ d % 2 = 0) = U := by
    ext d
    simp only [U, Finset.mem_filter]
    constructor <;> rintro ⟨hA, hm⟩ <;> exact ⟨hA, by omega⟩
  have hpart : E.card + U.card = A.card := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (fun d => d % 2 = 0)
    simpa only [hnot, E] using h
  have hAupper : A.card ≤ 2 * k - 2 := by omega
  have hanchor : ∀ a ∈ S, contactAnchorDistances S a = A := by
    intro a ha
    have hsub : contactAnchorDistances S a ⊆ A := by
      intro d hd
      exact Finset.mem_biUnion.mpr ⟨a, ha, hd⟩
    have hcard := contactDistances_anchor_card S a ha hsize hk
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hSnonempty
  have hAcard : A.card = 2 * k - 2 := by
    rw [← hanchor a ha]
    exact contactDistances_anchor_card S a ha hsize hk
  have hEexact : E.card = k - 1 := by omega
  have hUexact : U.card = k - 1 := by omega
  refine ⟨hanchor, ?_, ?_⟩
  · simpa only [A, U, Nat.odd_iff] using hUexact
  · simpa only [A, E, Nat.even_iff] using hEexact

/-! ## Divisibility of contact gaps

Minimum-distance divisibility for a finite numerical contact-distance set.
The positive-difference and complement closures are explicit assumptions.
Their derivation from contact-distance invariance in an actual cycle is a
separate bridge; this module does not infer graph paths or cycle memberships.
-/

/-- A positive finite distance set closed under positive differences and
complements has a minimum dividing every distance and the ambient length.
For an odd ambient length, this minimum is odd; every even member is at least
twice the minimum. -/
theorem contact_gap_divisibility {n : ℕ} (D : Finset ℕ) (hD : D.Nonempty)
    (hpos : ∀ e ∈ D, 0 < e) (hbound : ∀ e ∈ D, e < n)
    (hdiff : ∀ d ∈ D, ∀ e ∈ D, d < e → e - d ∈ D)
    (hreflect : ∀ e ∈ D, n - e ∈ D) (hn : Odd n) :
    let d := D.min' hD
    0 < d ∧ d ∣ n ∧ Odd d ∧ (∀ e ∈ D, d ∣ e) ∧
      (∀ e ∈ D, Even e → 2 * d ≤ e) := by
  let d := D.min' hD
  have hdmem : d ∈ D := D.min'_mem hD
  have hdpos : 0 < d := hpos d hdmem
  have hall : ∀ e ∈ D, d ∣ e := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro he
      have hdle : d ≤ e := D.min'_le e he
      by_cases hde : d = e
      · rw [← hde]
      · have hlt : d < e := by omega
        have hsub : e - d ∈ D := hdiff d hdmem e he hlt
        have hsmall : e - d < e := Nat.sub_lt (hpos e he) hdpos
        have hdiv : d ∣ e - d := ih (e - d) hsmall hsub
        rw [show e = (e - d) + d by omega]
        exact dvd_add hdiv (dvd_refl d)
  have hddivn : d ∣ n := by
    have hnsub : n - d ∈ D := hreflect d hdmem
    have hdlt : d < n := hbound d hdmem
    rw [show n = (n - d) + d by omega]
    exact dvd_add (hall (n - d) hnsub) (dvd_refl d)
  have hdodd : Odd d := by
    apply Nat.odd_iff.mpr
    by_contra hnot
    have hdmod : d % 2 = 0 := by omega
    obtain ⟨q, hq⟩ := hddivn
    have hnzero : n % 2 = 0 := by
      rw [hq, Nat.mul_mod, hdmod]
      simp
    have hnone : n % 2 = 1 := Nat.odd_iff.mp hn
    omega
  have heven : ∀ e ∈ D, Even e → 2 * d ≤ e := by
    intro e he hep
    obtain ⟨q, hq⟩ := hall e he
    have hqzero : q ≠ 0 := by
      intro hzero
      have hepos := hpos e he
      simp [hq, hzero] at hepos
    have hqone : q ≠ 1 := by
      intro hone
      have hdeven : Even d := by simpa only [hq, hone, Nat.mul_one] using hep
      have hdzero : d % 2 = 0 := Nat.even_iff.mp hdeven
      have hdone : d % 2 = 1 := Nat.odd_iff.mp hdodd
      omega
    have hqge : 2 ≤ q := by omega
    calc
      2 * d = d * 2 := Nat.mul_comm _ _
      _ ≤ d * q := Nat.mul_le_mul_left d hqge
      _ = e := hq.symm
  exact ⟨hdpos, hddivn, hdodd, hall, heven⟩

/-! ## Structure of contact gaps -/

/-! Bridge from proved anchor-distance invariance to minimum-distance
divisibility, with reflection and positive-difference closure for actual
`ZMod` contact distances. -/

theorem contact_structure_bounds {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) {d : ℕ} (hd : d ∈ contactAllDistances S) :
    0 < d ∧ d < n := by
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1
  exact ⟨ZMod.val_pos.mpr hba, ZMod.val_lt _⟩

theorem contact_structure_reflect {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) {d : ℕ} (hd : d ∈ contactAllDistances S) :
    n - d ∈ contactAllDistances S := by
  obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1
  let : NeZero (b - a) := ⟨hba⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b, (Finset.mem_erase.mp hb).2, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1.symm, ha⟩, ?_⟩
  rw [show a - b = -(b - a) by abel, ZMod.val_neg_of_ne_zero]

theorem contact_structure_diff {n : ℕ} [NeZero n]
    (S : Finset (ZMod n))
    (hinvariant : ∀ a ∈ S, contactAnchorDistances S a = contactAllDistances S)
    {d e : ℕ} (hd : d ∈ contactAllDistances S) (he : e ∈ contactAllDistances S)
    (hde : d < e) : e - d ∈ contactAllDistances S := by
  obtain ⟨a, ha, hda⟩ := Finset.mem_biUnion.mp hd
  have hea : e ∈ contactAnchorDistances S a := by
    rw [hinvariant a ha]
    exact he
  obtain ⟨bd, hbd, hbdval⟩ := Finset.mem_image.mp hda
  obtain ⟨be, hbe, hbeval⟩ := Finset.mem_image.mp hea
  have hbe_ne_bd : be ≠ bd := by
    intro heq
    subst be
    omega
  have hval : (be - bd).val = e - d := by
    rw [show be - bd = (be - a) - (bd - a) by abel]
    rw [ZMod.val_sub (show (bd - a).val ≤ (be - a).val by omega), hbdval, hbeval]
  apply Finset.mem_biUnion.mpr
  refine ⟨bd, (Finset.mem_erase.mp hbd).2, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨be, Finset.mem_erase.mpr ⟨hbe_ne_bd, (Finset.mem_erase.mp hbe).2⟩, hval⟩

theorem contact_odd_arc_has_outside_contact {n d : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (hn : Odd n) (hd : d ∈ contactAllDistances S)
    (hdodd : Odd d) (hminimum : ∀ e ∈ contactAllDistances S, d ≤ e)
    (hinvariant : ∀ a ∈ S, contactAnchorDistances S a = contactAllDistances S)
    {a : ZMod n} (ha : a ∈ S) {δ : ℕ}
    (hδ : δ ∈ contactAnchorDistances S a) (hδodd : Odd δ) :
    ∃ b, b ∈ S ∧ b ≠ a ∧ δ < (b - a).val := by
  have hδglobal : δ ∈ contactAllDistances S := by
    rw [← hinvariant a ha]
    exact hδ
  have hδlt := (contact_structure_bounds S hδglobal).2
  have hdlt := (contact_structure_bounds S hd).2
  have hcomplement := contact_structure_reflect S hδglobal
  have hmin := hminimum (n - δ) hcomplement
  have hnmod := Nat.odd_iff.mp hn
  have hdmod := Nat.odd_iff.mp hdodd
  have hδmod := Nat.odd_iff.mp hδodd
  have hstrict : δ < n - d := by omega
  have hanchor : n - d ∈ contactAnchorDistances S a := by
    rw [hinvariant a ha]
    exact contact_structure_reflect S hd
  obtain ⟨b, hb, hval⟩ := Finset.mem_image.mp hanchor
  refine ⟨b, (Finset.mem_erase.mp hb).2, (Finset.mem_erase.mp hb).1, ?_⟩
  omega

theorem contact_gap_structure {n : ℕ} (S : Finset (ZMod n))
    (hn : Odd n) (hD : (contactAllDistances S).Nonempty)
    (hinvariant : ∀ a ∈ S, contactAnchorDistances S a = contactAllDistances S) :
    ∃ d, d ∈ contactAllDistances S ∧
      (∀ e ∈ contactAllDistances S, d ≤ e) ∧
      0 < d ∧ d ∣ n ∧ Odd d ∧
      (∀ e ∈ contactAllDistances S, d ∣ e) ∧
      (∀ e ∈ contactAllDistances S, Even e → 2 * d ≤ e) := by
  have hnne : n ≠ 0 := by
    have hnmod := Nat.odd_iff.mp hn
    omega
  let : NeZero n := ⟨hnne⟩
  let D := contactAllDistances S
  have hpos : ∀ e ∈ D, 0 < e := fun e he => (contact_structure_bounds S he).1
  have hbound : ∀ e ∈ D, e < n := fun e he => (contact_structure_bounds S he).2
  have hdiff : ∀ d ∈ D, ∀ e ∈ D, d < e → e - d ∈ D := by
    intro d hd e he hde
    exact contact_structure_diff S hinvariant hd he hde
  have hreflect : ∀ e ∈ D, n - e ∈ D := fun e he => contact_structure_reflect S he
  have hdiv := contact_gap_divisibility D hD hpos hbound hdiff hreflect hn
  refine ⟨D.min' hD, D.min'_mem hD, ?_, hdiv⟩
  intro e he
  exact D.min'_le e he

/-! ## Fan arithmetic -/

/-- Signed integer differences between two finite sets. -/
public def signedDifferences (A B : Finset ℤ) : Finset ℤ :=
  (A.product B).image (fun ij => ij.1 - ij.2)

/-- Membership characterization for cross-module consumers. -/
theorem mem_signedDifferences {A B : Finset ℤ} {z : ℤ} :
    z ∈ signedDifferences A B ↔ ∃ s t, s ∈ A ∧ t ∈ B ∧ z = s - t := by
  simp [signedDifferences, Finset.mem_image, Finset.mem_product]
  tauto

/-- The elementary integer sumset bound, proved by joining two monotone chains
at the difference of the two maxima. -/
theorem card_signedDifferences_ge (A B : Finset ℤ)
    (ha : A.Nonempty) (hb : B.Nonempty) :
    A.card + B.card ≤ (signedDifferences A B).card + 1 := by
  classical
  let a := A.max' ha
  let b := B.max' hb
  have ham : a ∈ A := A.max'_mem ha
  have hbm : b ∈ B := B.max'_mem hb
  let U := A.image (fun x => x - b)
  let W := (B.erase b).image (fun y => a - y)
  have hU : U.card = A.card := Finset.card_image_of_injective A (by
    intro x y h
    exact sub_left_injective h)
  have hW : W.card = (B.erase b).card :=
    Finset.card_image_of_injective _ (by
      intro x y h
      exact sub_right_injective h)
  have hd : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzW
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hzU
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hzW
    have hxle : x ≤ a := A.le_max' x hx
    have hyle : y ≤ b := B.le_max' y (Finset.mem_erase.mp hy).2
    have hyne : y ≠ b := (Finset.mem_erase.mp hy).1
    omega
  have hsub : U ∪ W ⊆ signedDifferences A B := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨(x, b), Finset.mem_product.mpr ⟨hx, hbm⟩, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr
        ⟨(a, y), Finset.mem_product.mpr ⟨ham, (Finset.mem_erase.mp hy).2⟩, rfl⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hU, hW] at hle
  have herase := Finset.card_erase_add_one hbm
  omega

/-- Taking natural absolute values identifies at most two integers. -/
theorem card_le_two_mul_card_natAbs_image (X : Finset ℤ) :
    X.card ≤ 2 * (X.image Int.natAbs).card := by
  classical
  let P := X.filter (fun x => 0 ≤ x)
  let N := X.filter (fun x => x < 0)
  have hP : Set.InjOn Int.natAbs P := by
    intro x hx y hy heq
    have hxpos := (Finset.mem_filter.mp hx).2
    have hypos := (Finset.mem_filter.mp hy).2
    rcases Int.natAbs_eq_natAbs_iff.mp heq with heq | heq
    · exact heq
    · omega
  have hN : Set.InjOn Int.natAbs N := by
    intro x hx y hy heq
    have hxneg := (Finset.mem_filter.mp hx).2
    have hyneg := (Finset.mem_filter.mp hy).2
    rcases Int.natAbs_eq_natAbs_iff.mp heq with heq | heq
    · exact heq
    · omega
  have hPi : P.image Int.natAbs ⊆ X.image Int.natAbs :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hNi : N.image Int.natAbs ⊆ X.image Int.natAbs :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hp := Finset.card_le_card hPi
  have hn := Finset.card_le_card hNi
  rw [Finset.card_image_of_injOn hP] at hp
  rw [Finset.card_image_of_injOn hN] at hn
  have hparts : P.card + N.card = X.card := by
    simpa only [P, N, not_le] using
      (Finset.card_filter_add_card_filter_not (s := X) (fun x => 0 ≤ x))
  omega

/-- An absolute value occurring with only one sign improves the folding bound
by one. -/
theorem card_lt_two_mul_card_natAbs_image_of_unpaired_neg (X : Finset ℤ) (L : ℕ)
    (hneg : -(L : ℤ) ∈ X) (hpos : (L : ℤ) ∉ X) :
    X.card < 2 * (X.image Int.natAbs).card := by
  classical
  have hLmem : L ∈ X.image Int.natAbs := by
    exact Finset.mem_image.mpr ⟨-(L : ℤ), hneg, by simp⟩
  have heq : (X.erase (-(L : ℤ))).image Int.natAbs =
      (X.image Int.natAbs).erase L := by
    ext n
    constructor
    · intro hn
      obtain ⟨x, hx, hxn⟩ := Finset.mem_image.mp hn
      obtain ⟨hxne, hx⟩ := Finset.mem_erase.mp hx
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image.mpr ⟨x, hx, hxn⟩⟩
      intro hnL
      have habs : x.natAbs = (L : ℤ).natAbs := by simpa [hnL] using hxn
      rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
      · exact hpos (h ▸ hx)
      · exact hxne h
    · intro hn
      obtain ⟨hnne, hn⟩ := Finset.mem_erase.mp hn
      obtain ⟨x, hx, hxn⟩ := Finset.mem_image.mp hn
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_erase.mpr ⟨?_, hx⟩, hxn⟩
      intro hxneg
      subst x
      have hnL : L = n := by simpa using hxn
      exact hnne hnL.symm
  have hweak := card_le_two_mul_card_natAbs_image (X.erase (-(L : ℤ)))
  rw [heq] at hweak
  have hxcard := Finset.card_erase_add_one hneg
  have habscard := Finset.card_erase_add_one hLmem
  omega

/-- Positive odd differences of elements of a finite natural-number set. -/
public def oddPositiveDifferences (S : Finset ℕ) : Finset ℕ :=
  ((S.product S).filter (fun ij => ij.1 < ij.2 ∧ Odd (ij.2 - ij.1))).image
    (fun ij => ij.2 - ij.1)

/-- Membership characterization for cross-module consumers. -/
theorem mem_oddPositiveDifferences {S : Finset ℕ} {d : ℕ} :
    d ∈ oddPositiveDifferences S ↔
      ∃ i j : ℕ, (i ∈ S ∧ j ∈ S ∧ i < j ∧ Odd (j - i)) ∧ d = j - i := by
  rw [oddPositiveDifferences, Finset.mem_image]
  constructor
  · rintro ⟨a, hab, rfl⟩
    have hprod : a ∈ S.product S := (Finset.mem_filter.mp hab).1
    have hfilter : a.1 < a.2 ∧ Odd (a.2 - a.1) := (Finset.mem_filter.mp hab).2
    obtain ⟨hlt, hodd⟩ := hfilter
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hprod
    exact ⟨a.1, a.2, ⟨ha, hb, hlt, hodd⟩, rfl⟩
  · rintro ⟨i, j, ha, hb, hlt, hodd, rfl⟩
    refine ⟨(i, j), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha.1, ha.2.1⟩, ha.2.2.1, ha.2.2.2⟩

/-- Absolute differences between an even and an odd element are positive odd
differences in the order used by `oddPositiveDifferences`. -/
theorem natAbs_image_signedDifferences_subset_oddPositiveDifferences (S : Finset ℕ) :
    (signedDifferences ((S.filter Even).image (fun x : ℕ => (x : ℤ)))
      ((S.filter Odd).image (fun x : ℕ => (x : ℤ)))).image Int.natAbs ⊆
    oddPositiveDifferences S := by
  classical
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨heS, he⟩ := Finset.mem_filter.mp he
  obtain ⟨hoS, ho⟩ := Finset.mem_filter.mp ho
  have hne : e ≠ o := by
    intro h
    subst o
    exact (Nat.not_even_iff_odd.mpr ho) he
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hodd : Odd (o - e) := (Nat.odd_sub hlt.le).mpr (iff_of_true ho he)
    exact Finset.mem_image.mpr ⟨(e, o),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heS, hoS⟩, hlt, hodd⟩,
      (Int.natAbs_natCast_sub_natCast_of_le hlt.le).symm⟩
  · have hodd : Odd (e - o) := (Nat.odd_sub' hlt.le).mpr (iff_of_true ho he)
    exact Finset.mem_image.mpr ⟨(o, e),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hoS, heS⟩, hlt, hodd⟩,
      (Int.natAbs_natCast_sub_natCast_of_ge hlt.le).symm⟩

/-- Every natural-number set of at least `2*k+1` elements containing both
parities has at least `k` distinct positive odd differences. -/
theorem card_oddPositiveDifferences_ge (S : Finset ℕ) (k : ℕ)
    (he : (S.filter Even).Nonempty) (ho : (S.filter Odd).Nonempty)
    (hsize : 2 * k + 1 ≤ S.card) :
    k ≤ (oddPositiveDifferences S).card := by
  classical
  let E := S.filter Even
  let O := S.filter Odd
  let A := E.image (fun x : ℕ => (x : ℤ))
  let B := O.image (fun x : ℕ => (x : ℤ))
  have ha : A.Nonempty := he.image _
  have hb : B.Nonempty := ho.image _
  have hAc : A.card = E.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hBc : B.card = O.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hpart : E.card + O.card = S.card := by
    simpa only [E, O, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not (s := S) Even)
  have hdiff := card_signedDifferences_ge A B ha hb
  rw [hAc, hBc, hpart] at hdiff
  have habs := card_le_two_mul_card_natAbs_image (signedDifferences A B)
  have hcard := Finset.card_le_card
    (natAbs_image_signedDifferences_subset_oddPositiveDifferences S)
  change ((signedDifferences A B).image Int.natAbs).card ≤ _ at hcard
  omega

/-- If a set ranges from zero to an odd maximum, the unmatched extreme signed
difference supplies one more positive odd difference. -/
theorem card_oddPositiveDifferences_ge_of_odd_endpoints (S : Finset ℕ) (k L : ℕ)
    (h0 : 0 ∈ S) (hL : L ∈ S) (hOdd : Odd L)
    (hmax : ∀ x ∈ S, x ≤ L) (hsize : 2 * k + 1 ≤ S.card) :
    k + 1 ≤ (oddPositiveDifferences S).card := by
  classical
  let E := S.filter Even
  let O := S.filter Odd
  let A := E.image (fun x : ℕ => (x : ℤ))
  let B := O.image (fun x : ℕ => (x : ℤ))
  have hAm : (0 : ℤ) ∈ A :=
    Finset.mem_image.mpr ⟨0, Finset.mem_filter.mpr ⟨h0, by simp⟩, rfl⟩
  have hBm : (L : ℤ) ∈ B :=
    Finset.mem_image.mpr ⟨L, Finset.mem_filter.mpr ⟨hL, hOdd⟩, rfl⟩
  have hAc : A.card = E.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hBc : B.card = O.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hpart : E.card + O.card = S.card := by
    simpa only [E, O, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not (s := S) Even)
  have hdiff := card_signedDifferences_ge A B ⟨0, hAm⟩ ⟨L, hBm⟩
  rw [hAc, hBc, hpart] at hdiff
  have hneg : -(L : ℤ) ∈ signedDifferences A B := by
    apply Finset.mem_image.mpr
    exact ⟨(0, L), Finset.mem_product.mpr ⟨hAm, hBm⟩, by simp⟩
  have hpos : (L : ℤ) ∉ signedDifferences A B := by
    intro h
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨heS, _⟩ := Finset.mem_filter.mp he
    obtain ⟨_, ho⟩ := Finset.mem_filter.mp ho
    have hemax := hmax e heS
    have hopos : 0 < o := ho.pos
    change (e : ℤ) - (o : ℤ) = L at heq
    omega
  have habs := card_lt_two_mul_card_natAbs_image_of_unpaired_neg
    (signedDifferences A B) L hneg hpos
  have hcard := Finset.card_le_card
    (natAbs_image_signedDifferences_subset_oddPositiveDifferences S)
  change ((signedDifferences A B).image Int.natAbs).card ≤ _ at hcard
  omega

/-! ## Fan rigidity arithmetic -/

/-- Two injective odd-length maps force the endpoint gap to occur. The inputs
are natural numbers; no graph-theoretic assertion is assumed implicitly. -/
theorem fan_numeric_gap (n k : ℕ) (D L : Finset ℕ)
    (hrange : ∀ d ∈ D, 0 < d ∧ d < n)
    (hcard : 2 * k ≤ D.card) (hn : n ∈ L) (hL : L.card ≤ k)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ L)
    (heven : ∀ d ∈ D, Even d → n - d + 2 ∈ L) :
    D.card = 2 * k ∧ n - 2 ∈ D := by
  classical
  let E := D.filter Even
  let O := D.filter Odd
  have hpart : E.card + O.card = D.card := by
    simpa only [E, O, Nat.not_even_iff_odd] using
      (Finset.card_filter_add_card_filter_not (s := D) Even)
  have hEs : E.image (fun d => n - d + 2) ⊆ L := by
    intro l hl
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hl
    exact heven d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
  have hEi : Set.InjOn (fun d => n - d + 2) E := by
    intro d hd e he hde
    have hdlt := (hrange d (Finset.mem_filter.mp hd).1).2
    have helt := (hrange e (Finset.mem_filter.mp he).1).2
    change n - d + 2 = n - e + 2 at hde
    omega
  have hEc : E.card ≤ k := by
    have h := Finset.card_le_card hEs
    rw [Finset.card_image_of_injOn hEi] at h
    omega
  have hOs : O.image (fun d => d + 2) ⊆ L := by
    intro l hl
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hl
    exact hodd d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
  have hOi : Function.Injective (fun d : ℕ => d + 2) := by
    intro d e h
    exact Nat.add_right_cancel h
  have hOc : O.card ≤ k := by
    have h := Finset.card_le_card hOs
    rw [Finset.card_image_of_injective O hOi] at h
    omega
  have hOk : O.card = k := by omega
  have hOeq : O.image (fun d => d + 2) = L := by
    apply Finset.eq_of_subset_of_card_le hOs
    rw [Finset.card_image_of_injective O hOi, hOk]
    exact hL
  have hnO : n ∈ O.image (fun d => d + 2) := hOeq.symm ▸ hn
  obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hnO
  have hdD := (Finset.mem_filter.mp hd).1
  have hdne : d = n - 2 := by omega
  exact ⟨by omega, hdne ▸ hdD⟩

/-- On an odd cyclic group, a nonempty finite set closed under subtracting two
contains every residue. -/
theorem zmod_eq_univ_of_closed_sub_two (n : ℕ) [NeZero n] (hodd : Odd n)
    (S : Finset (ZMod n)) (hne : S.Nonempty)
    (hclosed : ∀ a ∈ S, a - 2 ∈ S) : S = Finset.univ := by
  classical
  obtain ⟨a, ha⟩ := hne
  have horbit : ∀ t : ℕ, a - (t : ZMod n) * 2 ∈ S := by
    intro t
    induction t with
    | zero => simpa using ha
    | succ t ih =>
      have h := hclosed _ ih
      have heq : a - ((t + 1 : ℕ) : ZMod n) * 2 =
          (a - (t : ZMod n) * 2) - 2 := by
        push_cast
        ring
      exact heq ▸ h
  apply Finset.eq_univ_of_forall
  intro b
  let x := (a - b).val
  have hxcast : (x : ZMod n) = a - b := ZMod.natCast_zmod_val _
  have hrepr : ∃ t : ℕ, (t : ZMod n) * 2 = (x : ZMod n) := by
    by_cases hx : Even x
    · obtain ⟨t, ht⟩ := hx
      refine ⟨t, ?_⟩
      rw [ht]
      push_cast
      ring
    · obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp hx
      obtain ⟨q, hq⟩ := hodd
      let t := p + q + 1
      have ht : x + n = t + t := by dsimp [t]; omega
      have hcast := congrArg (fun z : ℕ => (z : ZMod n)) ht
      push_cast at hcast
      rw [ZMod.natCast_self, add_zero] at hcast
      refine ⟨t, ?_⟩
      rw [hcast]
      ring
  obtain ⟨t, ht⟩ := hrepr
  have heq : a - (t : ZMod n) * 2 = b := by
    rw [ht, hxcast]
    ring
  exact heq ▸ horbit t

/-- Proper cyclic forward distances from a fixed residue to the other members
of a set. -/
def cyclicForwardDistances (n : ℕ) (S : Finset (ZMod n)) (a : ZMod n) : Finset ℕ :=
  (S.erase a).image (fun b => (b - a).val)

/-- Numeric rigidity for spokes from an exterior vertex to an odd cycle.
The two length-oracle hypotheses must be supplied by actual graph cycles. -/
theorem odd_cyclic_fan_rigidity (n k : ℕ) [NeZero n] (hodd : Odd n)
    (S : Finset (ZMod n)) (L : Finset ℕ)
    (hsize : 2 * k + 1 ≤ S.card) (hn : n ∈ L) (hL : L.card ≤ k)
    (hforward : ∀ a ∈ S, ∀ b ∈ S, b ≠ a →
      Odd (b - a).val → (b - a).val + 2 ∈ L)
    (hbackward : ∀ a ∈ S, ∀ b ∈ S, b ≠ a →
      Even (b - a).val → n - (b - a).val + 2 ∈ L) :
    S = Finset.univ ∧ n = 2 * k + 1 := by
  classical
  have hcalc (a : ZMod n) (ha : a ∈ S) :
      S.card = 2 * k + 1 ∧ a - 2 ∈ S := by
    let D := cyclicForwardDistances n S a
    have hi : Function.Injective (fun b : ZMod n => (b - a).val) := by
      intro b c h
      exact sub_left_injective (ZMod.val_injective n h)
    have hDc : D.card = (S.erase a).card := Finset.card_image_of_injective _ hi
    have hSc := Finset.card_erase_add_one ha
    have hrange : ∀ d ∈ D, 0 < d ∧ d < n := by
      intro d hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      have hba := (Finset.mem_erase.mp hb).1
      have hz : (b - a).val ≠ 0 := by
        intro h
        have hzero : b - a = 0 := ZMod.val_injective n (by simpa using h)
        exact hba (sub_eq_zero.mp hzero)
      exact ⟨Nat.pos_of_ne_zero hz, ZMod.val_lt _⟩
    have hDsize : 2 * k ≤ D.card := by omega
    have ho : ∀ d ∈ D, Odd d → d + 2 ∈ L := by
      intro d hd hod
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hba, hb⟩ := Finset.mem_erase.mp hb
      exact hforward a ha b hb hba hod
    have he : ∀ d ∈ D, Even d → n - d + 2 ∈ L := by
      intro d hd hed
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hba, hb⟩ := Finset.mem_erase.mp hb
      exact hbackward a ha b hb hba hed
    obtain ⟨hDcard, hgap⟩ := fan_numeric_gap n k D L hrange hDsize hn hL ho he
    have hn2 : 2 ≤ n := by
      have h := (hrange (n - 2) hgap).1
      omega
    obtain ⟨b, hb, hval⟩ := Finset.mem_image.mp hgap
    have hcast := ZMod.natCast_zmod_val (b - a)
    rw [hval, Nat.cast_sub hn2, ZMod.natCast_self, zero_sub] at hcast
    have heq : b = a - 2 := by
      linear_combination -hcast
    exact ⟨by omega, heq ▸ (Finset.mem_erase.mp hb).2⟩
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  have hfull : S = Finset.univ :=
    zmod_eq_univ_of_closed_sub_two n hodd S hnonempty (fun a ha => (hcalc a ha).2)
  obtain ⟨a, ha⟩ := hnonempty
  have hcard := (hcalc a ha).1
  rw [hfull, Finset.card_univ, ZMod.card] at hcard
  exact ⟨hfull, hcard⟩

/-! ## Cycle-length sets

Definitions `cycleLengths` and `oddCycleLengths` follow the Apache-2.0
Formal Conjectures Authors' Circumference.lean (2026) and are restated here so
that the package compiles on its pinned toolchain.
-/

end Erdos58

namespace SimpleGraph

public def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m | ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

public def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

end SimpleGraph

namespace Erdos58

variable {V : Type*} {G : SimpleGraph V}

/-- Public membership interface for the package-local odd-cycle-length set. -/
public theorem mem_cycleLengths {n : ℕ} (h : n ∈ G.cycleLengths) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := h

/-- Public membership interface for the package-local cycle-length set. -/
public theorem mem_cycleLengths_intro {n : ℕ} {v : V} {p : G.Walk v v}
    (hc : p.IsCycle) (hlen : p.length = n) :
    n ∈ G.cycleLengths := ⟨v, p, hc, hlen⟩

public theorem cycleLengths_ext_iff {n : ℕ} :
    n ∈ G.cycleLengths ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n :=
  Iff.rfl

public theorem mem_oddCycleLengths_intro {n : ℕ} {v : V} {p : G.Walk v v}
    (hc : p.IsCycle) (hlen : p.length = n) (hodd : Odd n) :
    n ∈ G.oddCycleLengths := by
  exact ⟨⟨v, p, hc, hlen⟩, hodd⟩

theorem mem_oddCycleLengths_intro_internal {n : ℕ} {v : V} {p : G.Walk v v}
    (hc : p.IsCycle) (hlen : p.length = n) (hodd : Odd n) :
    n ∈ G.oddCycleLengths := by
  exact mem_oddCycleLengths_intro hc hlen hodd

/-- Public elimination interface for the package-local odd-cycle-length set. -/
theorem mem_oddCycleLengths_elim {n : ℕ} (h : n ∈ G.oddCycleLengths) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n ∧ Odd n := by
  unfold SimpleGraph.oddCycleLengths SimpleGraph.cycleLengths at h
  obtain ⟨hCycle, hOdd⟩ := h
  obtain ⟨v, p, hp, hlen⟩ := hCycle
  exact ⟨v, p, hp, hlen, hOdd⟩

/-- The properties of a finite normal DFS forest needed by the coloring proof.
They require actual simple graph paths, not merely numerical depth labels. -/
structure NormalDepth {V : Type*} (G : SimpleGraph V) where
  depth : V → ℕ
  edge_ne : ∀ {u v}, G.Adj u v → depth u ≠ depth v
  earlier_injective : ∀ {v u w}, G.Adj u v → G.Adj w v →
    depth u < depth v → depth w < depth v → depth u = depth w → u = w
  back_path : ∀ {u v}, G.Adj u v → depth u < depth v →
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = depth v - depth u

/-! ## Path offsets

Arithmetic classification of the endpoint-chord path lengths in Gyárfás
Lemma 6. This module makes no claim that the numerical paths or cycles exist;
those geometric constructions must be proved separately.

For crossing, distinct internal endpoint chords, the three intervening
segments have positive lengths `a`, `b`, `c`. The four candidate A–B path
lengths are `a+1`, `c+1`, `b+2`, and `a+b+c`.
-/

private theorem pathOffsets_three_le_card {R : Finset ℕ} {x y z : ℕ}
    (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ R.card := by
  have hsub : ({x, y, z} : Finset ℕ) ⊆ R := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hc : ({x, y, z} : Finset ℕ).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hxy, hxz, hyz⟩
  have h := Finset.card_le_card hsub
  omega

/-- The four numerical candidates for crossing endpoint-chord paths. -/
public def crossingPathLengths (a b c : ℕ) : Finset ℕ :=
  {a + 1, c + 1, b + 2, a + b + c}

/-- Positive crossing segments admit at most two path lengths only in the
two exceptional configurations. The shared chord `AB` is outside this model. -/
theorem crossing_path_lengths_classification {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcard : (crossingPathLengths a b c).card ≤ 2) :
    a = c ∧ (a = b + 1 ∨ a = 1) := by
  have hac : a = c := by
    by_contra hne
    have hthree := pathOffsets_three_le_card
      (R := crossingPathLengths a b c)
      (x := a + 1) (y := c + 1) (z := a + b + c)
      (by simp [crossingPathLengths])
      (by simp [crossingPathLengths])
      (by simp [crossingPathLengths])
      (by omega) (by omega) (by omega)
    omega
  refine ⟨hac, ?_⟩
  by_contra hfail
  have hab : a ≠ b + 1 := fun h => hfail (Or.inl h)
  have haone : a ≠ 1 := fun h => hfail (Or.inr h)
  have hthree := pathOffsets_three_le_card
    (R := crossingPathLengths a b c)
    (x := a + 1) (y := b + 2) (z := a + b + c)
    (by simp [crossingPathLengths])
    (by simp [crossingPathLengths])
    (by simp [crossingPathLengths])
    (by omega) (by omega) (by omega)
  omega

theorem crossing_path_lengths_balanced (b : ℕ) :
    crossingPathLengths (b + 1) b (b + 1) = {b + 2, 3 * b + 2} := by
  ext n
  simp only [crossingPathLengths, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem crossing_path_lengths_unit (b : ℕ) :
    crossingPathLengths 1 b 1 = {2, b + 2} := by
  ext n
  simp only [crossingPathLengths, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem crossing_path_lengths_card_le_two_iff {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (crossingPathLengths a b c).card ≤ 2 ↔
      a = c ∧ (a = b + 1 ∨ a = 1) := by
  refine ⟨crossing_path_lengths_classification ha hb hc, ?_⟩
  rintro ⟨hac, hab | haone⟩
  · subst c
    subst a
    rw [crossing_path_lengths_balanced]
    exact Finset.card_le_two
  · subst c
    subst a
    rw [crossing_path_lengths_unit]
    exact Finset.card_le_two

public theorem crossingPathLengths_ext_iff (a b c : ℕ) :
    crossingPathLengths a b c = {a + 1, c + 1, b + 2, a + b + c} := by
  simp [crossingPathLengths]

/-- Offsets obtained from the one-exterior-vertex path and the A–B paths. -/
public def pathLengthOffsets (R : Finset ℕ) : Finset ℕ :=
  insert 2 (R.image (fun h => h + 2))

theorem balanced_path_offsets (b : ℕ) :
    pathLengthOffsets (crossingPathLengths (b + 1) b (b + 1)) =
      {2, b + 4, 3 * b + 4} := by
  ext n
  simp [pathLengthOffsets, crossing_path_lengths_balanced]

theorem unit_path_offsets (b : ℕ) :
    pathLengthOffsets (crossingPathLengths 1 b 1) = {2, 4, b + 4} := by
  ext n
  simp [pathLengthOffsets, crossing_path_lengths_unit]

theorem balanced_path_offsets_card {b : ℕ} (hb : 0 < b) :
    (pathLengthOffsets (crossingPathLengths (b + 1) b (b + 1))).card = 3 := by
  rw [balanced_path_offsets]
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨by omega, by omega, by omega⟩

theorem unit_path_offsets_card {b : ℕ} (hb : 0 < b) :
    (pathLengthOffsets (crossingPathLengths 1 b 1)).card = 3 := by
  rw [unit_path_offsets]
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨by omega, by omega, by omega⟩

theorem balanced_path_offsets_even {b : ℕ} (hb : Even b) :
    ∀ n ∈ pathLengthOffsets (crossingPathLengths (b + 1) b (b + 1)), Even n := by
  rw [balanced_path_offsets]
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  obtain ⟨q, hq⟩ := hb
  rcases hn with rfl | rfl | rfl
  · exact ⟨1, by omega⟩
  · exact ⟨q + 2, by omega⟩
  · exact ⟨3 * q + 2, by omega⟩

theorem balanced_path_offsets_two_odd {b : ℕ} (_hpos : 0 < b) (hb : Odd b) :
    Odd (b + 4) ∧ Odd (3 * b + 4) ∧ b + 4 ≠ 3 * b + 4 ∧
      b + 4 ∈ pathLengthOffsets (crossingPathLengths (b + 1) b (b + 1)) ∧
      3 * b + 4 ∈ pathLengthOffsets (crossingPathLengths (b + 1) b (b + 1)) := by
  obtain ⟨q, hq⟩ := hb
  refine ⟨⟨q + 2, by omega⟩, ⟨3 * q + 3, by omega⟩, by omega, ?_, ?_⟩
  · rw [balanced_path_offsets]
    simp
  · rw [balanced_path_offsets]
    simp

theorem unit_path_offsets_even {b : ℕ} (hb : Even b) :
    ∀ n ∈ pathLengthOffsets (crossingPathLengths 1 b 1), Even n := by
  rw [unit_path_offsets]
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  obtain ⟨q, hq⟩ := hb
  rcases hn with rfl | rfl | rfl
  · exact ⟨1, by omega⟩
  · exact ⟨2, by omega⟩
  · exact ⟨q + 2, by omega⟩

theorem unit_path_offsets_odd {b : ℕ} (hpos : 0 < b) (hb : Odd b) :
    Even 2 ∧ Even 4 ∧ Odd (b + 4) ∧ 4 < b + 4 := by
  obtain ⟨q, hq⟩ := hb
  exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨q + 2, by omega⟩, by omega⟩

/-- Noncrossing endpoint diagonals, with both skipped endpoint segments
at least two edges, supply at least three different numerical path lengths.
The middle segment may have length zero, covering a common internal contact. -/
theorem noncrossing_path_lengths_card {a b c : ℕ}
    (ha : 2 ≤ a) (hc : 2 ≤ c) :
    3 ≤ ({b + 2, b + c + 1, a + b + 1, a + b + c} : Finset ℕ).card := by
  apply pathOffsets_three_le_card
    (x := b + 2) (y := b + c + 1) (z := a + b + c)
  · simp
  · simp
  · simp
  · omega
  · omega
  · omega

/-! ## Two-connector configurations

Elementary two-path fans, for the structural equality direction of Erdős #58.
All witnesses are actual simple walks with explicitly controlled supports.
-/

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

/-- A segment avoiding the tripod except at its two attachments moves its center
strictly toward the root. Repeated vertices in the spliced walks are bypassed. -/
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

/-- Attach a path reaching one branch of a fan to that branch. Its resulting
support is disjoint from the other branch, including the original fan root. -/
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

/-! ## Normal depth -/

open SimpleGraph

/-- A normal depth function with a prescribed root and actual simple paths
from that root. This extra information supports the recursive construction. -/
structure RootedNormalDepth {V : Type*} (G : SimpleGraph V) (root : V)
    extends NormalDepth G where
  root_depth : depth root = 0
  root_path : ∀ v, ∃ p : G.Walk root v, p.IsPath ∧ p.length = depth v

variable {V : Type*} (G : SimpleGraph V) (root : V)

abbrev Deleted := {v : V // v ≠ root}

abbrev deletedGraph : SimpleGraph (Deleted root) := G.induce {v | v ≠ root}

abbrev deletedHom : deletedGraph G root →g G := (Embedding.induce {v | v ≠ root}).toHom

lemma deletedHom_injective : Function.Injective (deletedHom G root) :=
  Subtype.val_injective

lemma reachable_neighbor {x : V} (hx : x ≠ root) (p : G.Walk x root) :
    ∃ a : Deleted root, (deletedGraph G root).Reachable ⟨x, hx⟩ a ∧ G.Adj a.val root := by
  let rec aux {x : V} (hx : x ≠ root) (p : G.Walk x root) :
      ∃ a : Deleted root, (deletedGraph G root).Reachable ⟨x, hx⟩ a ∧ G.Adj a.val root := by
    cases p with
    | nil => exact (hx rfl).elim
    | @cons _ y _ h p =>
      by_cases hy : y = root
      · subst y
        exact ⟨⟨x, hx⟩, .rfl, h⟩
      · obtain ⟨a, ha, har⟩ := aux hy p
        exact ⟨a, (show (deletedGraph G root).Adj ⟨x, hx⟩ ⟨y, hy⟩ from h).reachable.trans ha, har⟩
  exact aux hx p

lemma component_neighbor (hG : G.Connected)
    (c : (deletedGraph G root).ConnectedComponent) :
    ∃ a : c, G.Adj root a.val.val := by
  obtain ⟨x, hx⟩ := c.nonempty_supp
  obtain ⟨a, ha, har⟩ := reachable_neighbor G root x.property
    (hG.preconnected x.val root).some
  refine ⟨⟨a, ?_⟩, har.symm⟩
  exact (ConnectedComponent.mem_supp_iff c a).2
    ((ConnectedComponent.sound ha).symm.trans hx)

abbrev componentHom (c : (deletedGraph G root).ConnectedComponent) : c.toSimpleGraph →g G :=
  (deletedHom G root).comp c.toSimpleGraph_hom

lemma componentHom_injective (c : (deletedGraph G root).ConnectedComponent) :
    Function.Injective (componentHom G root c) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

lemma componentHom_not_root (c : (deletedGraph G root).ConnectedComponent) (v : c) :
    componentHom G root c v ≠ root := v.val.property

lemma component_card_lt [Fintype V] (c : (deletedGraph G root).ConnectedComponent) :
    Nat.card c < Fintype.card V := by
  classical
  let := Fintype.ofFinite c
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem (componentHom G root c)
    (componentHom_injective G root c) (by
      rintro ⟨v, hv⟩
      exact componentHom_not_root G root c v hv)

section Glue

variable (a : (c : (deletedGraph G root).ConnectedComponent) → c)
variable (R : (c : (deletedGraph G root).ConnectedComponent) →
  RootedNormalDepth c.toSimpleGraph (a c))

noncomputable def gluedDepth (v : V) : ℕ := by
  classical
  exact if h : v = root then 0 else
    (R ((deletedGraph G root).connectedComponentMk ⟨v, h⟩)).depth ⟨⟨v, h⟩, rfl⟩ + 1

lemma gluedDepth_root : gluedDepth G root a R root = 0 := by
  classical
  simp [gluedDepth]

lemma gluedDepth_component (c : (deletedGraph G root).ConnectedComponent) (v : c) :
    gluedDepth G root a R v.val.val = (R c).depth v + 1 := by
  classical
  rcases v with ⟨v, hv⟩
  change (deletedGraph G root).connectedComponentMk v = c at hv
  subst c
  simp [gluedDepth, v.property]

lemma gluedDepth_pos {v : V} (hv : v ≠ root) : 0 < gluedDepth G root a R v := by
  classical
  simp [gluedDepth, hv]

lemma gluedRootPath (ha : ∀ c, G.Adj root (a c).val.val) (v : V) :
    ∃ p : G.Walk root v, p.IsPath ∧ p.length = gluedDepth G root a R v := by
  classical
  by_cases hv : v = root
  · subst v
    exact ⟨.nil, by simp, by simp [gluedDepth_root]⟩
  · let c := (deletedGraph G root).connectedComponentMk ⟨v, hv⟩
    let vc : c := ⟨⟨v, hv⟩, rfl⟩
    obtain ⟨p, hp, hl⟩ := (R c).root_path vc
    let f := componentHom G root c
    have hf : Function.Injective f := componentHom_injective G root c
    have hr : root ∉ (p.map f).support := by
      simp only [Walk.support_map, List.mem_map]
      rintro ⟨b, _, hb⟩
      exact componentHom_not_root G root c b hb
    refine ⟨.cons (ha c) (p.map f), hp.map hf |>.cons hr, ?_⟩
    change (p.map f).length + 1 = gluedDepth G root a R v
    rw [Walk.length_map, hl]
    exact (gluedDepth_component G root a R c vc).symm

noncomputable def glueRooted (ha : ∀ c, G.Adj root (a c).val.val) :
    RootedNormalDepth G root where
  depth := gluedDepth G root a R
  edge_ne := by
    classical
    intro u v huv
    by_cases hu : u = root
    · subst u
      have hv := huv.ne.symm
      have hpos := gluedDepth_pos G root a R hv
      rw [gluedDepth_root]
      omega
    by_cases hv : v = root
    · subst v
      have hpos := gluedDepth_pos G root a R hu
      rw [gluedDepth_root]
      omega
    let c := (deletedGraph G root).connectedComponentMk ⟨v, hv⟩
    let vc : c := ⟨⟨v, hv⟩, rfl⟩
    have huc : (⟨u, hu⟩ : Deleted root) ∈ c.supp :=
      ConnectedComponent.connectedComponentMk_eq_of_adj (G := deletedGraph G root) huv
    let uc : c := ⟨⟨u, hu⟩, huc⟩
    have hne := (R c).edge_ne (u := uc) (v := vc) huv
    rw [gluedDepth_component G root a R c uc, gluedDepth_component G root a R c vc]
    omega
  earlier_injective := by
    classical
    intro v u w huv hwv hul hwl heq
    have hv : v ≠ root := by
      intro h
      subst v
      rw [gluedDepth_root] at hul
      omega
    by_cases hu : u = root
    · subst u
      by_cases hw : w = root
      · exact hw.symm
      · have hpos := gluedDepth_pos G root a R hw
        rw [gluedDepth_root] at heq
        omega
    by_cases hw : w = root
    · subst w
      have hpos := gluedDepth_pos G root a R hu
      rw [gluedDepth_root] at heq
      omega
    let c := (deletedGraph G root).connectedComponentMk ⟨v, hv⟩
    let vc : c := ⟨⟨v, hv⟩, rfl⟩
    have huc : (⟨u, hu⟩ : Deleted root) ∈ c.supp :=
      ConnectedComponent.connectedComponentMk_eq_of_adj (G := deletedGraph G root) huv
    have hwc : (⟨w, hw⟩ : Deleted root) ∈ c.supp :=
      ConnectedComponent.connectedComponentMk_eq_of_adj (G := deletedGraph G root) hwv
    let uc : c := ⟨⟨u, hu⟩, huc⟩
    let wc : c := ⟨⟨w, hw⟩, hwc⟩
    rw [gluedDepth_component G root a R c uc, gluedDepth_component G root a R c vc] at hul
    rw [gluedDepth_component G root a R c wc, gluedDepth_component G root a R c vc] at hwl
    rw [gluedDepth_component G root a R c uc, gluedDepth_component G root a R c wc] at heq
    have hc := (R c).earlier_injective (v := vc) (u := uc) (w := wc) huv hwv
      (by omega) (by omega) (by omega)
    exact congrArg (fun x : c => x.val.val) hc
  back_path := by
    classical
    intro u v huv hlt
    by_cases hu : u = root
    · subst u
      obtain ⟨p, hp, hl⟩ := gluedRootPath G root a R ha v
      exact ⟨p, hp, by simpa [gluedDepth_root] using hl⟩
    have hv : v ≠ root := by
      intro h
      subst v
      rw [gluedDepth_root] at hlt
      omega
    let c := (deletedGraph G root).connectedComponentMk ⟨v, hv⟩
    let vc : c := ⟨⟨v, hv⟩, rfl⟩
    have huc : (⟨u, hu⟩ : Deleted root) ∈ c.supp :=
      ConnectedComponent.connectedComponentMk_eq_of_adj (G := deletedGraph G root) huv
    let uc : c := ⟨⟨u, hu⟩, huc⟩
    rw [gluedDepth_component G root a R c uc, gluedDepth_component G root a R c vc] at hlt
    obtain ⟨p, hp, hl⟩ := (R c).back_path (u := uc) (v := vc) huv (by omega)
    refine ⟨p.map (componentHom G root c), hp.map (componentHom_injective G root c), ?_⟩
    change @Walk.length _ G ((componentHom G root c) uc)
      ((componentHom G root c) vc) (p.map (componentHom G root c)) = _
    rw [Walk.length_map, hl, gluedDepth_component G root a R c uc,
      gluedDepth_component G root a R c vc]
    omega
  root_depth := gluedDepth_root G root a R
  root_path := gluedRootPath G root a R ha

end Glue

universe u

lemma rootedNormalDepth_exists_aux (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (root : V),
      Fintype.card V = n → G.Connected → Nonempty (RootedNormalDepth G root) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G root hcard hG
    choose a ha using component_neighbor G root hG
    have hR : ∀ c : (deletedGraph G root).ConnectedComponent,
        Nonempty (RootedNormalDepth c.toSimpleGraph (a c)) := by
      intro c
      let := Fintype.ofFinite c
      apply ih (Fintype.card c)
      · simpa [Nat.card_eq_fintype_card, hcard] using component_card_lt G root c
      · exact rfl
      · exact c.connected_toSimpleGraph
    let R := fun c => Classical.choice (hR c)
    exact ⟨glueRooted G root a R ha⟩

/-- Every finite connected graph has a normal depth function with any chosen root.
The construction recursively processes the components left after deleting the root. -/
theorem rootedNormalDepth_exists [Finite V] (hG : G.Connected) :
    Nonempty (RootedNormalDepth G root) := by
  classical
  let := Fintype.ofFinite V
  exact rootedNormalDepth_exists_aux (Fintype.card V) G root rfl hG

section Forest

variable (R : (c : G.ConnectedComponent) → NormalDepth c.toSimpleGraph)

def forestDepth (v : V) : ℕ :=
  (R (G.connectedComponentMk v)).depth ⟨v, rfl⟩

lemma forestDepth_component (c : G.ConnectedComponent) (v : c) :
    forestDepth G R v.val = (R c).depth v := by
  rcases v with ⟨v, hv⟩
  change G.connectedComponentMk v = c at hv
  subst c
  rfl

/-- Normal depth functions glue over disjoint connected components. -/
def normalDepthOfComponents : NormalDepth G where
  depth := forestDepth G R
  edge_ne := by
    intro u v huv
    let c := G.connectedComponentMk v
    let vc : c := ⟨v, rfl⟩
    let uc : c := ⟨u, ConnectedComponent.connectedComponentMk_eq_of_adj huv⟩
    rw [forestDepth_component G R c uc, forestDepth_component G R c vc]
    exact (R c).edge_ne (u := uc) (v := vc) huv
  earlier_injective := by
    intro v u w huv hwv hul hwl heq
    let c := G.connectedComponentMk v
    let vc : c := ⟨v, rfl⟩
    let uc : c := ⟨u, ConnectedComponent.connectedComponentMk_eq_of_adj huv⟩
    let wc : c := ⟨w, ConnectedComponent.connectedComponentMk_eq_of_adj hwv⟩
    rw [forestDepth_component G R c uc, forestDepth_component G R c vc] at hul
    rw [forestDepth_component G R c wc, forestDepth_component G R c vc] at hwl
    rw [forestDepth_component G R c uc, forestDepth_component G R c wc] at heq
    exact congrArg Subtype.val ((R c).earlier_injective
      (u := uc) (v := vc) (w := wc) huv hwv hul hwl heq)
  back_path := by
    intro u v huv hlt
    let c := G.connectedComponentMk v
    let vc : c := ⟨v, rfl⟩
    let uc : c := ⟨u, ConnectedComponent.connectedComponentMk_eq_of_adj huv⟩
    rw [forestDepth_component G R c uc, forestDepth_component G R c vc] at hlt
    obtain ⟨p, hp, hl⟩ := (R c).back_path (u := uc) (v := vc) huv hlt
    refine ⟨p.map c.toSimpleGraph_hom, hp.map Subtype.val_injective, ?_⟩
    change @Walk.length _ G (c.toSimpleGraph_hom uc) (c.toSimpleGraph_hom vc)
      (p.map c.toSimpleGraph_hom) = _
    rw [Walk.length_map, hl, forestDepth_component G R c uc, forestDepth_component G R c vc]

end Forest

/-- Every finite graph has a normal DFS depth function with actual tree paths. -/
theorem normalDepth_exists [Finite V] : Nonempty (NormalDepth G) := by
  classical
  have hR : ∀ c : G.ConnectedComponent, Nonempty (NormalDepth c.toSimpleGraph) := by
    intro c
    obtain ⟨R⟩ := rootedNormalDepth_exists c.toSimpleGraph
      ⟨c.out, c.out_eq⟩ c.connected_toSimpleGraph
    exact ⟨R.toNormalDepth⟩
  exact ⟨normalDepthOfComponents G (fun c => Classical.choice (hR c))⟩

end Erdos58
