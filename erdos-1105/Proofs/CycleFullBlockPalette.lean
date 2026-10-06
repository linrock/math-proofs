module

public import CycleImagePalette
public import CycleBlockFullVertices

@[expose] public section

/-!
Exact injection of internal full-block edge tags and earlier-block
crossing tags into the realized raw ordered-block palette.
-/

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle
open ErdosProblems.AntiRamseyCycleBlockCount

abbrev fullSourceEdge (m : ℕ) :=
  (⊤ : SimpleGraph (Fin m)).edgeSet

/-- A source edge of complete full block `b`, mapped to the host. -/
def fullBlockHostEdge (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  (fullBlockCopy m n hm b).toHom.mapEdgeSet e

@[simp] theorem fullBlockHostEdge_val (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    (fullBlockHostEdge m n hm b e).val =
      Sym2.map (fullBlockVertex m n hm b) e.val := by
  change Sym2.map (fullBlockCopy m n hm b) e.val =
    Sym2.map (fullBlockVertex m n hm b) e.val
  rfl

/-- All endpoints of a mapped full-block edge have block index `b`. -/
theorem fullBlockHostEdge_blockSym2 (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    Sym2.map (consecutiveBlockMap m n)
      (fullBlockHostEdge m n hm b e).val =
        Sym2.diag (Fin.castLE (Nat.le_succ _) b) := by
  rw [fullBlockHostEdge_val]
  induction e.val using Sym2.inductionOn with
  | hf i j =>
    simp [Sym2.map_mk, Sym2.diag, fullBlockVertex_block]

/-- An internal edge realizes exactly its own host-edge raw tag. -/
theorem fullBlockHostEdge_raw_color (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    rawOrderedBlockLabeling (consecutiveBlockMap m n)
      (fullBlockHostEdge m n hm b e) =
        Sum.inl (fullBlockHostEdge m n hm b e).val := by
  change orderedBlockColor (consecutiveBlockMap m n)
    (fullBlockHostEdge m n hm b e).val =
      Sum.inl (fullBlockHostEdge m n hm b e).val
  rw [fullBlockHostEdge_val]
  induction e.val using Sym2.inductionOn with
  | hf i j =>
    simp [Sym2.map_mk, orderedBlockColor_mk, fullBlockVertex_block]

/-- Host edges from separate full blocks are distinct; within a block,
the complete-graph Copy map is injective on source edges. -/
theorem fullBlockHostEdge_pair_injective (m n : ℕ) (hm : 0 < m) :
    Function.Injective
      (fun p : Fin (n / m) × fullSourceEdge m =>
        fullBlockHostEdge m n hm p.1 p.2) := by
  intro p r h
  have hblocks :
      Sym2.diag (Fin.castLE (Nat.le_succ _) p.1) =
        Sym2.diag (Fin.castLE (Nat.le_succ _) r.1) := by
    have hh := congrArg
      (fun z : (⊤ : SimpleGraph (Fin n)).edgeSet =>
        Sym2.map (consecutiveBlockMap m n) z.val) h
    simpa only [fullBlockHostEdge_blockSym2] using hh
  have hb : p.1 = r.1 :=
    Fin.castLE_injective (Nat.le_succ _)
      (Sym2.diag_injective hblocks)
  have he : p.2 = r.2 := by
    have h' := h
    change fullBlockHostEdge m n hm p.1 p.2 =
      fullBlockHostEdge m n hm r.1 r.2 at h'
    rw [← hb] at h'
    have hval :
        Sym2.map (fullBlockVertex m n hm p.1) p.2.val =
          Sym2.map (fullBlockVertex m n hm p.1) r.2.val := by
      simpa only [fullBlockHostEdge_val] using congrArg Subtype.val h'
    have hvertex : Function.Injective (fullBlockVertex m n hm p.1) := by
      intro i j hij
      have hv := congrArg Fin.val hij
      simp only [fullBlockVertex_val] at hv
      exact Fin.ext (Nat.add_right_cancel hv)
    exact Subtype.ext ((Sym2.map.injective hvertex) hval)
  exact Prod.ext hb he

def earlyFullBlock (m n : ℕ) (hq : 0 < n / m)
    (b : Fin (n / m - 1)) : Fin (n / m) :=
  ⟨b.val, by omega⟩

def lastFullBlock (m n : ℕ) (hq : 0 < n / m) :
    Fin (n / m) :=
  ⟨n / m - 1, by omega⟩

theorem earlyFullBlock_lt_last (m n : ℕ) (hq : 0 < n / m)
    (b : Fin (n / m - 1)) :
    earlyFullBlock m n hq b < lastFullBlock m n hq := by
  change b.val < n / m - 1
  exact b.isLt

/-- An edge from `b` to the last full block realizes the earlier-block tag. -/
def crossFullHostEdge (m n : ℕ) (hm : 0 < m) (hq : 0 < n / m)
    (b : Fin (n / m - 1)) : (⊤ : SimpleGraph (Fin n)).edgeSet := by
  let z : Fin m := ⟨0, hm⟩
  let x := fullBlockVertex m n hm (earlyFullBlock m n hq b) z
  let y := fullBlockVertex m n hm (lastFullBlock m n hq) z
  have hb : earlyFullBlock m n hq b ≠ lastFullBlock m n hq :=
    ne_of_lt (earlyFullBlock_lt_last m n hq b)
  have hxy : x ≠ y := by
    intro h
    have hp : (earlyFullBlock m n hq b, z) =
        (lastFullBlock m n hq, z) :=
      fullBlockVertex_injective m n hm h
    exact hb (congrArg Prod.fst hp)
  exact ⟨s(x, y), by
    simpa only [SimpleGraph.mem_edgeSet] using ((top_adj x y).mpr hxy)⟩

theorem crossFullHostEdge_raw_color (m n : ℕ) (hm : 0 < m)
    (hq : 0 < n / m) (b : Fin (n / m - 1)) :
    rawOrderedBlockLabeling (consecutiveBlockMap m n)
      (crossFullHostEdge m n hm hq b) =
        Sum.inr (Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq b)) := by
  let z : Fin m := ⟨0, hm⟩
  let a := earlyFullBlock m n hq b
  let c := lastFullBlock m n hq
  have hlt : (Fin.castLE (Nat.le_succ _) a) <
      (Fin.castLE (Nat.le_succ _) c) := by
    simpa only [Fin.lt_def, Fin.val_castLE] using
      earlyFullBlock_lt_last m n hq b
  change orderedBlockColor (consecutiveBlockMap m n)
    s(fullBlockVertex m n hm a z, fullBlockVertex m n hm c z) =
      Sum.inr (Fin.castLE (Nat.le_succ _) a)
  rw [orderedBlockColor_mk, fullBlockVertex_block, fullBlockVertex_block]
  simp [ne_of_lt hlt, min_eq_left (le_of_lt hlt)]

/-- The complete-block raw colors and the earlier-block crossing tags form
an explicit family of colors that really occur on host edges. -/
noncomputable def fullBlockRawWitness (m n : ℕ) (hm : 0 < m)
    (hq : 0 < n / m) :
    Sum (Fin (n / m) × fullSourceEdge m) (Fin (n / m - 1)) →
      rawPalette (consecutiveBlockMap m n)
  | Sum.inl (b, e) =>
      ⟨Sum.inl (fullBlockHostEdge m n hm b e).val, by
        rw [← fullBlockHostEdge_raw_color m n hm b e]
        exact rawPalette_mem _ _⟩
  | Sum.inr b =>
      ⟨Sum.inr
        (Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq b)), by
        rw [← crossFullHostEdge_raw_color m n hm hq b]
        exact rawPalette_mem _ _⟩

/-- Exact full-block image injection. -/
theorem fullBlockRawWitness_injective (m n : ℕ) (hm : 0 < m)
    (hq : 0 < n / m) :
    Function.Injective (fullBlockRawWitness m n hm hq) := by
  intro x y h
  have hv := congrArg Subtype.val h
  cases x with
  | inl p =>
    cases y with
    | inl r =>
      have he : fullBlockHostEdge m n hm p.1 p.2 =
          fullBlockHostEdge m n hm r.1 r.2 :=
        Subtype.ext (Sum.inl.inj hv)
      exact congrArg Sum.inl (fullBlockHostEdge_pair_injective m n hm he)
    | inr r => cases hv
  | inr p =>
    cases y with
    | inl r => cases hv
    | inr r =>
      have hc : Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq p) =
          Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq r) :=
        Sum.inr.inj hv
      have hearly : earlyFullBlock m n hq p = earlyFullBlock m n hq r :=
        Fin.castLE_injective (Nat.le_succ _) hc
      have hv : p.val = r.val := by
        simpa only [earlyFullBlock] using congrArg Fin.val hearly
      have hp : p = r := Fin.ext hv
      exact congrArg Sum.inr hp

end ErdosProblems.AntiRamseyCycleCounted
