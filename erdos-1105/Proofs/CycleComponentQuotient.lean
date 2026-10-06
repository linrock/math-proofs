module

public import CycleWeakCount
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-!
assembly of the exact weak-block quotient output from explicit
whole-component cardinality, cross-color constancy and raw triangle inputs. No general-k component or Claim3/Claim4 hypothesis is proved in this module. The component enumeration/fiber and representative-pullback mechanics follow
the checked fixed-k4 partition/quotient sources, with their triangle-specific
mathematical premises replaced by the explicit conditional inputs below.
-/

namespace ErdosProblems.AntiRamseyCycleComponentQuotient

open SimpleGraph Finset
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyTriangle

variable {n k : ℕ} {C : Type*} [DecidableEq C]

/-- Whole components become the exact weak-block witnesses when their sizes
and the original host's cross-component color conditions are supplied.
The graph G is arbitrary and need not be a canonical representative graph. -/
theorem weak_structure_of_component_conditions
    (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hupper : ∀ D : G.ConnectedComponent, D.supp.ncard ≤ k - 1)
    (hcross : ∀ (D E : G.ConnectedComponent) (_hDE : D ≠ E)
      (a d : Fin n) (_ha : a ∈ D.supp) (_hd : d ∈ E.supp) (had : a ≠ d)
      (a' d' : Fin n) (_ha' : a' ∈ D.supp) (_hd' : d' ∈ E.supp)
      (had' : a' ≠ d'), χ.get a d had = χ.get a' d' had')
    (hrawTriangle : ∀ (a d c : Fin n)
      (had : a ≠ d) (hdc : d ≠ c) (hca : c ≠ a)
      (_hAD : G.connectedComponentMk a ≠ G.connectedComponentMk d)
      (_hDC : G.connectedComponentMk d ≠ G.connectedComponentMk c)
      (_hCA : G.connectedComponentMk c ≠ G.connectedComponentMk a),
      ¬ (χ.get a d had ≠ χ.get d c hdc ∧
        χ.get d c hdc ≠ χ.get c a hca ∧
        χ.get c a hca ≠ χ.get a d had)) :
    ∃ (t : ℕ) (b : Fin n → Fin t) (ψ : TopEdgeLabeling (Fin t) C),
      1 ≤ t ∧
      (∀ (a d : Fin n) (had : a ≠ d) (hbd : b a ≠ b d),
        χ.get a d had = ψ.get (b a) (b d) hbd) ∧
      NoRainbowTriangle ψ ∧
      (∀ i : Fin t, 1 ≤ (blockFiber b i).card) ∧
      (∀ i : Fin t, (blockFiber b i).card ≤ k - 1) ∧
      (∑ i : Fin t, (blockFiber b i).card = n) := by
  classical
  let t : ℕ := Fintype.card G.ConnectedComponent
  let e : G.ConnectedComponent ≃ Fin t := Fintype.equivFin G.ConnectedComponent
  let b : Fin n → Fin t := fun v => e (G.connectedComponentMk v)
  let z : Fin n := ⟨0, hn⟩
  have htpos : 0 < t := by
    dsimp [t]
    exact Finset.card_pos.mpr ⟨G.connectedComponentMk z, Finset.mem_univ _⟩
  have ht : 1 ≤ t := by omega
  have hfiber (i : Fin t) : blockFiber b i = (e.symm i).supp.toFinset := by
    ext v
    simpa [blockFiber, b, ConnectedComponent.mem_supp_iff] using
      (e.eq_symm_apply (x := i) (y := G.connectedComponentMk v)).symm
  have hsupper (i : Fin t) : (blockFiber b i).card ≤ k - 1 := by
    calc
      (blockFiber b i).card = (e.symm i).supp.toFinset.card :=
        congrArg Finset.card (hfiber i)
      _ = (e.symm i).supp.ncard :=
        (Set.ncard_eq_toFinset_card' (e.symm i).supp).symm
      _ ≤ k - 1 := hupper (e.symm i)
  have hnonempty : ∀ i : Fin t, ∃ a : Fin n, b a = i := by
    intro i
    obtain ⟨a, ha⟩ := (e.symm i).nonempty_supp
    have hcomp : G.connectedComponentMk a = e.symm i :=
      (ConnectedComponent.mem_supp_iff (e.symm i) a).mp ha
    refine ⟨a, ?_⟩
    change e (G.connectedComponentMk a) = i
    rw [hcomp]
    exact e.apply_symm_apply i
  have hspos (i : Fin t) : 1 ≤ (blockFiber b i).card := by
    obtain ⟨a, ha⟩ := hnonempty i
    have hm : a ∈ blockFiber b i := by simp [blockFiber, ha]
    have hpos : 0 < (blockFiber b i).card := Finset.card_pos.mpr ⟨a, hm⟩
    omega
  choose rep hrep using hnonempty
  have hinj : Function.Injective rep := by
    intro i j heq
    calc
      i = b (rep i) := (hrep i).symm
      _ = b (rep j) := congrArg b heq
      _ = j := hrep j
  let emb : Fin t ↪ Fin n := ⟨rep, hinj⟩
  let ψ : TopEdgeLabeling (Fin t) C := TopEdgeLabeling.pullback χ emb
  have hpull : ∀ (i j : Fin t) (hij : i ≠ j),
      ψ.get i j hij = χ.get (rep i) (rep j) (hinj.ne hij) := by
    intro i j hij
    simp [ψ, emb, TopEdgeLabeling.pullback, EdgeLabeling.get,
      EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk]
  have hcompne (i j : Fin t) (hij : i ≠ j) :
      G.connectedComponentMk (rep i) ≠ G.connectedComponentMk (rep j) := by
    intro hcomp
    apply hij
    calc
      i = b (rep i) := (hrep i).symm
      _ = b (rep j) := congrArg e hcomp
      _ = j := hrep j
  have hcrosslabel : ∀ (a d : Fin n) (had : a ≠ d)
      (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd := by
    intro a d had hbd
    have hDE : G.connectedComponentMk a ≠ G.connectedComponentMk d := by
      intro hcomp
      exact hbd (congrArg e hcomp)
    have hrepA : rep (b a) ∈ (G.connectedComponentMk a).supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact e.injective (hrep (b a))
    have hrepD : rep (b d) ∈ (G.connectedComponentMk d).supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact e.injective (hrep (b d))
    have hrepne : rep (b a) ≠ rep (b d) := hinj.ne hbd
    have hconst := hcross (G.connectedComponentMk a) (G.connectedComponentMk d)
      hDE a d ConnectedComponent.connectedComponentMk_mem
      ConnectedComponent.connectedComponentMk_mem had
      (rep (b a)) (rep (b d)) hrepA hrepD hrepne
    calc
      χ.get a d had = χ.get (rep (b a)) (rep (b d)) hrepne := hconst
      _ = ψ.get (b a) (b d) hbd := (hpull (b a) (b d) hbd).symm
  have htriple : NoRainbowTriangle ψ := by
    intro i j l hij hjl hli
    have hraw := hrawTriangle (rep i) (rep j) (rep l)
      (hinj.ne hij) (hinj.ne hjl) (hinj.ne hli)
      (hcompne i j hij) (hcompne j l hjl) (hcompne l i hli)
    by_contra hrepeat
    apply hraw
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      exact hrepeat (Or.inl (by simpa only [hpull] using heq))
    · intro heq
      exact hrepeat (Or.inr (Or.inl (by simpa only [hpull] using heq)))
    · intro heq
      exact hrepeat (Or.inr (Or.inr (by simpa only [hpull] using heq)))
  have hsum : ∑ i : Fin t, (blockFiber b i).card = n := by
    have h : (Finset.univ : Finset (Fin n)).card =
        ∑ i : Fin t, ((Finset.univ : Finset (Fin n)).filter
          (fun v => b v = i)).card :=
      Finset.card_eq_sum_card_fiberwise (by simp)
    simpa [blockFiber] using h.symm
  exact ⟨t, b, ψ, ht, hcrosslabel, htriple, hspos, hsupper, hsum⟩

end ErdosProblems.AntiRamseyCycleComponentQuotient
