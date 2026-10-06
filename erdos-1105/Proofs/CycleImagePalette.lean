module

public import CycleBlockBridge
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
An arbitrary small-fiber ordered-block coloring uses a finite set of raw
tags. Relabel exactly that image by `Fin M` to obtain a surjective
anti-Ramsey witness, where `M` is the image cardinality. The numerical
formula for conventional blocks is a separate counting problem.
-/

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle

/-- The finite set of raw colors actually used on complete-graph edges. -/
noncomputable def rawPalette {n t : ℕ} (π : Fin n → Fin t) :
    Finset (Sum (Sym2 (Fin n)) (Fin t)) := by
  classical
  exact Finset.univ.image (rawOrderedBlockLabeling π)

/-- Every complete-graph edge has a color in the realized raw palette. -/
theorem rawPalette_mem {n t : ℕ} (π : Fin n → Fin t)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    rawOrderedBlockLabeling π e ∈ rawPalette π := by
  classical
  unfold rawPalette
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

/-- Relabel each realized raw color bijectively to a consecutive palette. -/
noncomputable def rawImageColor {n t : ℕ} (π : Fin n → Fin t) :
    TopEdgeLabeling (Fin n) (Fin (rawPalette π).card) := by
  classical
  exact fun e => (rawPalette π).equivFin
    ⟨rawOrderedBlockLabeling π e, rawPalette_mem π e⟩

/-- Two equal raw host-edge colors remain equal after image relabeling. -/
theorem rawImageColor_eq_of_raw_eq {n t : ℕ} (π : Fin n → Fin t)
    (e₁ e₂ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (h : rawOrderedBlockLabeling π e₁ = rawOrderedBlockLabeling π e₂) :
    rawImageColor π e₁ = rawImageColor π e₂ := by
  classical
  have hsub :
      (⟨rawOrderedBlockLabeling π e₁, rawPalette_mem π e₁⟩ : rawPalette π) =
      (⟨rawOrderedBlockLabeling π e₂, rawPalette_mem π e₂⟩ : rawPalette π) :=
    Subtype.ext h
  exact congrArg (rawPalette π).equivFin hsub

/-- By construction, every consecutive palette color is used. -/
theorem rawImageColor_surjective {n t : ℕ} (π : Fin n → Fin t) :
    Function.Surjective (rawImageColor π) := by
  classical
  intro j
  let c : rawPalette π := (rawPalette π).equivFin.symm j
  have hc : c.val ∈ rawPalette π := c.property
  change c.val ∈ Finset.univ.image (rawOrderedBlockLabeling π) at hc
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hc
  have hsub :
      (⟨rawOrderedBlockLabeling π e, rawPalette_mem π e⟩ : rawPalette π) = c :=
    Subtype.ext he
  refine ⟨e, ?_⟩
  simp only [rawImageColor]
  rw [hsub]
  exact (rawPalette π).equivFin.apply_symm_apply j

/-- A small-fiber block coloring remains nonrainbow after its realized image
is relabeled to `Fin M`. -/
theorem rawImageColor_noRainbow_copy
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k) :
    ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom (rawImageColor π) := by
  intro f hf
  have hraw := rawOrderedBlockLabeling_noRainbow_copy hk hn π hsmall f
  apply hraw
  intro e₁ e₂ hcolor
  apply hf
  exact rawImageColor_eq_of_raw_eq π
    (f.toHom.mapEdgeSet e₁) (f.toHom.mapEdgeSet e₂) hcolor

/-- The number of realized raw colors is a formal lower bound for any
small-fiber ordered block map. -/
theorem rawPalette_card_le_antiRamseyNum
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k) :
    (rawPalette π).card ≤ antiRamseyNum (cycleGraph k) n := by
  let A : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}
  have hbound : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  have hmem : (rawPalette π).card ∈ A :=
    ⟨rawImageColor π, rawImageColor_surjective π,
      rawImageColor_noRainbow_copy hk hn π hsmall⟩
  change (rawPalette π).card ≤ sSup A
  exact le_csSup hbound hmem

end ErdosProblems.AntiRamseyCycleCounted
