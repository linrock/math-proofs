module

public import MonochromaticPairs546
public import RamseyBasics546


@[expose] public section

/-!
# Lifting monochromatic pairs from induced reservoirs

The subtype inclusion preserves non-induced copies, both monochromatic colors,
and finite cardinalities. This module supplies the ambient graph interfaces for
a density argument performed inside an induced reservoir.
-/

namespace Erdos546

open SimpleGraph

/-- Forget the membership proofs in a finite set of subtype vertices. -/
def ambientFinset {W : Type*} (S : Set W) (X : Finset S) : Finset W :=
  X.map (Function.Embedding.subtype (fun w => w ∈ S))

theorem ambientFinset_card {W : Type*} (S : Set W) (X : Finset S) :
    (ambientFinset S X).card = X.card := by
  simp [ambientFinset]

theorem ambientFinset_subset {W : Type*} (S : Set W) (X : Finset S) :
    (ambientFinset S X : Set W) ⊆ S := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
  exact v.property

theorem ambientFinset_subset_coe {W : Type*} (S : Finset W) (X : Finset (S : Set W)) :
    ambientFinset (S : Set W) X ⊆ S :=
  ambientFinset_subset (S : Set W) X

theorem ambientFinset_mono {W : Type*} (S : Set W) {X Y : Finset S} (hXY : X ⊆ Y) :
    ambientFinset S X ⊆ ambientFinset S Y :=
  Finset.map_subset_map.mpr hXY

/-- Injective adjacency-preserving maps carry monochromatic pairs to their images. -/
theorem monoPair_map_of_copy {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : G.Copy H) (X Y : Finset V)
    (hp : MonoPair G X Y) : MonoPair H (X.map c.toEmbedding) (Y.map c.toEmbedding) := by
  rcases hp with ⟨hd, hc, hcross⟩
  refine ⟨(Finset.disjoint_map c.toEmbedding).mpr hd, ?_, ?_⟩
  · intro x hx y hy hne
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    exact c.toHom.map_adj (hc hv hw (fun he => hne (congrArg c he)))
  · intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    exact c.toHom.map_adj (hcross v hv w hw)

theorem monoPair_induce_lift {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (S : Set W) (X Y : Finset S)
    (hp : MonoPair (H.induce S) X Y) :
    MonoPair H (ambientFinset S X) (ambientFinset S Y) := by
  classical
  exact monoPair_map_of_copy (H.induce S) H
    (SimpleGraph.Embedding.induce (G := H) S).toCopy X Y hp

/-- Complementation commutes with restriction through the injective subtype inclusion. -/
theorem induce_compl_eq {W : Type*} (H : SimpleGraph W) (S : Set W) :
    (Hᶜ).induce S = (H.induce S)ᶜ := by
  change SimpleGraph.comap (fun w : S => (w : W)) Hᶜ =
    (SimpleGraph.comap (fun w : S => (w : W)) H)ᶜ
  exact comap_compl_of_injective _ Subtype.val_injective H

theorem monoPair_induce_compl_lift {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (S : Set W) (X Y : Finset S)
    (hp : MonoPair (H.induce S)ᶜ X Y) :
    MonoPair Hᶜ (ambientFinset S X) (ambientFinset S Y) := by
  apply monoPair_induce_lift Hᶜ S X Y
  rw [induce_compl_eq]
  exact hp

/-- An induced subgraph of a graph without a copy of `G` still has no such copy. -/
theorem free_induce {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (S : Set W) (hfree : G.Free H) : G.Free (H.induce S) := by
  intro hc
  exact hfree (hc.trans ⟨(SimpleGraph.Embedding.induce (G := H) S).toCopy⟩)

theorem free_induce_compl {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (S : Set W) (hfree : G.Free Hᶜ) : G.Free (H.induce S)ᶜ := by
  rw [← induce_compl_eq]
  exact free_induce G Hᶜ S hfree

#print axioms ambientFinset_card
#print axioms ambientFinset_subset
#print axioms ambientFinset_subset_coe
#print axioms ambientFinset_mono
#print axioms monoPair_map_of_copy
#print axioms monoPair_induce_lift
#print axioms induce_compl_eq
#print axioms monoPair_induce_compl_lift
#print axioms free_induce
#print axioms free_induce_compl

end Erdos546
