module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFiberwiseContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension

/-! # All-monomorphism lifting from an actual retraction homotopy of a Kan fibration

A two-horn makes the contraction vertical. Relative endpoint extension
then supplies actual lifts of every mono square, without a model structure.
An ordinary localized isomorphism is not assumed to supply the homotopy.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanRetractionRightLifting
variable {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)

include hp hs in
lemma of_vertical (V : SSet.Homotopy (𝟙 E) (p ≫ s))
    (hV : V.h ≫ p = fst E (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) ≫ p) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp p := by
  intro A T i hi
  have : Mono i := hi
  constructor
  intro a b sq
  let c := b ≫ s
  have hc : i ≫ c = a ≫ (p ≫ s) := by
    dsimp only [c]
    rw [← Category.assoc, ← sq.w, Category.assoc]
  let H := LargeParameterSquare.changeEndpoints (HomotopyClasses.preHomotopy a V)
    (Category.comp_id a) hc.symm
  let q := fst T (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) ≫ b
  have hb : c ≫ p = SSet.ι₁ ≫ q := by
    dsimp only [c, q]
    rw [Category.assoc, hs, Category.comp_id, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  have hH : H.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q := by
    dsimp only [H]
    rw [LargeParameterSquare.changeEndpoints_h]
    change (a ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h) ≫ p = _
    rw [Category.assoc, hV, whiskerRight_fst_assoc, sq.w]
    exact (whiskerRight_fst_assoc i _ b).symm
  obtain ⟨g, hg, W, _hW, hWp⟩ :=
    KanFibrationEndpointExtension.exists_from_one p hp i c a H q hb hH
  have hgp : g ≫ p = b := by
    have h : (SSet.ι₀ ≫ W.h) ≫ p = SSet.ι₀ ≫ q := by rw [Category.assoc, hWp]
    rw [W.h₀] at h
    simpa only [q, ← Category.assoc, SSet.ι₀_fst, Category.id_comp] using h
  exact CommSq.HasLift.mk' { l := g, fac_left := hg, fac_right := hgp }

include hp hs in
lemma of_homotopy (H : SSet.Homotopy (𝟙 E) (p ≫ s)) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp p := by
  obtain ⟨V, hV⟩ := KanFiberwiseContraction.exists_homotopy p hp s hs H
  exact of_vertical p hp s hs V hV

include hp hs in
lemma boundary_rlp (H : SSet.Homotopy (𝟙 E) (p ≫ s)) : SSet.modelCategoryQuillen.I.rlp p := by
  rw [← SSet.rlp_monomorphisms]
  exact of_homotopy p hp s hs H

end SerrePositivity.SimplicialModel.KanRetractionRightLifting
