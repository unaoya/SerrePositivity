module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison

/-! # Weak equivalences of the actual raw mixed Hom and strict lift actions -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedResolutionInvariance
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev comparison : MixedBiresolutionComparison.functor (C := C) ⟶
    RightResolutionMapping.functor hcof hfib :=
  MixedBiresolutionComparison.rawIso.inv ≫ BiresolutionRawMapping.comparison hcof hfib

lemma comparison_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((comparison hcof hfib).app X) :=
  (weakEquivalences SSet.{v}).comp_mem _ _ ((weakEquivalences SSet.{v}).of_isIso _)
    (BiresolutionRawMapping.comparison_weakEquivalence hcof hfib X)

include hcof hfib in
lemma map_weakEquivalence {X Y : RightResolutionMapping.Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((RightResolutionMapping.projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((MixedBiresolutionComparison.functor (C := C)).map f) := by
  have h := (weakEquivalences SSet.{v}).comp_mem _ _
    (comparison_weakEquivalence hcof hfib X)
    (RightResolutionMapping.map_weakEquivalence hcof hfib f hs ht)
  rw [← (comparison hcof hfib).naturality f] at h
  exact (weakEquivalences SSet.{v}).of_postcomp _ _
    (comparison_weakEquivalence hcof hfib Y) h

include hcof hfib in
lemma lift_map_weakEquivalence {X X' : ResolutionObject C} (k : X ⟶ X')
    {Y Y' : ResolutionObject Cᵒᵖ} (l : Y ⟶ Y')
    (hk : weakEquivalences C k.base) (hl : weakEquivalences Cᵒᵖ l.base) :
    weakEquivalences SSet.{v} (MixedDiagonalHom.map k.diagram l.diagram) := by
  let f : MixedBiresolutionComparison.pair X' Y' ⟶ MixedBiresolutionComparison.pair X Y :=
    ((FramedResolution.lift k).op, (FramedResolution.lift l).op)
  exact map_weakEquivalence hcof hfib f hk hl

include hcof hfib in
lemma strict_action_weakEquivalence {X X' : ResolutionObject C} (k : X ⟶ X')
    {Y Y' : ResolutionObject Cᵒᵖ} (l : Y ⟶ Y')
    (hk : weakEquivalences C k.base) (hl : weakEquivalences Cᵒᵖ l.base)
    (d e : MixedResolutionLiftAction.input X' Y' ⟶
      SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) :
    weakEquivalences SSet.{v}
      (MixedResolutionLiftAction.action X X' k.base Y Y' l.base
        (d ≫ ResolutionLiftSpace.ofLift k) (e ≫ ResolutionLiftSpace.ofLift l) (𝟙 _)) := by
  rw [MixedResolutionKanComparison.action_ofLift, Category.id_comp]
  exact (weakEquivalences SSet.{v}).comp_mem _ _
    (lift_map_weakEquivalence hcof hfib k l hk hl)
    (MixedResolutionComparison.augmentation_weakEquivalence hcof hfib X Y)

end SerrePositivity.HomotopyFunctionComplex.MixedResolutionInvariance
