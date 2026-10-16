module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison

/-! # The strict large ordinary bar inverts weak equivalences in both base variables

Object and arrow lifts are used only to test an already strict base functor.
They are not required to form a functorial section of the presentation projection.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarBaseInvariance
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev ofBase (X : Cᵒᵖ × C) : RightResolutionMapping.Index C :=
  (op (FramedResolution.ofObject X.1.unop), DualResolutionTargets.ofObject C X.2)

def liftBase {X Y : RightResolutionMapping.Index C}
    (f : RightResolutionMapping.projection.obj X ⟶
      RightResolutionMapping.projection.obj Y) : X ⟶ Y :=
  ((FramedResolution.liftBase f.1.unop).op, DualResolutionTargets.liftBase C f.2)

@[simp] lemma projection_liftBase {X Y : RightResolutionMapping.Index C}
    (f : RightResolutionMapping.projection.obj X ⟶
      RightResolutionMapping.projection.obj Y) :
    RightResolutionMapping.projection.map (liftBase f) = f := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hcof hfib hL in
lemma map_isIso {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso (L.map (OrdinaryResolutionBar.functor.map f)) := by
  let g : ofBase X ⟶ ofBase Y := liftBase f
  have hg : weakEquivalences SSet.{v}
      (MixedBiresolutionComparison.functor.map g) :=
    MixedResolutionInvariance.map_weakEquivalence hcof hfib g hs ht
  have : IsIso (((MixedBiresolutionComparison.functor ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L).map g) :=
    OrdinaryBarMappingComparison.small_map_isIso hcof hfib L hL _ hg
  exact (NatIso.isIso_map_iff
    (OrdinaryBarMappingComparison.mixedIso hcof hfib L hL) g).mp inferInstance

include hcof hfib in
lemma localized_map_isIso {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryResolutionBar.functor.map f)) :=
  map_isIso hcof hfib AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) f hs ht

/-- Each value has an explicit small reference, after localization; the base
diagram itself has not been replaced by a small strict simplicial functor. -/
def valueIso (X : Cᵒᵖ × C) :
    L.obj (SSet.uliftFunctor.{max u v, v}.obj
      ((ReplacementMapping.uncurried hcof hfib).obj
        ((RightResolutionMapping.presentationRows.obj (op (SimplexCategory.mk 0))).obj
          (ofBase X)))) ≅ L.obj (OrdinaryResolutionBar.functor.obj X) :=
  (OrdinaryBarMappingComparison.zeroIso hcof hfib L hL).app (ofBase X)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarBaseInvariance
