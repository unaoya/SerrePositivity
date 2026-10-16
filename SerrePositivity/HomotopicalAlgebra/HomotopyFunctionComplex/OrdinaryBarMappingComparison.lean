module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance

/-! # Natural comparison of the ordinary bar with the small mapping diagrams

The whole diagrams compare after any functor inverting anodyne extensions.
The base bar remains large. Only the original small simplicial model is used.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hcof hfib hL in
lemma small_map_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : weakEquivalences SSet.{v} f) :
    IsIso (L.map (SSet.uliftFunctor.{max u v, v}.map f)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _
    (UniverseLift.anodyneQ_map_isIso_of_weakEquivalence hcof hfib f hf)

include hcof hfib hL in
lemma right_isIso : IsIso (Functor.whiskerRight
    (OrdinaryResolutionBar.right (C := C)) L) := by
  have (R : RightResolutionMapping.Index C) :
      IsIso ((Functor.whiskerRight (OrdinaryResolutionBar.right (C := C)) L).app R) :=
    AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _
      (OrdinaryBarEvaluationEquivalence.right_isIso R
        (OrdinaryBarCenters.leftSystem R hcof) (OrdinaryBarCenters.rightSystem R hcof)
        hcof hfib)
  exact NatIso.isIso_of_isIso_app _

/-- The natural span is used as a span, without choosing evaluations on the base. -/
def mixedIso :
    (MixedBiresolutionComparison.functor (C := C) ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  have := right_isIso (C := C) hcof hfib L hL
  exact (BarConstruction.spanLeftComparisonIso (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor L hL).symm ≪≫
      asIso (Functor.whiskerRight OrdinaryResolutionBar.right L)

def resolutionIso :
    (RightResolutionMapping.functor (C := C) hcof hfib ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  let η := Functor.whiskerRight
    (Functor.whiskerRight (MixedResolutionInvariance.comparison (C := C) hcof hfib)
      SSet.uliftFunctor.{max u v, v}) L
  have (R : RightResolutionMapping.Index C) : IsIso (η.app R) :=
    small_map_isIso hcof hfib L hL _
      (MixedResolutionInvariance.comparison_weakEquivalence hcof hfib R)
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact (asIso η).symm ≪≫ mixedIso hcof hfib L hL

/-- Degree zero is the existing replacement mapping diagram pulled back along
the actual target presentation functor. -/
def zeroIso :
    (RightResolutionMapping.zero (C := C) hcof hfib ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  let η := Functor.whiskerRight
    (Functor.whiskerRight (RightResolutionMapping.comparison (C := C) hcof hfib)
      SSet.uliftFunctor.{max u v, v}) L
  have (R : RightResolutionMapping.Index C) : IsIso (η.app R) :=
    small_map_isIso hcof hfib L hL _
      (RightResolutionMapping.comparison_weakEquivalence hcof hfib R)
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact asIso η ≪≫ resolutionIso hcof hfib L hL

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison
