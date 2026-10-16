module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement

/-! # A natural comparison with the original replacement mapping diagram

The existing refinement category records actual weak target comparisons.
Every original presentation occurs. No strict section over the base is used.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReplacementComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The comparison of the two actual base diagrams retains the target base arrow. -/
def baseComparison :
    RightResolutionRefinement.resolved C ⋙ RightResolutionMapping.projection ⟶
    RightResolutionRefinement.original C ⋙ ReplacementMapping.projection :=
  Functor.whiskerRight
    (NatTrans.prod (𝟙 _) (RightResolutionRefinement.targetComparison C))
    ReplacementMapping.projection

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hcof hfib hL in
lemma baseComparison_isIso : IsIso (Functor.whiskerRight
    (Functor.whiskerRight (baseComparison (C := C)) OrdinaryResolutionBar.functor) L) := by
  have (X : RightResolutionRefinement.Index C) :
      IsIso ((Functor.whiskerRight
        (Functor.whiskerRight (baseComparison (C := C)) OrdinaryResolutionBar.functor) L).app
          X) :=
    OrdinaryBarBaseInvariance.map_isIso hcof hfib L hL _
      ((weakEquivalences C).id_mem _) X.2.property
  exact NatIso.isIso_of_isIso_app _

/-- Both comparisons are natural on the full refinement index. -/
def refinementIso :
    ((RightResolutionRefinement.original C ⋙ ReplacementMapping.uncurried hcof hfib) ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    ((RightResolutionRefinement.original C ⋙ ReplacementMapping.projection) ⋙
      OrdinaryResolutionBar.functor) ⋙ L := by
  let η := Functor.whiskerRight
    (Functor.whiskerRight (RightResolutionRefinement.left C hcof hfib)
      SSet.uliftFunctor.{max u v, v}) L
  have (X : RightResolutionRefinement.Index C) : IsIso (η.app X) :=
    OrdinaryBarMappingComparison.small_map_isIso hcof hfib L hL _
      (RightResolutionRefinement.left_weakEquivalence C hcof hfib X)
  have : IsIso η := NatIso.isIso_of_isIso_app _
  have := baseComparison_isIso (C := C) hcof hfib L hL
  exact (asIso η).symm ≪≫
    Functor.isoWhiskerLeft (RightResolutionRefinement.resolved C)
      (OrdinaryBarMappingComparison.zeroIso hcof hfib L hL) ≪≫
    asIso (Functor.whiskerRight
      (Functor.whiskerRight (baseComparison (C := C)) OrdinaryResolutionBar.functor) L)

/-- Every original presentation is covered, with its original base and value. -/
def presentationIso (X : ReplacementMapping.Index C) :
    L.obj (SSet.uliftFunctor.{max u v, v}.obj
      ((ReplacementMapping.uncurried hcof hfib).obj X)) ≅
    L.obj (OrdinaryResolutionBar.functor.obj (ReplacementMapping.projection.obj X)) :=
  (refinementIso hcof hfib L hL).app (RightResolutionRefinement.ofOriginal C X)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReplacementComparison
