module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedAugmentationArrowDiagram
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison

/-! F2 の矢印側の実 Hom 比較を、元の augmentation 図式間の区間 Hom に移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomArrowIntervalComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
    intervalMappingSpace
      (functorVertex (dgGluingDerivedAugmentationArrowDiagram R C D M X))
      (functorVertex (dgGluingDerivedAugmentationArrowDiagram R C D M Y)) :=
  dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.fst _ _ ≫
    (dgGluingLaxHomArrowEndpointIso R C D M X Y).hom ≫
    (pinchedEndpointIso (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M X)
      (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M Y)).hom ≫
    pinchedHomToIntervalMappingSpace _ _

lemma dgGluingLaxHomArrowIntervalComparison_action (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomArrowIntervalComparison R C D M X Y =
    (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) ≫
      (pinchedEndpointIso (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M X)
        (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M Y)).hom ≫
      pinchedHomToIntervalMappingSpace _ _ := by
  simpa only [dgGluingLaxHomArrowIntervalComparison, Category.assoc] using
    congrArg (fun k => k ≫
      (pinchedEndpointIso (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M X)
        (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M Y)).hom ≫
      pinchedHomToIntervalMappingSpace _ _)
      (dgGluingLaxHomPullbackComparison_arrow_transport R C D M X Y)

end SerrePositivity.InfinityCategories
