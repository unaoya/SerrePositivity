module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPullbackComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedCompositeTransport

/-! F2 の矢印側射影を、元の指定構造矢印族の写像空間作用へ値まで戻す。 -/
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
local notation "F" => dgGluingUniverseDerivedNerveLaxComparison R C D M

def dgGluingLaxHomArrowEndpointIso (X Y : DGGluingObject R C D M) :=
  dgGluingPinchedCompositeIso (F)
    (F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M))
    (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
    (dgGluingUniverseDerivedNerveLaxComparison_arrow R C D M)
    (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y))

lemma dgGluingLaxHomPullbackComparison_arrow_transport (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.fst _ _ ≫
      (dgGluingLaxHomArrowEndpointIso R C D M X Y).hom =
    (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) := by
  rw [← Category.assoc, dgGluingLaxHomPullbackComparison_arrow,
    dgGluingLaxHomMappingComparison]
  simpa only [Category.assoc, dgGluingLaxHomArrowEndpointIso] using
    congrArg (fun k => (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫ k)
      (dgGluingPinchedComposite_naturality (F)
        (F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (dgGluingUniverseDerivedCoefficient R C D M))
        (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
        (dgGluingUniverseDerivedNerveLaxComparison_arrow R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)))

end SerrePositivity.InfinityCategories
