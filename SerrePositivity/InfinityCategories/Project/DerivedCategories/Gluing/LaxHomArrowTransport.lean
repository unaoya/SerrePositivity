module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomPullbackComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedCompositeTransport

/-! F2 の矢印側射影を、元の指定構造矢印族の写像空間作用へ値まで戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M

def dgGluingLaxHomArrowEndpointIso (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositeIso (F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_arrow R C D M)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))

lemma dgGluingLaxHomPullbackComparison_arrow_transport (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.fst _ _ ≫
      (dgGluingLaxHomArrowEndpointIso R C D M X Y).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison_arrow,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomMappingComparison]
  simpa only [Category.assoc, dgGluingLaxHomArrowEndpointIso] using
    congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomMappingIso R C D M X Y).inv ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedComposite_naturality (F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_arrow R C D M)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
