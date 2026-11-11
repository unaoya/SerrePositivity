module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizationRawFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeDerivedNormalizationCubes
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeIdentityAugmentationPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniversePinchedIntervalEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseSquareComposition

/-! native cube の元 augmentation 面を、正本の同じ全 Hom 区間族・実導来矢印族へ厳密に照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C))
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y

def dgGluingNativeHomIntervalEvaluation :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))

def dgGluingNativeAugmentationIntervalSquare :=
  (Δ[1] ◁ dgGluingNativeHomIntervalEvaluation R C D M X Y) ≫
    (β_ (Δ[1] : SSet.{max (u + 1) v w})
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationPrism R C D M

lemma dgGluingNativePreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeCube R C D M X Y =
      dgGluingNativeAugmentationIntervalSquare R C D M X Y := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex IX) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex IY))
  have hf : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1 p =
    dgGluingNativeHomIntervalEvaluation R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor R C D M) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorPinchedInterval
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor R C D M) X Y
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeCube, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationCube_inner,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawCube_original_face]
  change (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
      ((Δ[1] ◁ p) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleIdentityAugmentationPrism R C) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily_comp, ← Category.assoc, ← whiskerLeft_comp,
    hf, whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityAugmentationPrism]
  rfl

lemma dgGluingNativeDerivedPreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y =
      (Δ[1] ◁ dgGluingNativeHomIntervalEvaluation R C D M X Y) ≫
        (β_ (Δ[1] : SSet.{max (u + 1) v w})
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))).hom ≫
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationHomotopy R C D M).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube, ← Category.assoc,
    dgGluingNativePreNormalizeCube_original_face, dgGluingNativeAugmentationIntervalSquare]
  simp only [Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
