module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedCompositionPrisms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaNormalizeHom

/-! 恒等 comma の実標準閉射での正規化前後合成を、同じ実 slice 三角形の全族として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E Y.source

def dgGluingIdentityCommaPreNormalizePrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPrecompositionPrism R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X) f

lemma dgGluingIdentityCommaPreNormalizePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ dgGluingIdentityCommaPreNormalizePrism R E X Y f =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R Q NX Y := by
  rw [dgGluingIdentityCommaPreNormalizePrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPrecompositionPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom_closed]

lemma dgGluingIdentityCommaPreNormalizePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ dgGluingIdentityCommaPreNormalizePrism R E X Y f =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R Q X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPrecompositionPrism_one R Q _ f

lemma dgGluingIdentityCommaPreNormalizePrism_projection :
    dgGluingIdentityCommaPreNormalizePrism R E X Y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((SSet.const (X := K)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex NX) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPrecompositionPrism_projection R Q _ f

def dgGluingIdentityCommaPostNormalizePrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPostcompositionPrism R Q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)
    (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y))

lemma dgGluingIdentityCommaPostNormalizePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ dgGluingIdentityCommaPostNormalizePrism R E X Y f =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom R E X Y) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R Q NX NY := by
  rw [dgGluingIdentityCommaPostNormalizePrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPostcompositionPrism_zero,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeHom_closed R E NX Y]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp (D := Q) (E := Q) (T := Q)
    (x := X) (y := Y) (x' := NX) (y' := Y) (x'' := NX) (y'' := NY)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeHom R E NX Y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom, hc]
  simp only [Category.assoc]

lemma dgGluingIdentityCommaPostNormalizePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ dgGluingIdentityCommaPostNormalizePrism R E X Y f =
      (SSet.const (X := K)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y))) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R Q Y NY :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPostcompositionPrism_one R Q _ _

lemma dgGluingIdentityCommaPostNormalizePrism_projection :
    dgGluingIdentityCommaPostNormalizePrism R E X Y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex NX) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedPostcompositionPrism_projection R Q _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
