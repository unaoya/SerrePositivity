module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProjectivePointRingPresentation

/-!
概要：射影的一点加群の同じ係数複体の導来評価を既存の一点模型へ比較する。
方針：C3の全関手復元と既存の射影的複体の評価比較を合成する。
規約：元の射・高次単体を持つ全関手同型。
使われ方：3b-3 R6 U39の係数移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

/-- U39の係数移送：元の一点加群の係数評価と指定一点模型の全族比較。 -/
def projectivePointCoefficientDerivedIso :
    FunctorIso (nerveMap (projectivePointCoefficientComplex A) ≫ complexDerivedEvaluation A)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveDGModules A PUnit.{1}) ≫
        (projectivePointEquivalence A).hom) := by
  have e := (complexDerivedEvaluation_projectiveRingIso A).precomp
    (nerveMap (projectivePointRingPresentation A))
  have hl := congrArg nerveMap (projectivePointRingPresentation_underlying A)
  change nerveMap (projectivePointRingPresentation A) ≫
      nerveMap (projectiveRingUnderlyingComplex A) =
        nerveMap (projectivePointCoefficientComplex A) at hl
  have hr := congrArg nerveMap (projectivePointRingPresentation_constant A)
  change nerveMap (projectivePointRingPresentation A) ≫
      nerveMap (projectiveRingComplexConstant A).onClosed =
        𝟙 (nerve (ClosedCategory A (ProjectiveDGModules A PUnit.{1}))) at hr
  have hr' : nerveMap (projectivePointRingPresentation A) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (projectiveRingComplexConstant A) ≫ (projectivePointEquivalence A).hom =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveDGModules A PUnit.{1}) ≫
        (projectivePointEquivalence A).hom := by
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A))
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (projectiveRingComplexConstant A)) _, closedNerveInclusion_dgFunctor,
      Category.assoc (nerveMap (projectiveRingComplexConstant A).onClosed),
      ← Category.assoc _ (nerveMap (projectiveRingComplexConstant A).onClosed) _, hr,
      Category.id_comp]
  change FunctorIso
    (nerveMap (projectivePointRingPresentation A) ≫
      nerveMap (projectiveRingUnderlyingComplex A) ≫ complexDerivedEvaluation A)
    (nerveMap (projectivePointRingPresentation A) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (projectiveRingComplexConstant A) ≫ (projectivePointEquivalence A).hom) at e
  rw [← Category.assoc _ (nerveMap (projectiveRingUnderlyingComplex A)) _, hl, hr'] at e
  exact e


end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
