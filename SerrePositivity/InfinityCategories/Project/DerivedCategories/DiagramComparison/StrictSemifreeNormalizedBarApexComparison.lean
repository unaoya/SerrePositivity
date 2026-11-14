module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProjectivePointCoefficientDerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeProjectiveApex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeComputedApexComparison

/-!
概要：元の正規化barの係数複体と、同じ計算済み全余錐族のapexを比較する。
方針：射影的一点模型の係数評価比較、C2のapex同定、同じ全族の輸送を合成する。
規約：対象ごとのapexや同型を選び直さない。
使われ方：3b-3 R6 U39・U41の最終受け渡し。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet CartesianMonoidalCategory MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U39の係数移送：元の正規化射影的加群の全係数関手。 -/
lemma strictSemifreeNormalizedProjectiveModule_coefficients :
    strictSemifreeNormalizedProjectiveModule A ⋙ projectivePointCoefficientComplex A =
      strictSemifreeNormalizedBarComplex A := by
  change (strictSemifreeNormalizedProjectiveModule A ⋙
    (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleProjectiveProperty A PUnit.{1})).onClosed) ⋙
        moduleEvaluation A PUnit.{1} PUnit.unit = _
  rw [strictSemifreeNormalizedProjectiveModule_underlying]
  rfl

/-- U39の分割：同じ未輸送の全余錐族のapexを同じ正規化barで読む。 -/
lemma strictSemifreeRawDAApex_eq :
    let P := nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)
    let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
    lift (𝟙 P) (SSet.stdSimplex.isTerminalObj₀.from P) ≫
      (P ◁ joinInr I (Δ[0] : SSet.{u + 1})) ≫
        strictSemifreeReindexedRawDAJoinFamily A =
      nerveMap (strictSemifreeNormalizedProjectiveModule A) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveDGModules A PUnit.{1}) ≫
          (projectivePointEquivalence A).hom := by
  have h := congrArg (fun f => f ≫ (projectivePointEquivalence A).hom)
    (strictSemifreeProjectiveApex A)
  simpa only [strictSemifreeReindexedRawDAJoinFamily, strictSemifreeRawDAJoinFamily,
    Category.assoc] using! h

/-- U39：同じ正規化barの全複体評価と、同じ計算済みapexの全関手同型。 -/
def strictSemifreeNormalizedBarApexIso :
    FunctorIso (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
      (strictSemifreeComputedApexFamily A) := by
  have e := (projectivePointCoefficientDerivedIso A).precomp
    (nerveMap (strictSemifreeNormalizedProjectiveModule A))
  have hc := congrArg nerveMap (strictSemifreeNormalizedProjectiveModule_coefficients A)
  change nerveMap (strictSemifreeNormalizedProjectiveModule A) ≫
      nerveMap (projectivePointCoefficientComplex A) =
        nerveMap (strictSemifreeNormalizedBarComplex A) at hc
  have ee : FunctorIso
      (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
      (nerveMap (strictSemifreeNormalizedProjectiveModule A) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveDGModules A PUnit.{1}) ≫
          (projectivePointEquivalence A).hom) := by
    simpa only [← Category.assoc, hc] using! e
  let a := lift (𝟙 (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)))
    (SSet.stdSimplex.isTerminalObj₀.from _) ≫
      (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
        joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0])
  have et := (strictSemifreeComputedDAJoinFamily_transportIso A).precomp a
  change FunctorIso (a ≫ strictSemifreeReindexedRawDAJoinFamily A)
    (a ≫ strictSemifreeComputedDAJoinFamily A) at et
  have er := strictSemifreeRawDAApex_eq A
  change a ≫ strictSemifreeReindexedRawDAJoinFamily A = _ at er
  rw [er] at et
  simpa only [a, strictSemifreeComputedApexFamily, Category.assoc] using! ee ≪≫ et

/-- U41：元のstrict実現と、同じ指定普遍余錐族のapexの全関手比較。 -/
def strictSemifreeRealizationNativeApexIso :
    FunctorIso (strictSemifreeRealizationFamily A)
      (strictSemifreeNativeApexFamily A SimplexCategoryᵒᵖ) :=
  (strictSemifreeNormalizedBarRealizationIso A).symm ≪≫
    strictSemifreeNormalizedBarApexIso A ≪≫ strictSemifreeComputedNativeApexIso A

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
