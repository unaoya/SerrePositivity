module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.F2PresentableSigmaLiftedHomRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaHomWeightRightKan

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.YonedaWeightFamilyComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RightKanRestrictionIso

/-!
概要：元の P_Σ 延長の全 Hom 族と、全自然変換空間族を同じ両変数で自然同型にする。
方針：元の Yoneda 制限を全係数で比較し、二つの実際の右 Kan 条件から持ち上げる。
規約：元の延長・指定単位・全 C と全標的係数を保持する。
使われ方：元の延長の指定余錐像の普遍性を前層の余極限性へ帰着する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D}
  (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G))
  (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β)

/-- 概要：両全族の元の Yoneda 制限は、元の指定単位により全係数で自然同型。
方針：元の Yoneda 制限を全係数で比較し、二つの実際の右 Kan 条件から持ち上げる。
規約：元の延長・指定単位・全 C と全標的係数を保持する。
使われ方：元の延長の指定余錐像の普遍性を前層の余極限性へ帰着する。 -/
def sigmaHomWeightFamily_liftedRestrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily F₀)
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLiftedHomFamily G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily_restrictionIso F₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily_evaluationIso F₀ ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homWeightEvaluationFamily_liftedIso F₀ ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLiftedHomFamily_restrictionIso β hβ).symm

/-- 概要：元の延長の持ち上げた全 Hom 族は、同じ全自然変換空間族と両変数で自然同型。
方針：元の Yoneda 制限を全係数で比較し、二つの実際の右 Kan 条件から持ち上げる。
規約：元の延長・指定単位・全 C と全標的係数を保持する。
使われ方：元の延長の指定余錐像の普遍性を前層の余極限性へ帰着する。 -/
def sigmaHomWeightFamily_liftedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLiftedHomFamily G) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanReflRestrictionIso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily_isRightKanExtension F₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLiftedHomFamily_isRightKanExtension β hβ)
    (sigmaHomWeightFamily_liftedRestrictionIso β hβ)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
