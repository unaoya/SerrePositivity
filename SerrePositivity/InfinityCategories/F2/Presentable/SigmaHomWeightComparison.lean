module
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaLiftedHomRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaHomWeightRightKan

public import SerrePositivity.InfinityCategories.F2.Presentable.YonedaWeightFamilyComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightKanRestrictionIso

/-!
概要：元の P_Σ 延長の全 Hom 族と、全自然変換空間族を同じ両変数で自然同型にする。
方針：元の Yoneda 制限を全係数で比較し、二つの実際の右 Kan 条件から持ち上げる。
規約：元の延長・指定単位・全 C と全標的係数を保持する。
使われ方：元の延長の指定余錐像の普遍性を前層の余極限性へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : SigmaPresheafInfinity C ⟶ D}
  (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
  (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β)

/-- 概要：両全族の元の Yoneda 制限は、元の指定単位により全係数で自然同型。
方針：元の Yoneda 制限を全係数で比較し、二つの実際の右 Kan 条件から持ち上げる。
規約：元の延長・指定単位・全 C と全標的係数を保持する。
使われ方：元の延長の指定余錐像の普遍性を前層の余極限性へ帰着する。 -/
def sigmaHomWeightFamily_liftedRestrictionIso :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C))) ≫
      sigmaHomWeightFamily F₀)
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C))) ≫
      sigmaLiftedHomFamily G) :=
  sigmaHomWeightFamily_restrictionIso F₀ ≪≫ yonedaHomWeightFamily_evaluationIso F₀ ≪≫
    homWeightEvaluationFamily_liftedIso F₀ ≪≫ (sigmaLiftedHomFamily_restrictionIso β hβ).symm

/-- 概要：元の延長の持ち上げた全 Hom 族は、同じ全自然変換空間族と両変数で自然同型。
方針：元の Yoneda 制限を全係数で比較し、二つの実際の右 Kan 条件から持ち上げる。
規約：元の延長・指定単位・全 C と全標的係数を保持する。
使われ方：元の延長の指定余錐像の普遍性を前層の余極限性へ帰着する。 -/
def sigmaHomWeightFamily_liftedIso :
    FunctorIso (sigmaHomWeightFamily F₀) (sigmaLiftedHomFamily G) :=
  rightKanReflRestrictionIso _ (sigmaHomWeightFamily_isRightKanExtension F₀)
    (sigmaLiftedHomFamily_isRightKanExtension β hβ)
    (sigmaHomWeightFamily_liftedRestrictionIso β hβ)

end SerrePositivity.InfinityCategories.HomotopyLimits
