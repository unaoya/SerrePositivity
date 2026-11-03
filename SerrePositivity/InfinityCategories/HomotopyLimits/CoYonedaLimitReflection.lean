module
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSmallLimits
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafLimitDetection
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits

/-!
概要：元の全 co-Yoneda 族は、同じ全錐の極限性を反映する。
方針：全係数の小極限存在で点ごとの極限性へ戻し、表現可能前層による判定を使う。
規約：元の指定全錐と全評価を保持する。
使われ方：P_Σ 左 Kan 延長の全 Hom 比較から元の余極限性を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：全 co-Yoneda 族の像が極限なら元の全錐も極限である。
方針：全係数の点ごとの評価を、元の表現可能前層の全錐へ同定する。
規約：標的は quasicategory、錐の形状は任意。
使われ方：同じ全 Hom 族で判定した左 Kan 延長の余錐像の回収。 -/
lemma coyonedaInfinityMap_reflects_isLimit {K C : SSet.{u}} [Quasicategory C]
    {p : K ⟶ C.op} (c : JoinCone p)
    (hc : IsLimitCone (mapJoinCone (coyonedaInfinityMap C) (JoinCone.ulift.{u, u + 1} c))) :
    IsLimitCone c := by
  have hp : HasPointwiseLimits ((SSet.uliftFunctor.{u + 1, u}).map p ≫
      coyonedaInfinityMap C) := by
    intro y
    exact hasLimit_coherentSpaceDiagram _
  have hpoint := isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits hp _ hc
  apply (isLimitCone_iff_representablePresheafInfinity c).mpr
  intro y
  have hy := hpoint (ULift.up y)
  change IsLimitCone (mapJoinCone (coyonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up y))
    (JoinCone.ulift.{u, u + 1} c)) at hy
  rwa [coyonedaInfinityMap_evaluation] at hy

end SerrePositivity.InfinityCategories.HomotopyLimits
