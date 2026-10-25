module

public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaEvaluationLimits
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseLimits

/-!
概要：元の Yoneda 全射は、元の任意の小さい全極限錐を前層内の極限へ送る。
方針：同じ各評価の極限保存を、前層の点ごとの極限判定へ渡す。
規約：有限性・離散性・モデル構造は仮定しない。既存の深層モジュールは変更しない。
使われ方：Ind の有限極限を、同じ C 図式の全錐から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の Yoneda 全射は任意の小さい極限の同じ native な全錐を保存する。 -/
lemma yonedaInfinityMap_isLimit {K C : SSet.{u}} [Quasicategory C]
    {D : K ⟶ C} (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (yonedaInfinityMap C) (JoinCone.ulift.{u, u + 1} c)) := by
  apply presheafInfinity_isLimit_of_evaluation
    ((SSet.uliftFunctor.{u + 1, u}).map D ≫ yonedaInfinityMap C)
  intro x
  apply (isLimitCone_iff_of_diagram_eq
    (d := mapJoinCone (yonedaInfinityMap C ≫ presheafInfinityEvaluation x)
      (JoinCone.ulift.{u, u + 1} c)) (by simp only [Category.assoc])
    (by simp only [mapJoinCone, Category.assoc])).mpr
  exact yonedaInfinityMap_evaluation_isLimit c hc x

end SerrePositivity.InfinityCategories
