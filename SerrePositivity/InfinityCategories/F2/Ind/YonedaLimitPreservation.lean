module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaConeFamily
public import SerrePositivity.InfinityCategories.F2.Ind.FullConeLift
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality

/-!
概要：元の小さい極限全錐を、Ind Yoneda がそのまま保存する。
方針：前層 Yoneda の極限保存と、元の全部分包含の反映を合成する。
規約：形状の有限性・交換入力・元の圏の全極限存在を要求しない。
使われ方：I-2 c の各段の実引き戻し四角形の保存。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の任意の小さい指定極限全錐を、Ind Yoneda は保存する。 -/
lemma indYoneda_isLimit (κ : Cardinal.{u}) {K C : SSet.{u}}
    [Quasicategory C] {D : K ⟶ C} (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (indYoneda κ C) (JoinCone.ulift.{u, u + 1} c)) := by
  apply ind_isLimit_of_inclusion κ
  apply (F2.isLimitCone_iff_of_cone_val_eq _ _ ?_).mpr (yonedaInfinityMap_isLimit c hc)
  change ((JoinCone.ulift.{u, u + 1} c).val ≫ indYoneda κ C) ≫
    indInclusionPresheaf κ C = (JoinCone.ulift.{u, u + 1} c).val ≫ yonedaInfinityMap C
  rw [Category.assoc, indYoneda_inclusion]

end SerrePositivity.InfinityCategories.F2.Ind
