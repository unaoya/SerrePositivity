module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeRestriction
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.F1.ColimitRestriction
public import SerrePositivity.InfinityCategories.F1.CosliceRestriction
public import SerrePositivity.InfinityCategories.Core.PastingCorner

/-! # 部分長方形から右の span への普遍性の制限

概要：終端角を除いた長方形上の coslice は、右の span 上へ trivial Kan fibration で制限される。
方針：固定部分を持つ収縮による right anodyne 性を、coslice の制限の充填へ適用する。
規約：左四角形の押し出し性を使う比較はこの定理とは別である。
使われ方：S4 の貼り合わせの二つの制限のうち、右側の span への制限。
-/
@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：五頂点図式から右の span への coslice の制限は trivial Kan fibration。
方針：右の span の包含の right anodyne 性を適用する。
規約：図式 p の値域 X の quasicategory 性だけを仮定する。
使われ方：貼り合わせの右側の普遍性の比較。 -/
lemma pastingCornerRestrict_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (p : (pastingCorner : SSet.{u}) ⟶ X) :
    TrivialKanFibration (sliceUnderRestrict p pastingRightSpan.ι) :=
  sliceUnderRestrict_trivialKanFibration p pastingRightSpan.ι pastingRightSpan_rightAnodyne

/-- 概要：五頂点図式の余錐の余極限性は右の span 上への制限で判定できる。
方針：coslice の制限が同値なので、その始対象性を保ち反映する。
規約：余錐の頂点は同じ。値域 X は quasicategory とする。
使われ方：S4 の右四角形と部分長方形の colimit の比較。 -/
lemma pastingCorner_isColimitCone_iff_rightSpan {X : SSet.{u}} [Quasicategory X]
    {p : (pastingCorner : SSet.{u}) ⟶ X} (c : JoinCocone p) :
    IsColimitCone c ↔ IsColimitCone (c.restrict pastingRightSpan.ι) :=
  isColimitCone_iff_restrict_of_rightAnodyne c pastingRightSpan.ι pastingRightSpan_rightAnodyne

end SerrePositivity.InfinityCategories
