module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomNativeRestrictionIso

/-!
概要：既存の局所自然性は、元の指定結合比較と制限自然性の合成そのもの。
方針：同じ指定合成の始点正規化は、その元の値を保持する。
規約：元の局所自然性・指定因子・局所分類作用を保持する。
使われ方：元の全 Hom 上の局所自然性の三角等式への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の局所自然性は、元の二つの指定同型の合成の値を保持する。 -/
lemma cocartesianLocalHomComparison_nativeRestrictionIso_factors_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (cocartesianLocalHomComparison_nativeRestrictionIso l k p q)
      (cocartesianLocalNativeRestrictionCompositeIso l k p q) := by
  exact F2.functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories
