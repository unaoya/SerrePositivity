module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalHomComparison

/-!
概要：既存の指定局所制限自然性は、元の二因子の指定合成そのものである。
方針：同じ指定合成の端点正規化は、その元の値を保持する。
規約：元の制限自然性・指定因子・局所分類作用を保持する。
使われ方：元の全 Hom 上の局所自然性の三角等式への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の局所制限自然性は、元の二つの指定因子の合成の値を保持する。 -/
lemma cocartesianIteratedLocalHomComparison_restrictionIso_factors_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (cocartesianIteratedLocalHomComparison_restrictionIso l k p q)
      (cocartesianIteratedLocalRestrictionCompositeIso l k p q) := by
  exact F2.functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories
