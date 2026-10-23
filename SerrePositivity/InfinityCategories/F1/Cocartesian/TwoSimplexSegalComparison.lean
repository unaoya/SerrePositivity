module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSourceFactorization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexTargetFactorization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexGlobalPullbackComparison

/-!
概要：元の分類 Hom 作用の二辺制限は、同じ source 制限と既存の pullback 同値に整合する。
方針：同じ pullback 上で構成済みの比較同型の両端を、証明済みの二因数分解へ移す。
規約：元の全相対 Hom と元の分類 Hom 作用を保持する。
使われ方：二単体上の source・target Segal 同値から同じ Hom 作用の同値性を結論する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom に対する source 制限・厳密比較と、同じ分類作用・target 制限の比較同型。 -/
def cocartesianTwoSimplexSegalComparisonIso
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (cocartesianTwoSimplexSourceRestrictionMap k p q ≫
        cocartesianTwoSimplexStrictPullbackMap k p q)
      (cocartesianStraighteningHomInterval p q ≫
        cocartesianTwoSimplexTargetRestrictionMap k p q) :=
  F2.functorIsoOfEq (cocartesianTwoSimplexGlobalPullbackComparisonIso k p q)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_factor k p q).symm
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_factor k p q).symm

end SerrePositivity.InfinityCategories
