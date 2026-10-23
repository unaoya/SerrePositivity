module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitPointValueToFiberTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawUnitActionValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoPostValueComparison

/-!
概要：値射影前の元の raw fiber 二面比較を、同じ固定 native 中央比較へ照合する。
方針：同じ二面の全空間成分と元の値射影を計算し、既存の指定値同定へ戻す。
規約：二面・単位・頂点等式を保持。使われ方：残る輸送作用の像を元の模型比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 元の raw fiber 比較を同じ固定値へ写すと、元の native 中央比較の指定値に一致する。 -/
lemma coherentColimitRawUnitFiberComparison_valueTo_heq_native :
    HEq ((coherentColimitRawUnitFiberComparison B a).postcomp V)
      (coherentColimitNativeTriangleActionComparison B a) := by
  exact functorIso_postcomp_pair_comparison_heq
    (coherentColimitRawUnitActionComparison B a) P V
    (coherentColimitNativeTriangleActionComparison B a)
    (coherentColimitRawUnitAction_valueTo_heq_native B a)

end SerrePositivity.InfinityCategories.F2
