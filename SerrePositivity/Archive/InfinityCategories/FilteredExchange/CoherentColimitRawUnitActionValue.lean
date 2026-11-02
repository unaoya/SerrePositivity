module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitPointValueToFiberTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareConstantFiberMap

/-!
概要：元の raw 全空間二面比較の値射影を、同じ指定 native 中央比較へ戻す。
方針：同じ二面の元の相対成分の値射影を一つの合成射として照合する。
規約：元の指定値と頂点等式を保持。使われ方：raw fiber 比較の二段の射影の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)

/-- 元の raw 全空間比較の同じ合成値射への像は、元の native 中央比較の指定値。 -/
lemma coherentColimitRawUnitAction_valueTo_heq_native :
    HEq ((coherentColimitRawUnitActionComparison B a).postcomp
      (coherentColimitRawConstantFiberProjection B G ≫
        pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)))
      (coherentColimitNativeTriangleActionComparison B a) := by
  have hn := coherentColimitUnitValueActionTo_total_heq_native B a
  unfold coherentColimitUnitValueActionTo at hn
  rw [constantTargetValueProjectionTo_eq_fiberValueTo] at hn
  exact (functorSquareComparison_value_fiberMap
    (coherentColimitUnitUpperTriangle B a) (coherentColimitUnitLowerTriangle B a)
    (pointedFiberValueTo (coherentDiagramTotalCocone_vertex G))).symm.trans hn

end SerrePositivity.InfinityCategories.F2
