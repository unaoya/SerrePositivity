module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstUnitValue

/-!
概要：元の raw 第一辺合成比較から、同じ実端点の元の模型単位比較を回収する。
方針：固定値への像の実両端を揃え、元の上側単位因子を合成する。
規約：元の模型比較を選び直さない。使われ方：長辺分解後の最初辺因子の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 元の raw 第一辺合成比較の値を、元の模型単位比較の始点と上面作用で読む指定同型。 -/
def coherentColimitRawFirstUnitValueComparison :=
  vertexIsoOfEq ((coherentColimitRawFirstUnitComparison B a).postcomp V)
    (coherentColimitRawFirstUnit_source_value_vertex B a)
    (congrArg functorVertex (coherentColimitRawUnitFiberValue_target_map B a))

/-- 同じ実両端に揃えた値は、元の逆下側因子と元の二面比較の合成そのもの。 -/
lemma coherentColimitRawFirstUnitValueComparison_eq_reduced :
    coherentColimitRawFirstUnitValueComparison B a =
      (coherentColimitLowerTransportFactorIso B a).symm ≪≫
        coherentColimitNativeTriangleActionComparison B a :=
  eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitRawFirstUnitComparison_value_heq_reduced B a))

/-- 元の上側単位因子を合成すると、同じ元の第一辺模型単位比較を厳密に回収する。 -/
lemma coherentColimitRawFirstUnitValueComparison_model :
    coherentColimitRawFirstUnitValueComparison B a ≪≫ coherentColimitUpperUnitFactorIso B a =
      coherentColimitIntervalModelUnitComparison B a := by
  rw [coherentColimitRawFirstUnitValueComparison_eq_reduced,
    coherentColimitIntervalModelUnitComparison_eq_reduced, Iso.trans_assoc]

end SerrePositivity.InfinityCategories.F2
