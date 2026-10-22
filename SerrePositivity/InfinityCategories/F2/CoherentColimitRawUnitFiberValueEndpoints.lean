module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUnitFiberValue
public import SerrePositivity.InfinityCategories.F2.FunctorSequentialPostFiberMapVertex

/-!
概要：raw fiber 二面比較の固定値への実両端を、元の native 中央比較の実両端へ揃える。
方針：二つの元の相対後合成の全射から端点を計算し、元の頂点等式と照合する。
規約：元の全二面と値射を保持。使われ方：raw fiber 比較の値の厳密同定と反映。
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
local notation "p" => leftUnstraighteningProjection F
local notation "uF" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "uG" => coconeTransformationHomotopy (coherentDiagramTotalCocone G)
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- raw fiber 比較の実始点の固定値への像は、元の native 下面実合成射。 -/
lemma coherentColimitRawUnitFiberValue_source_map :
    (coherentColimitRawLowerCompositeAction B a ≫ P) ≫ V =
      coherentColimitLowerCompositeAction B a := by
  have hr := functorSequentialPost_fiberMap_vertex uF ca p
    (𝟙 (leftUnstraightening F)) (Category.id_comp p) V
  have hn := coherentColimitValueProjection_lower_vertex B a
  rw [constantTargetValueProjectionTo_eq_fiberValueTo] at hn
  apply functorVertex_injective
  simpa only [coherentColimitRawLowerCompositeAction, coherentColimitRawConstantFiberProjection,
    Category.id_comp, Category.assoc] using hr.symm.trans hn

/-- raw fiber 比較の実終点の固定値への像は、元の native 上面実合成射。 -/
lemma coherentColimitRawUnitFiberValue_target_map :
    (coherentColimitRawUpperCompositeAction B a ≫ P) ≫ V =
      coherentColimitUpperCompositeAction B a := by
  have hr := functorSequentialPost_fiberMap_vertex a uG p
    (𝟙 (leftUnstraightening F)) (Category.id_comp p) V
  have hn := coherentColimitValueProjection_upper_vertex B a
  rw [constantTargetValueProjectionTo_eq_fiberValueTo] at hn
  apply functorVertex_injective
  simpa only [coherentColimitRawUpperCompositeAction, coherentColimitRawConstantFiberProjection,
    Category.id_comp, Category.assoc] using hr.symm.trans hn

/-- 元の raw fiber 比較を同じ実両端の固定値へ写すと、元の native 中央比較に等しい。 -/
lemma coherentColimitRawUnitFiberValue_eq_native :
    functorIsoOfEq ((coherentColimitRawUnitFiberComparison B a).postcomp V)
      (coherentColimitRawUnitFiberValue_source_map B a)
      (coherentColimitRawUnitFiberValue_target_map B a) =
    coherentColimitNativeTriangleActionComparison B a := by
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentColimitRawUnitFiberComparison_valueTo_heq_native B a))

end SerrePositivity.InfinityCategories.F2
