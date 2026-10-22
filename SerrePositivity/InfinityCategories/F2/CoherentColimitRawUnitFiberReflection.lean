module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUnitFiberValueEndpoints
public import SerrePositivity.InfinityCategories.F2.PointedFiberValueToReflection

/-!
概要：同じ raw fiber 両端間の比較が元の二面比較に等しいことを、固定 native 値で判定する。
方針：元の実両端を揃えた値射影の単射性と、元の指定中央比較の等式を使う。
規約：比較を再選択しない。使われ方：残る全区間族比較の指定値の反映。
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
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 元の raw fiber 比較への一致は、同じ実両端の固定 native 中央比較への像で判定できる。 -/
lemma coherentColimitRawUnitFiberComparison_eq_iff_valueTo
    (e : FunctorIso (coherentColimitRawLowerCompositeAction B a ≫ P)
      (coherentColimitRawUpperCompositeAction B a ≫ P)) :
    functorIsoOfEq (e.postcomp V)
      (coherentColimitRawUnitFiberValue_source_map B a)
      (coherentColimitRawUnitFiberValue_target_map B a) =
      coherentColimitNativeTriangleActionComparison B a ↔
    e = coherentColimitRawUnitFiberComparison B a := by
  constructor
  · intro h
    apply pointedFiberValueTo_postcompose_transport_injective (leftUnstraightening F)
      (coherentDiagramTotalCocone_vertex G)
      (coherentColimitRawUnitFiberValue_source_map B a)
      (coherentColimitRawUnitFiberValue_target_map B a)
    exact h.trans (coherentColimitRawUnitFiberValue_eq_native B a).symm
  · intro h
    subst e
    exact coherentColimitRawUnitFiberValue_eq_native B a

end SerrePositivity.InfinityCategories.F2
