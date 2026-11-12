module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedSpaceParametrizedEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberTransportFamilySourceComparison

/-!
概要：任意の指定区間族の選択済み輸送を、同じ普遍輸送射の制限へ比較する。
方針：始点が恒等の輸送族の比較で、区間の curry の往復と恒等の前合成を消す。
規約：全パラメータを保持。使われ方：二つの実際の輸送の同型を元の辺へ反映する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定区間族の実際の輸送作用は、同じ普遍輸送射の元の区間族による制限と同型。 -/
def pointedIntervalTransport_mapIso {T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) :
    FunctorIso (pointedIntervalTransport a).map
      (a ≫ parametrizedFiberTransport pointedSpaceProjection x y) := by
  have e := (pointedIntervalTransport a).mapIso_parametrizedSource pointedSpaceProjection
    (𝟙 _) (intervalMappingUncurry a) (intervalMappingUncurry_zero a)
      (intervalMappingUncurry_one a)
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hc] at e
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using e

end SerrePositivity.InfinityCategories.F2
