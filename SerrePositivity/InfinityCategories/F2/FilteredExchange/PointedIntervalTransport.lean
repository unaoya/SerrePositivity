module

public import SerrePositivity.InfinityCategories.F1.FiberTransportFamilyNaturality
public import SerrePositivity.InfinityCategories.F1.PointedSpaces

/-!
概要：𝒮 内の区間の全族の普遍 pointed-space 輸送と、任意の同じ輸送の比較。
方針：元の fiber の恒等射からの輸送族を選び、係数の前合成と選択独立性を使う。
規約：底となる別の図式の選択に依存しない。
使われ方：定値図式間の unstraightening の作用の比較先。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の区間の全族に沿う fiber 間の輸送。
方針：始点 fiber の恒等係数からパラメータ全体を持ち上げる。
規約：元の区間を保持。使われ方：定値図式の作用の底に依存しない比較先。 -/
def pointedIntervalTransport {T : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace x y) :
    FiberTransportFamily (b := y) pointedSpaceProjection (𝟙 (vertexFiber pointedSpaceProjection x))
      (intervalMappingUncurry a) :=
  fiberTransportFamily pointedSpaceProjection (𝟙 _) (intervalMappingUncurry a)
    (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)

/-- 概要：同じ底の区間・始点の任意の輸送は、普遍輸送の係数による制限と同型。
方針：全族での輸送の選択独立性を適用する。
規約：全パラメータの関手同型。使われ方：定値 unstraightening の作用を元の fiber 作用へ移す。 -/
def pointedIntervalTransportComparison {K T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (f : K ⟶ vertexFiber pointedSpaceProjection x)
    (a : T ⟶ intervalMappingSpace x y)
    (w : FiberTransportFamily (b := y) pointedSpaceProjection f (intervalMappingUncurry a)) :
    FunctorIso w.endpoint ((f ▷ T) ≫ (pointedIntervalTransport a).endpoint) := by
  let U : FiberTransportFamily (b := y) pointedSpaceProjection f (intervalMappingUncurry a) := by
    simpa only [Category.comp_id] using (pointedIntervalTransport a).precomposeSource f
  exact w.endpointIso pointedSpaceProjection f (intervalMappingUncurry a)
    (intervalMappingUncurry_one a) U

end SerrePositivity.InfinityCategories.F2
