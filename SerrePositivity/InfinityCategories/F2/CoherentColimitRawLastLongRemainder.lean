module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawLastPointAction
public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerValueToCancellation

/-!
概要：同じ二長辺輸送の指定比較と新長辺の残余を、元の実合成射へ正規化する。
方針：同じ指定点で実両端を計算し、元の最後辺比較と値を照合する。
規約：元の二輸送と指定比較を保持。使われ方：元の長辺残余の厳密な消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "w" => coherentColimitConstantTriangleLongTransport B T
local notation "U" => coherentColimitTriangleRawLastLongTransport B T
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)

/-- 元の二長辺輸送の endpointIso の一点値を、同じ実両端で保持する。 -/
def coherentColimitRawLastLongEndpointPointIso :=
  functorIsoOfEq (FunctorIso.precomp
    (FiberTransportFamily.endpointIso pointedSpaceProjection P (intervalMappingUncurry A)
      (intervalMappingUncurry_one A) w U) s)
    (coherentColimitConstantTriangleLongTransport_endpoint_point B T l)
    (coherentColimitTriangleRawLastLongTransport_point_endpoint B T l)

/-- 同じ実両端の二長辺比較は、元の最後辺の指定一点比較の同じ第一作用前合成に等しい。 -/
lemma coherentColimitRawLastLongEndpointPointIso_eq_point :
    coherentColimitRawLastLongEndpointPointIso B T =
      coherentColimitRawLastPointActionIso B a b := by
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    ((coherentColimitTriangleRawLastLongEndpointIso_heq_point B T).trans
      (coherentColimitRawLastPointActionIso_heq_point B a b).symm))

/-- raw 普遍最終辺を持つ同じ長辺輸送の、元の指定点での残余の指定比較。 -/
def coherentColimitRawLastLongRemainderIso :=
  functorIsoOfEq ((pointedIntervalTransportComparison P A U).precomp s)
    (coherentColimitTriangleRawLastLongTransport_point_endpoint B T l) rfl

end SerrePositivity.InfinityCategories.F2
