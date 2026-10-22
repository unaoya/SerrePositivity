module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawLastLongRemainder
public import SerrePositivity.InfinityCategories.F2.FunctorIsoInverseMiddleCancellation

/-!
概要：元の長辺残余の逆と元の最後辺の指定一点比較を、新長辺残余の逆へ消去する。
方針：元の二長辺輸送の普遍比較の合成則を同じ指定点で評価する。
規約：元の全三角形・三比較・実両端を保持。使われ方：a6 の元の模型比較式の消去。
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

/-- 元の長辺残余の逆と元の最後辺の指定比較は、同じ新長辺残余の逆へ厳密に消去される。 -/
lemma coherentColimitRawLastLong_inverse_middle_cancel :
    (coherentColimitConstantTriangleRemainderIso B T).symm ≪≫
      coherentColimitRawLastPointActionIso B a b =
    (coherentColimitRawLastLongRemainderIso B T).symm := by
  have h := pointedIntervalTransportComparison_trans P A w U
  have hp := congrArg (fun e => FunctorIso.precomp e s) h
  have he := functorIso_precomp_trans
    (FiberTransportFamily.endpointIso pointedSpaceProjection P (intervalMappingUncurry A)
      (intervalMappingUncurry_one A) w U) (pointedIntervalTransportComparison P A U) s
  have hc := functorIsoOfEq_inverse_middle_cancel
    (FunctorIso.precomp (FiberTransportFamily.endpointIso pointedSpaceProjection P
      (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U) s)
    ((pointedIntervalTransportComparison P A w).precomp s)
    ((pointedIntervalTransportComparison P A U).precomp s)
    (coherentColimitConstantTriangleLongTransport_endpoint_point B T l)
    (coherentColimitTriangleRawLastLongTransport_point_endpoint B T l) (he.symm.trans hp)
  change (coherentColimitConstantTriangleRemainderIso B T).symm ≪≫
    coherentColimitRawLastLongEndpointPointIso B T =
      (coherentColimitRawLastLongRemainderIso B T).symm at hc
  rw [coherentColimitRawLastLongEndpointPointIso_eq_point] at hc
  exact hc

end SerrePositivity.InfinityCategories.F2
