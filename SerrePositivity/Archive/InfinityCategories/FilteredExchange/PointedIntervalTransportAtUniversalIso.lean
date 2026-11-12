module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportPoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportUniversal
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：元の区間族の指定点の輸送を、同じ普遍輸送射の指定点での値へ戻す。
方針：元の全区間比較の同じ成分の実両端だけを揃える。
規約：元の区間族と指定比較を保持。使われ方：元の余極限辺と全 Kan Hom 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の指定点での実輸送と同じ普遍輸送の値を、元の全比較の同じ成分で結ぶ。 -/
def pointedIntervalTransportAt_universalIso {T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌) :
    FunctorIso (pointedIntervalTransportAt a l)
      ((functorVertexEquiv _ _).symm ((parametrizedFiberTransport pointedSpaceProjection x y).app
        (Opposite.op ⦋0⦌) (a.app (Opposite.op ⦋0⦌) l))) :=
  vertexIsoOfEq (VertexIso.map (pointedIntervalTransport_mapIso a) (evaluateFunctorAt l))
    ((evaluateFunctorAt_functorVertex l (pointedIntervalTransport a).map).trans
      ((functorVertexEquiv _ _).apply_symm_apply _).symm)
    ((evaluateFunctorAt_functorVertex l (a ≫ parametrizedFiberTransport
      pointedSpaceProjection x y)).trans ((functorVertexEquiv _ _).apply_symm_apply _).symm)

/-- quasi な係数では、同じ実輸送比較は元の全比較の指定成分と値まで一致する。 -/
lemma pointedIntervalTransportAt_universalIso_heq_app {T : SSet.{u + 1}} [Quasicategory T]
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌) :
    HEq (pointedIntervalTransportAt_universalIso a l)
      ((pointedIntervalTransport_mapIso a).app l) :=
  (vertexIsoOfEq_heq _ _ _).trans
    (functorIso_app_heq_evaluate (pointedIntervalTransport_mapIso a) l).symm

end SerrePositivity.InfinityCategories.F2
