module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedOppositeTriangleIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.OppositeKanPostcomposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：反転精密化の作用の指定同型を元の二段作用から長辺作用への関手同型にする。
方針：実 Hom 頂点の式と同じ元の二辺の厳密な合成則で両端だけを正規化する。
規約：元の実辺の類を変更しない。
使われ方：長辺値式の指定単位・余単位の整理。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "h" => coherentEdgeHom (SpaceInfinity.δ 1 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject f))
local notation "Q" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject g))
local notation "R" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject h))

/-- 元の反転精密化の作用の始点は元の二段の後合成関手の頂点。 -/
lemma pointedOppositeTriangleAction_source_vertex :
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (functorVertex (f ≫ g)))) =
      functorVertex ((P ≫ Q) ≫ pointedCoherentFiberComparison L) :=
  (pointedOppositeHomAction_vertex (f ≫ g)).trans
    (congrArg functorVertex (congrArg (fun p ↦ p ≫ pointedCoherentFiberComparison L)
      (uliftOppositeKanPostcomposition_comp f g)))

/-- 元の反転精密化の作用の終点は元の長辺の後合成関手の頂点。 -/
lemma pointedOppositeTriangleAction_target_vertex :
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (functorVertex h))) =
      functorVertex (R ≫ pointedCoherentFiberComparison L) :=
  pointedOppositeHomAction_vertex h

/-- 同じ元の精密化の作用の類を、元の二段作用と長辺作用の関手同型として保持。 -/
def pointedOppositeTriangleFunctorIso :
    FunctorIso ((P ≫ Q) ≫ pointedCoherentFiberComparison L)
      (R ≫ pointedCoherentFiberComparison L) :=
  vertexIsoOfEq (pointedOppositeTriangleActionIso s)
    (pointedOppositeTriangleAction_source_vertex s) (pointedOppositeTriangleAction_target_vertex s)

/-- 両端の正規化後も元の反転精密化の作用の類そのものを保持する。 -/
lemma pointedOppositeTriangleFunctorIso_heq_action :
    HEq (pointedOppositeTriangleFunctorIso s) (pointedOppositeTriangleActionIso s) :=
  vertexIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
