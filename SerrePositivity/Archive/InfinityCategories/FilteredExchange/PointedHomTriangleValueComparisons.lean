module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeRefinementValueVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightRefinementValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomRefinementValueCoherence

/-!
概要：元の三角形の長辺・二辺合成で、同じ全 Hom 比較の値の成分を保持する。
方針：反転 Hom と右区間の実頂点の等式だけで元の比較の両端を正規化する。
規約：同じ全係数と指定比較を保持。使われ方：指定三角形の値の整合式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "H" => SimplicialCategory.sHom K L
local notation "e" => coherentTriangleHomotopy s
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))
local notation "η" => pointedLeftHomValueActionIso K L
local notation "l" => ULift.up (SSet.opObjEquiv.symm (SimplicialObject.δ H 1 e))
local notation "c" => ULift.up (SSet.opObjEquiv.symm (SimplicialObject.δ H 0 e))

local notation "F" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "G" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "D" => coherentEdgeHom (SpaceInfinity.δ 1 s)
local notation "U" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject F))
local notation "W" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject G))
local notation "Z" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject D))

/-- 元の長辺の同じ全作用比較を、元の指定長辺と同じ右輸送の値の頂点へ移す。 -/
def pointedHomTriangleLongValueComparison :
    VertexIso (functorVertex ((Z ≫ pointedCoherentFiberComparison L) ≫ V))
      ((NatTrans.app P (Opposite.op ⦋0⦌))
        ((pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex D)))) :=
  vertexIsoOfEq (FunctorIso.app η l ≪≫
    VertexIso.map (VertexIso.map (coherentKanRefinementSourceComparison K L e)
      (pointedIntervalValueAction K L)) P)
    (pointedOppositeRefinementValue_target_vertex s V)
    (congrArg (NatTrans.app P (Opposite.op ⦋0⦌))
      (pointedRightRefinementValue_source_eq_triangle s))

/-- 元の二辺合成の同じ全作用比較を、同じ二辺作用と右輸送の値の頂点へ移す。 -/
def pointedHomTriangleCompositeValueComparison :
    VertexIso (functorVertex (((U ≫ W) ≫ pointedCoherentFiberComparison L) ≫ V))
      ((NatTrans.app P (Opposite.op ⦋0⦌))
        ((pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex (F ≫ G))))) :=
  vertexIsoOfEq (FunctorIso.app η c ≪≫
    VertexIso.map (VertexIso.map (coherentKanRefinementTargetComparison K L e)
      (pointedIntervalValueAction K L)) P)
    (pointedOppositeRefinementValue_source_vertex s V)
    (congrArg (NatTrans.app P (Opposite.op ⦋0⦌))
      (pointedRightRefinementValue_target_eq_triangle s))

end SerrePositivity.InfinityCategories.F2
