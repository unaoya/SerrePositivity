module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismEdgeValueRatioFactory
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedUniversalEdgeTargetValue
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueMorphismUniversalAction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity
/-!
概要：元の実辺の比の終点値を標準係数と同じ全 Hom の作用頂点で照合する。
方針：一般の実辺で native 値の式と標準係数の表示を先に合成する。
規約：全初期係数・実辺・元の native 輸送を保持する。
使われ方：最後辺の比と最後射評価の実頂点照合。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L)
/-- 概要：元の実辺の比の終点値は同じ作用の二段前作用の終点。
方針：native 値と標準係数を先に照合する。規約：全係数を保持。使われ方：最後射の三頂点。 -/
lemma pointedMorphismEdgeValueRatio_target_vertex_of_standard
    {P : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge)
    (q : P ⟶ vertexFiber pointedSpaceProjection x)
    (r : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op)
    (hq : q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx) = r ≫ C) :
    functorVertex (q ≫ (pointedMorphismEdgeValueRatio f e hx hy he).targetMap) =
      NatTrans.app ((pre r).app Y) (Opposite.op ⦋0⦌)
        (NatTrans.app ((pre C).app Y) (Opposite.op ⦋0⦌)
          ((pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
            (ULift.up (functorVertex f)))) := by
  rw [pointedValueHomTransport_morphism_vertex,
    functorVertex_precomposition, functorVertex_precomposition]
  apply congrArg functorVertex
  have h := pointedIntervalUniversalIso_target_value_change f e hx hy he q
  rw [hq] at h
  convert h using 1 <;> rfl
end
end SerrePositivity.InfinityCategories.F2
