module

public import SerrePositivity.InfinityCategories.F2.PointedLeftHomRefinementSquare
public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementValueSquare
public import SerrePositivity.InfinityCategories.F2.IsoComparisonThreeFactor

/-!
概要：元の反転精密化の作用と右精密化輸送を、同じ全係数の比較で結ぶ。
方針：全左 Hom 作用の自然性に左右区間の同じ四同型の整合式を合成する。
規約：元の指定精密化と全比較成分を保持。使われ方：長辺値式の指定因子の整理。
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

/-- 元の反転 Hom の作用と元の右区間の指定精密化は同じ値の比較で整合する。 -/
lemma pointedHomRefinement_value_coherence (K L : KanObject.{u})
    (e : (SimplicialCategory.sHom K L) _⦋1⦌) :
    let C := pointedCoherentFiberComparison K ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent K).symm)
    let P := (pre C).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)
    let F := pointedOppositeHomAction K L ≫
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom pointKanObject K).op)).map
        (eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent L).symm) ≫
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom)
    let η := pointedLeftHomValueActionIso K L
    VertexIso.map (coherentKanOppositeRefinementIso K L e) F ≪≫
        η.app (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 1 e))) ≪≫
        VertexIso.map (VertexIso.map (coherentKanRefinementSourceComparison K L e)
          (pointedIntervalValueAction K L)) P ≪≫
        VertexIso.map (VertexIso.map (coherentKanRightRefinementIso K L e)
          (pointedIntervalValueAction K L)) P =
      η.app (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 0 e))) ≪≫
        VertexIso.map (VertexIso.map (coherentKanRefinementTargetComparison K L e)
          (pointedIntervalValueAction K L)) P := by
  exact iso_comparison_compose_three _ _ _ _ _ _ _
    (pointedLeftHomRefinement_square K L e)
    (vertexIso_map_three_factor _ _ _ _
      ((pre (pointedCoherentFiberComparison K ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent K).symm))).app
            ((SSet.uliftFunctor.{u + 1, u}).obj L.obj))
      (coherentKanRefinement_value_square K L e))

end SerrePositivity.InfinityCategories.F2
