module

public import SerrePositivity.InfinityCategories.F2.PointedLeftHomValueAction
public import SerrePositivity.InfinityCategories.F2.CoherentKanOppositeRefinementIso
public import SerrePositivity.InfinityCategories.F2.FunctorIsoComponentNaturality

/-!
概要：元の反転精密化に沿って、全左 Hom 作用比較の指定成分が整合する。
方針：同じ実辺の類に全関手同型の自然性を適用する。
規約：元の反転辺と左区間像の類を保持。使われ方：同じ右区間との値の比較。
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

/-- 元の指定精密化に沿う、全反転 Hom 作用の値と左区間輸送の同じ正方形。 -/
lemma pointedLeftHomRefinement_square (K L : KanObject.{u})
    (e : (SimplicialCategory.sHom K L) _⦋1⦌) :
    let C := pointedCoherentFiberComparison K ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent K).symm)
    let F := pointedOppositeHomAction K L ≫
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom pointKanObject K).op)).map
        (eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent L).symm) ≫
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom)
    let η := pointedLeftHomValueActionIso K L
    VertexIso.map (coherentKanOppositeRefinementIso K L e) F ≪≫
        η.app (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 1 e))) =
      η.app (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 0 e))) ≪≫
        VertexIso.map
          (VertexIso.map (coherentKanLeftRefinementIso K L e) (pointedIntervalValueAction K L))
          ((pre C).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)) := by
  dsimp only
  have hr : VertexIso.map (coherentKanOppositeRefinementIso K L e)
      ((coherentKanLeftHomInterval K L ≫ pointedIntervalValueAction K L) ≫
        (pre (pointedCoherentFiberComparison K ≫
          eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent K).symm))).app
              ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)) =
      VertexIso.map
        (VertexIso.map (coherentKanLeftRefinementIso K L e) (pointedIntervalValueAction K L))
        ((pre (pointedCoherentFiberComparison K ≫
          eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent K).symm))).app
              ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)) := by
    apply Iso.ext
    rfl
  have h := functorIso_app_vertexIso_naturality (pointedLeftHomValueActionIso K L)
    (coherentKanOppositeRefinementIso K L e)
  rw [hr] at h
  exact h

end SerrePositivity.InfinityCategories.F2
