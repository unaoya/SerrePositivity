module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedLeftHomDiagonalValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberValueCurry

/-!
概要：全反転 Hom 作用の値を同じ全左区間の普遍輸送の値へ比較する。
方針：元の二独立係数の指定合成輸送を curry し、両端を厳密に回収する。
規約：頂点ごとの同型に弱めない。使われ方：元の反転精密化の指定 path の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の全反転 Hom の値の作用と、同じ左区間輸送の値との指定された全族比較。 -/
def pointedLeftHomValueActionIso (K L : KanObject.{u}) :
    FunctorIso
      (pointedOppositeHomAction K L ≫
        (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom pointKanObject K).op)).map
          (eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent L).symm) ≫
            (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom))
      ((coherentKanLeftHomInterval K L ≫ pointedIntervalValueAction K L) ≫
        (pre (pointedCoherentFiberComparison K ≫
          eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent K).symm))).app
              ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)) := by
  let A := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom pointKanObject K).op
  let H := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op
  refine functorIsoOfEq
    ((pointedLeftHomDiagonalValueIso K L (fst A H) (snd A H)).curry) ?_ ?_
  · rw [lift_snd_fst]
    change curry (((β_ A H).hom ≫
      (uliftTensorIso (SimplicialCategory.sHom K L).op
        (SimplicialCategory.sHom pointKanObject K).op).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
        pointedCoherentFiberComparison L) ≫
      (eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent L).symm) ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom)) = _
    rw [curry_natural_right]
    rfl
  · rw [diagonalFiberValue_curry]
    simp only [Category.assoc, pointedIntervalValueAction]
    rw [(pre (pointedCoherentFiberComparison K ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent K).symm))).naturality]

end SerrePositivity.InfinityCategories.F2
