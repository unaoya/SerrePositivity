module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedReverseKanCompositionFiber

/-!
概要：元の全反転 Hom 作用の値を、同じ左区間の実対角輸送へ接続する。
方針：F1 の全係数合成輸送の始点を、厳密に同じ二係数作用へ戻す。
規約：元の全係数と指定 fiber の移送を保持。使われ方：左精密化の値の整合式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の全反転 Hom の同じ二係数作用の値は、左区間による対角輸送と比較される。 -/
def pointedLeftHomDiagonalValueIso {P : SSet.{u + 1}} (K L : KanObject.{u})
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op) :
    FunctorIso
      (lift y x ≫ (uliftTensorIso (SimplicialCategory.sHom K L).op
        (SimplicialCategory.sHom pointKanObject K).op).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
        pointedCoherentFiberComparison L ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent L).symm) ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom)
      (diagonalFiberTransport pointedSpaceProjection
        (x ≫ pointedCoherentFiberComparison K ≫
          eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent K).symm))
        (y ≫ coherentKanLeftHomInterval K L) ≫
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom) := by
  have hs : lift
      (x ≫ (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom)
      (y ≫ (uliftOppositeIso (SimplicialCategory.sHom K L)).hom) ≫
        coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
          (Opposite.op pointKanObject) ≫ pointedReverseKanFiberComparison L =
      lift y x ≫ (uliftTensorIso (SimplicialCategory.sHom K L).op
        (SimplicialCategory.sHom pointKanObject K).op).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
        pointedCoherentFiberComparison L ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent L).symm) := by
    rw [← lift_map_assoc, pointedReverseKanComposition_fiber, lift_braiding_hom_assoc]
  exact functorIsoOfEq (pointedReverseKanDiagonalValueIso K L x y)
    (by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom) hs) rfl

end SerrePositivity.InfinityCategories.F2
