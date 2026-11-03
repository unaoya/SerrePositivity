module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedReverseKanFiberNormalization
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanLeftIntervalReverse
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalValueAction

/-!
概要：動く一点 Hom と反転 Hom の合成の値を同じ左区間の対角輸送へ接続する。
方針：F1 の指定された反転合成輸送を係数交換と同じ終点値で制限する。
規約：全独立係数と実 fiber を保持。使われ方：元の反転精密化の値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ全係数の反転合成の指定比較は、左区間による対角輸送の値を与える。 -/
def pointedReverseKanDiagonalValueIso {P : SSet.{u + 1}} (K L : KanObject.{u})
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op) :
    FunctorIso
      (CartesianMonoidalCategory.lift
        (x ≫ (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom)
        (y ≫ (uliftOppositeIso (SimplicialCategory.sHom K L)).hom) ≫
        coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
          (Opposite.op pointKanObject) ≫ pointedReverseKanFiberComparison L ≫
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom)
      (diagonalFiberTransport pointedSpaceProjection
        (x ≫ pointedCoherentFiberComparison K ≫
          eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent K).symm))
        (y ≫ coherentKanLeftHomInterval K L) ≫
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom) := by
  have hx : (x ≫ (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom) ≫
      pointedReverseKanFiberComparison K = x ≫ pointedCoherentFiberComparison K ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent K).symm) := by
    rw [Category.assoc, pointedReverseKanFiberComparison_normalized]
  have hy : (y ≫ (uliftOppositeIso (SimplicialCategory.sHom K L)).hom) ≫
      intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
        (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) =
      y ≫ coherentKanLeftHomInterval K L := by
    rw [← coherentKanLeftHomInterval_reverse]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [hx, hy, Category.assoc] using
    (pointedReverseKanCompositionTransport_diagonalIso K L
      (x ≫ (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom)
      (y ≫ (uliftOppositeIso (SimplicialCategory.sHom K L)).hom)).postcomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom

end SerrePositivity.InfinityCategories.F2
