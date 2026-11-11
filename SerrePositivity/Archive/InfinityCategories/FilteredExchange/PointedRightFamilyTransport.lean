module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyCoefficient
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedRightTransportNaturality

/-!
概要：動く Kan 点と Kan 射の全族の評価を、同じ区間族の pointed 輸送へ比較する。
方針：同じ合成四角形へ二つの動く係数を入力し、厳密な一点係数の合成式を使う。
規約：全パラメータを保持。使われ方：二単体・path の比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じパラメータで動く点と射の評価は、右 fiber 比較を介して元の区間輸送に整合する。 -/
def pointedRightFamilyTransportIso {K L : KanObject.{u}} {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) :
    FunctorIso (pointedRightFamilyEvaluation x y ≫ pointedRightFiberComparison L)
      (diagonalFiberTransport pointedSpaceProjection (x ≫ pointedRightFiberComparison K)
        (y ≫ coherentKanRightHomInterval K L)) := by
  let c := x ≫ (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv
  have e := coherentKanRightCompositionTransport_diagonalIso pointKanObject K L
    pointedSpaceIdentityPoint c y
  have hs := HomotopyLimits.pointedRightFiberComparison_parameter K x
  have hl : lift c y ≫ coherentHomComposition pointKanObject K L ≫
      coherentKanRightHomInterval pointKanObject L = pointedRightFamilyEvaluation x y ≫
        (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso L.obj).inv ≫
          coherentKanRightHomInterval pointKanObject L := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ coherentKanRightHomInterval pointKanObject L)
        (coherentRightPointCoefficient_family x y)).trans (Category.assoc _ _ _))
  rw [hl] at e
  dsimp only [c] at e
  simp only [Category.assoc] at e
  rw [hs, HomotopyLimits.pointedRightFiberComparison_parameter] at e
  exact e.symm

end SerrePositivity.InfinityCategories.F2
