module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyTransport

/-!
概要：元の右 Hom 合成四角形に動く点・射を入力した両端を、同じ実二作用へ厳密に戻す。
方針：元の一点係数の合成と、同じ恒等点輸送の全係数公式を使う。
規約：元の点・射・全パラメーターを保持。使われ方：指定比較の前合成の値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "c" => x ≫ CategoryTheory.Functor.map SSet.uliftFunctor
  (Iso.inv (pointFunctorEvaluationIso (KanObject.obj K)))

/-- 元の合成四角形の二段輸送の初点作用は、同じ右 fiber 比較の点の輸送そのもの。 -/
lemma pointedRightFamilyTransport_diagonal_source :
    diagonalFiberTransport pointedSpaceProjection
      (diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
        (c ≫ coherentKanRightHomInterval pointKanObject K))
      (y ≫ coherentKanRightHomInterval K L) =
    diagonalFiberTransport pointedSpaceProjection (x ≫ pointedRightFiberComparison K)
      (y ≫ coherentKanRightHomInterval K L) := by
  rw [Category.assoc, HomotopyLimits.pointedRightFiberComparison_parameter]

/-- 元の合成四角形の合成輸送は、同じ動く射での評価の後の右 fiber 比較そのもの。 -/
lemma pointedRightFamilyTransport_diagonal_target :
    diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
      (lift c y ≫ coherentHomComposition pointKanObject K L ≫
        coherentKanRightHomInterval pointKanObject L) =
      pointedRightFamilyEvaluation x y ≫ pointedRightFiberComparison L := by
  have hl : lift c y ≫ coherentHomComposition pointKanObject K L ≫
      coherentKanRightHomInterval pointKanObject L = pointedRightFamilyEvaluation x y ≫
        (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso L.obj).inv ≫
          coherentKanRightHomInterval pointKanObject L := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ coherentKanRightHomInterval pointKanObject L)
        (coherentRightPointCoefficient_family x y)).trans (Category.assoc _ _ _))
  rw [hl, HomotopyLimits.pointedRightFiberComparison_parameter]

end SerrePositivity.InfinityCategories.F2
