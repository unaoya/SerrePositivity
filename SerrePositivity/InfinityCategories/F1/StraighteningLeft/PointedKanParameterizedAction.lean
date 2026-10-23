module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftPointHomReverseComposition
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedLeftIntervalComparison

/-!
概要：任意のパラメーター付き Kan 作用と実際の pointed-space の対角輸送の比較。
方針：同じ反転した合成 prism に標準係数を入れ、終点を元の射へ厳密に戻す。
規約：始点も辺も任意の同じパラメーターで動く。fiber の逆同値は選ばない。
使われ方：pointed 自然性の四角形の輸送を直接の Hom 作用へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元のパラメーター付き Kan 作用が与える、反転した値の間の左 Hom の辺の族。 -/
def kanParameterizedLeftHomInterval {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    (SSet.uliftFunctor.{u + 1, u}).obj T ⟶ intervalMappingSpace
      (spaceInfinityVertex (kanObjectOpFunctor.obj X))
      (spaceInfinityVertex (kanObjectOpFunctor.obj Y)) :=
  leftPointHomReverseParameter f ≫
    intervalMappingCurryOfEndpoints
      (pointedReverseKanHomInterval (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))
      (pointedReverseKanHomInterval_zero (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))
      (pointedReverseKanHomInterval_one (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))

/-- 標準の左解像比較は、動く始点と任意のパラメーター付き Kan 作用を普遍輸送へ移す。 -/
def pointedSpaceLeftResolution_parametrizedTransportIso
    {P : SSet.{u + 1}} {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj)
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj X.obj)
    (t : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj T) :
    FunctorIso
      (lift x t ≫ (HomotopyLimits.uliftTensorIso X.obj T).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedSpaceLeftResolutionComparison Y)
      (diagonalFiberTransport pointedSpaceProjection
        (x ≫ pointedSpaceLeftResolutionComparison X) (t ≫ kanParameterizedLeftHomInterval f)) := by
  let cX := (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso X).hom ≫
    (HomotopyLimits.uliftOppositeIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))).hom
  let cY := (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso Y).hom ≫
    (HomotopyLimits.uliftOppositeIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj Y))).hom
  have hX : cX ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj X) =
      pointedSpaceLeftResolutionComparison X := pointedReverseKanFiberComparison_resolution X
  have hY : cY ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) =
      pointedSpaceLeftResolutionComparison Y := pointedReverseKanFiberComparison_resolution Y
  let C := coherentReverseHomComposition (Opposite.op (kanObjectOpFunctor.obj Y))
    (Opposite.op (kanObjectOpFunctor.obj X)) (Opposite.op pointKanObject)
  have hEnd : ((cX ⊗ₘ leftPointHomReverseParameter f) ≫ C) ≫
      pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) =
      (HomotopyLimits.uliftTensorIso X.obj T).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedSpaceLeftResolutionComparison Y := by
    calc
      _ = ((HomotopyLimits.uliftTensorIso X.obj T).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map f ≫ cY) ≫
          pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) :=
        congrArg (fun k ↦ k ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y))
          (leftPointHomReverseComposition_coefficient f)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (HomotopyLimits.uliftTensorIso X.obj T).inv ≫
            (SSet.uliftFunctor.{u + 1, u}).map f ≫ k) hY
  have hProd : lift (x ≫ cX) (t ≫ leftPointHomReverseParameter f) =
      lift x t ≫ (cX ⊗ₘ leftPointHomReverseParameter f) := rfl
  have hLeft : lift (x ≫ cX) (t ≫ leftPointHomReverseParameter f) ≫ C ≫
      pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) =
      lift x t ≫ (HomotopyLimits.uliftTensorIso X.obj T).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedSpaceLeftResolutionComparison Y := by
    rw [hProd]
    simpa only [Category.assoc] using congrArg (fun k ↦ lift x t ≫ k) hEnd
  have e := pointedReverseKanCompositionTransport_diagonalIso
    (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y)
    (x ≫ cX) (t ≫ leftPointHomReverseParameter f)
  change FunctorIso (lift (x ≫ cX) (t ≫ leftPointHomReverseParameter f) ≫ C ≫
    pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y))
      (diagonalFiberTransport pointedSpaceProjection
        ((x ≫ cX) ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj X))
        ((t ≫ leftPointHomReverseParameter f) ≫
          intervalMappingCurryOfEndpoints
            (pointedReverseKanHomInterval (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))
            (pointedReverseKanHomInterval_zero (kanObjectOpFunctor.obj X)
              (kanObjectOpFunctor.obj Y))
            (pointedReverseKanHomInterval_one (kanObjectOpFunctor.obj X)
              (kanObjectOpFunctor.obj Y)))) at e
  rw [hLeft, Category.assoc x cX, hX] at e
  exact e

end SerrePositivity.InfinityCategories
