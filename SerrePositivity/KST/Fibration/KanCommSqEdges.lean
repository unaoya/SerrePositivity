module
public import SerrePositivity.KST.Fibration.HomotopyPullbackInfinitySquare
public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs
public import SerrePositivity.KST.LocalizingInvariants.StrictCospanConePoints
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeLegs

/-! # 元の Kan 四角形の全 coherent 表示から、元の四射を厳密に回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable {P X Y Z : KanObject.{u}}
  {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
  (sq : CommSq a b f g)

/-- 右辺は、元の右の構造射 g の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_right :
    squareRightEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (coherentNerveEdge (show Y ⟶ Z from g)).edge := by
  rw [kanCommSqInfinitySquare, coneSquare_right]
  exact CospanShape.strictDiagram_left (show Y ⟶ Z from g) (show X ⟶ Z from f)

/-- 上辺は、元のもう一方の構造射 f の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_top :
    squareTopEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (coherentNerveEdge (show X ⟶ Z from f)).edge := by
  rw [kanCommSqInfinitySquare, coneSquare_top]
  exact CospanShape.strictDiagram_right (show Y ⟶ Z from g) (show X ⟶ Z from f)

/-- 下辺は、元の頂点からの射 b の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_bottom :
    squareBottomEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (coherentNerveEdge (show P ⟶ Y from b)).edge := by
  rw [kanCommSqInfinitySquare, coneSquare_bottom_leg]
  change (joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫
      joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
        strictCoherentConeMap (kanCommSqCone sq) = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, StrictCospanCone.left_point]
  change strictCoherentConeLeg (kanCommSqCone sq) (AsSmall.up.obj WalkingCospan.left) = _
  rw [strictCoherentConeLeg_eq]
  rfl

/-- 左辺は、元の頂点からの射 a の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_left :
    squareLeftEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (coherentNerveEdge (show P ⟶ X from a)).edge := by
  rw [kanCommSqInfinitySquare, coneSquare_left_leg]
  change (joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫
      joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
        strictCoherentConeMap (kanCommSqCone sq) = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, StrictCospanCone.right_point]
  change strictCoherentConeLeg (kanCommSqCone sq) (AsSmall.up.obj WalkingCospan.right) = _
  rw [strictCoherentConeLeg_eq]
  rfl

end SerrePositivity.KST.Fibration
