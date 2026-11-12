module
public import SerrePositivity.KST.Fibration.HomotopyPullbackInfinitySquare
public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs
public import SerrePositivity.KST.LocalizingInvariants.StrictCospanConePoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeLegs

/-! # 元の Kan 四角形の全 coherent 表示から、元の四射を厳密に回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable {P X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
  {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
  (sq : CommSq a b f g)

/-- 右辺は、元の右の構造射 g の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show Y ⟶ Z from g)).edge := by
  rw [kanCommSqInfinitySquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right]
  exact CospanShape.strictDiagram_left (show Y ⟶ Z from g) (show X ⟶ Z from f)

/-- 上辺は、元のもう一方の構造射 f の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show X ⟶ Z from f)).edge := by
  rw [kanCommSqInfinitySquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top]
  exact CospanShape.strictDiagram_right (show Y ⟶ Z from g) (show X ⟶ Z from f)

/-- 下辺は、元の頂点からの射 b の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show P ⟶ Y from b)).edge := by
  rw [kanCommSqInfinitySquare, coneSquare_bottom_leg]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, StrictCospanCone.left_point]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq) (AsSmall.up.obj WalkingCospan.left) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg_eq]
  rfl

/-- 左辺は、元の頂点からの射 a の同じ coherent な辺である。 -/
theorem kanCommSqInfinitySquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show P ⟶ X from a)).edge := by
  rw [kanCommSqInfinitySquare, coneSquare_left_leg]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, StrictCospanCone.right_point]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq) (AsSmall.up.obj WalkingCospan.right) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg_eq]
  rfl

end SerrePositivity.KST.Fibration
