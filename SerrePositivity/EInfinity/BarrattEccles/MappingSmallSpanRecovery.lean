module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceResolutionFiberComparison
public import SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck

/-!
# 小さい全左脚・全右脚の図式から元の三本矢への回収

概要：元の脚と中間射を down し、元の三本矢の nerve へ戻す。
方針：明示的な小さい comma の同値・宇宙比較・元の三本矢の表示同値を合成。
規約：同じ元の代数と脚を保持。単体集合モデルや元の対象の cofibrancy は不要。
使われ方：元の共通添字からの右比較射の厳密な因子分解。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の小さい全図式から、同じ元の三本矢の nerve への回収射。 -/
def mappingSmallSpanRecoveryNerveMap (X Y : (operad A).Algebra) :
    nerve (Grothendieck (mappingSmallSpanRightDiagram A X Y)) ⟶
      nerve (algebraSpecialHammock A X Y) := by
  let := modelCategory A
  exact FrameHom.SmallCommaGrothendieck.recoveryNerveMap.{u + 1, u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations _) X)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.rightSliceForget (trivialCofibrations _) Y) ≫
    (FrameHom.Thomason.selfLiftIso _).hom ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.fromComma (trivialFibrations _) (trivialCofibrations _) X Y)

/-- 全次数で元の中間射を down して取り出す。 -/
lemma mappingSmallSpanRecoveryNerveMap_middle (X Y : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ)
    (c : (nerve (Grothendieck (mappingSmallSpanRightDiagram A X Y))).obj n)
    (j : Fin (n.unop.len + 1)) :
    (((mappingSmallSpanRecoveryNerveMap A X Y).app n c).obj j).middle =
      (c.obj j).fiber.hom.down := rfl

/-- 同じ元の全図式の回収射そのものは局所化で可逆。 -/
lemma mappingSmallSpanRecoveryNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSmallSpanRecoveryNerveMap A X Y)) := by
  let := modelCategory A
  have := FrameHom.SmallCommaGrothendieck.recoveryNerveMap_localized_isIso.{u + 1, u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations _) X)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.rightSliceForget (trivialCofibrations _) Y)
  have : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.fromComma (trivialFibrations _) (trivialCofibrations _) X Y))) :=
    (FrameHom.NerveEquivalenceImage.imageIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.commaEquivalence
      (trivialFibrations _) (trivialCofibrations _) X Y).symm AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  dsimp only [mappingSmallSpanRecoveryNerveMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
