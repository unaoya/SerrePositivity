module

public import SerrePositivity.EInfinity.FrameHom.TerminalFiberBaseHomotopy
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluationTriangle

/-!
# 実 corner 評価の左円柱は同じ終対象 fiber の底円柱の像

概要：元の左円柱を Over n に射影した実評価の底円柱から回収する。
方針：二つの元の pullback.condition と点図式の等式輸送の射影式を接続する。
規約：同じ全円柱・選択済み評価・元の q を保つ。
使われ方：全関手圏での終対象性による標準左脚との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)]
  {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b)
    (roofTargetProjection A Y q))

lemma roofCornerEvaluationLeftHomotopy_h_base :
    (roofCornerEvaluationLeftHomotopy A Y q b f).h =
      (terminalFiberBaseHomotopy (roofCornerNormalizedProjection A Y q b)
        (roofCornerTerminal A Y q b) (roofCornerTerminalEvaluation A Y q b)
        (f ≫ roofCornerNormalizationMap A Y q b)).h ≫
      nerveMap (Over.forget (roofTargetDegree A Y q b)) ≫ nerveMap A ≫ q := by
  have hraw := pullback.condition
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q))
    (g := nerveMap A ≫ q)
  have hnorm := pullback.condition (f := roofTargetProjection A Y q)
    (g := nerveMap (Over.forget (roofTargetDegree A Y q b)))
  change ((f ▷ (Δ[1] : SSet.{u})) ≫ (roofCornerEvaluationSliceHomotopy A Y q b).h) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) = _
  rw [roofCornerEvaluationSliceHomotopy_h, terminalFiberBaseHomotopy_h]
  simp only [Category.assoc, comp_whiskerRight, roofTargetSlicePointIso_projection]
  rw [hraw, reassoc_of% hnorm]

end SerrePositivity.EInfinity.FrameHom.FrameArrows
