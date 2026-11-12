module

public import SerrePositivity.KST.Spectra.SpectrumTracedActualRightDifferenceSquare
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitStageSquare

/-!
概要：元の実評価を始点とする右側差の同じ正方形を、段射の構造座標へ戻す。
方針：同じ正方形を転置し、源の非定数構造辺の同じ後合成へ同定する。
規約：四辺全体と指定比較三角形を保持。使われ方：元の自然性区間との相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ RawSpectrumMapping.pointedSpace X Y.toKanSequence)

/-- 同じ右側段差の転置は、次段の源制限と前段の構造像を結ぶ実正方形を持つ。 -/
def tracedActualRightDifferenceStageSquare (n : ℕ) :
    SSet.Homotopy
      ((((tracedActualStageRightDifference X Y φ (n + 1)).path).basedTranspose.pre
        (X.sigma n)).path)
      ((PointedMapping.VerticalPath.basedPost
        (PointedMapping.VerticalPath.forgetProjection
          ((tracedActualStageRightDifference X Y φ n).path).basedTranspose.suspension)
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path)
    where
  h := (tracedActualRightDifferenceSquare X Y φ n).h ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right
  h₀ := by
    rw [← Category.assoc, (tracedActualRightDifferenceSquare X Y φ n).h₀]
    exact basedTranspose_restriction_path (X.sigma n)
      (tracedActualStageRightDifference X Y φ (n + 1)).path
  h₁ := by
    rw [← Category.assoc, (tracedActualRightDifferenceSquare X Y φ n).h₁]
    exact basedTranspose_step_path X (KanSequence.signedLoopTail Y.toKanSequence) n
      (tracedActualStageRightDifference X Y φ n).path
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 同じ段射正方形の左辺は、元の厳密実評価の構造頂点で全区間が一定。 -/
lemma tracedActualRightDifferenceStageSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (tracedActualRightDifferenceStageSquare X Y φ n).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right.app _
          (PointedMapping.familyVertex
            ((φ ≫ (signedEvaluationAt X Y (tracedOriginalLoopModelMap X) ≫
              pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)) ≫
                pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n))) := by
  change SquareAdjustment.leftSide ≫ ((tracedActualRightDifferenceSquare X Y φ n).h ≫ _) = _
  rw [← Category.assoc, tracedActualRightDifferenceSquare_start, SSet.const_comp]
  rfl

/-- 右辺全体は、同じ源構造入力区間への同じパラメータ列射の後合成そのもの。 -/
lemma tracedActualRightDifferenceStageSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (tracedActualRightDifferenceStageSquare X Y φ n).h =
      (tracedSourceUnitStructureInterval X Y φ n).path := by
  change SquareAdjustment.rightSide ≫ ((tracedActualRightDifferenceSquare X Y φ n).h ≫ _) = _
  rw [← Category.assoc, tracedActualRightDifferenceSquare_finish,
    PointedMapping.VerticalPath.basedPreAction_action_path]
  change ((OmegaSpectrum.signedLoopUnitStructurePath X n).path ≫
    (tracedSourceUnitStructureAction X Y φ n).right) ≫ _ = _
  have h := congrArg Under.Hom.right (tracedSourceUnitStructureAction_transpose X Y φ n)
  change (tracedSourceUnitStructureAction X Y φ n).right ≫ _ = _ at h
  rw [Category.assoc, h]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
