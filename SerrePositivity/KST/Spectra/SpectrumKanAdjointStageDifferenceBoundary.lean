module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStageDifferenceSquare

/-!
概要：共有辺から得た実比較正方形が、厳密な二つの終点を全区間で固定することを示す。
方針：相対外ホーン充填の左右辺を元の二つの定数終辺へ厳密に戻す。
規約：端点だけの可換性へ弱めない。使われ方：自由区間の境界上に垂直な構造区間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 比較正方形の左辺は、元の相対厳密化の終辺そのもの。 -/
lemma kanAdjointStageDifferenceSquare_left (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointStageDifferenceSquare X Y φ j n).h =
      SquareAdjustment.rightSide ≫
        (kanAdjointRelativeTracedStrictStageSquare X Y φ j n).h :=
  SquareAdjustment.SpecifiedDifference.square_left _ _ _ _ _

/-- 比較正方形の右辺は、元の単位正方形の終辺そのもの。 -/
lemma kanAdjointStageDifferenceSquare_right (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointStageDifferenceSquare X Y φ j n).h =
      SquareAdjustment.rightSide ≫ (kanAdjointTracedUnitStrictStageSquare X Y φ n).h :=
  SquareAdjustment.SpecifiedDifference.square_right _ _ _ _ _

/-- 左辺全体は、同じ厳密な相対列射の構造頂点で一定。 -/
lemma kanAdjointStageDifferenceSquare_left_constant (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointStageDifferenceSquare X Y φ j n).h =
      SSet.const (PointedMapping.familyVertex
        (PointedSimplicialSet.circle.{u} ◁ (kanAdjointRelativeTracedParameterHom X Y φ j).app n ≫
          (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)) := by
  rw [kanAdjointStageDifferenceSquare_left]
  exact kanAdjointRelativeTracedPastedSquare_finish X Y φ j n

/-- 右辺全体も、同じ厳密な単位後合成の構造頂点で一定。 -/
lemma kanAdjointStageDifferenceSquare_right_constant (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointStageDifferenceSquare X Y φ j n).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right.app _
        (PointedMapping.familyVertex
          ((φ ≫ pointedPost X
              (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
            pointedPost X (OmegaSpectrum.signedLoopProjection Y) ≫
            pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) (n + 1)) ≫
            _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
              ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space))) := by
  rw [kanAdjointStageDifferenceSquare_right]
  exact kanAdjointTracedUnitStageSquare_finish X Y φ n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
