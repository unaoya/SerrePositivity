module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitStageInterval

/-!
概要：既存の相対比較と単位比較の段区間を、二つの厳密な列射を終点とする表示へ揃える。
方針：全 Hom の段評価の転置と、端点変更で保持される同じ実区間を使う。
規約：比較区間の選択を変更しない。使われ方：共有構造辺の相対外ホーン充填。
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

/-- 相対比較の同じ段区間を、元の厳密な相対列射を終点として表示する。 -/
def kanAdjointRelativeTracedStrictStageInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level n).space)
      (kanAdjointParameterStage X Y φ n)
      ((kanAdjointRelativeTracedParameterHom X Y φ j).app n) := by
  refine (kanAdjointRelativeTracedStageEvaluationInterval X Y φ j n).changeEndpoints rfl ?_
  have h := congrArg PointedMapping.transpose (parameterFamily_evaluation X
    (KanSequence.signedLoopTail Y.toKanSequence) A
    (kanAdjointRelativeTracedParameterHom X Y φ j) n)
  rw [PointedMapping.transpose_transpose] at h
  exact h.symm

/-- 厳密な列射への端点表示を変えても、元の相対段区間を全体で保持。 -/
lemma kanAdjointRelativeTracedStrictStageInterval_path (n : ℕ) :
    (kanAdjointRelativeTracedStrictStageInterval X Y φ j n).path =
      (kanAdjointRelativeTracedStageEvaluationInterval X Y φ j n).path := rfl

/-- 相対段区間の構造像も、同じ実区間を厳密に保持する。 -/
lemma kanAdjointRelativeTracedStrictStageInterval_step_path (n : ℕ) :
    (PointedMapping.VerticalPath.basedPost
      (kanAdjointRelativeTracedStrictStageInterval X Y φ j n).suspension.forgetProjection
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path =
    (PointedMapping.VerticalPath.basedPost
      (kanAdjointRelativeTracedStageEvaluationInterval X Y φ j n).suspension.forgetProjection
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path := by
  unfold kanAdjointRelativeTracedStrictStageInterval
  exact PointedMapping.VerticalPath.changeEndpoints_step_path _ _ _ _

/-- 単位側の段区間の構造像も、端点表示の変更で元の実区間を変えない。 -/
lemma kanAdjointTracedUnitStageInterval_step_path (n : ℕ) :
    (PointedMapping.VerticalPath.basedPost
      (kanAdjointTracedUnitStageInterval X Y φ n).suspension.forgetProjection
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path =
    (PointedMapping.VerticalPath.basedPost
      (kanAdjointTracedUnitEvaluationInterval X Y φ n).basedTranspose.suspension.forgetProjection
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path := by
  unfold kanAdjointTracedUnitStageInterval
  exact PointedMapping.VerticalPath.changeEndpoints_step_path _ _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
