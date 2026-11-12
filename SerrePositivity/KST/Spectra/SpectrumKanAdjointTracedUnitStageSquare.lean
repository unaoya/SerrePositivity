module

public import SerrePositivity.KST.Spectra.PointedSpectrumIntervalTranspose
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitEvaluationSquare

/-!
概要：単位の同じ実正方形を、段射区間の源制限と構造像の比較へ戻す。
方針：第二辺の同定と全区間の転置の交換則を使う。
規約：非定数の共有辺を保持。使われ方：二つの厳密な列射の相対構造比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ単位正方形は、段射区間の源制限と構造像の実ホモトピーを与える。 -/
def kanAdjointTracedUnitStageSquare (n : ℕ) :
    SSet.Homotopy
      (((kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).basedTranspose.pre
        (X.sigma n)).path)
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointTracedUnitEvaluationInterval X Y φ n).basedTranspose.suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path)
    where
  h := (kanAdjointTracedUnitStructureSquare X Y φ n).h
  h₀ := by
    rw [(kanAdjointTracedUnitStructureSquare X Y φ n).h₀]
    exact basedTranspose_restriction_path (X.sigma n)
      (kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1))
  h₁ := by
    rw [(kanAdjointTracedUnitStructureSquare X Y φ n).h₁]
    have h := (kanAdjointTracedUnitParameterTriangle_zero X Y φ n).symm.trans
      (kanAdjointTracedUnitParameterTriangle_zero_evaluation X Y φ n)
    rw [h]
    exact basedTranspose_step_path X (KanSequence.signedLoopTail Y.toKanSequence) n
      (kanAdjointTracedUnitEvaluationInterval X Y φ n)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 段射区間の表示でも、共有する元の構造辺を全体として保持する。 -/
lemma kanAdjointTracedUnitStageSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointTracedUnitStageSquare X Y φ n).h =
      (kanAdjointTracedStructureInterval X Y φ n).path :=
  kanAdjointTracedUnitStructureSquare_start X Y φ n

/-- 段射表示の終点境界も、同じ厳密な単位構造頂点で全区間が一定。 -/
lemma kanAdjointTracedUnitStageSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointTracedUnitStageSquare X Y φ n).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right.app _
        (PointedMapping.familyVertex
          ((φ ≫ pointedPost X
              (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
            pointedPost X (OmegaSpectrum.signedLoopProjection Y) ≫
            pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) (n + 1)) ≫
            _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
              ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space))) :=
  kanAdjointTracedUnitStructureSquare_finish X Y φ n

/-- 既存の相対正方形と、同じ非定数構造辺を厳密に共有する。 -/
lemma kanAdjointTracedUnitStageSquare_shared_start
    {B : PointedSimplicialSet.{u}} (j : B ⟶ A) [Mono j.right] (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointTracedUnitStageSquare X Y φ n).h =
      SquareAdjustment.leftSide ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h :=
  kanAdjointTracedUnitStructureSquare_shared_start X Y φ j n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
