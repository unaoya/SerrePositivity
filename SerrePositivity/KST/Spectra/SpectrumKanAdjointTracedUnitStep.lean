module

public import SerrePositivity.KST.Spectra.PointedIhomStepInterval
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitTriangle

/-!
概要：単位の同じ構造三角形の第二辺を、実際の前段評価区間の構造像へ同定する。
方針：内部 Hom の作用と懸垂・標的後合成を全区間で交換する。
規約：区間や二単体を選び直さない。使われ方：共有辺を持つ実構造正方形の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 保持した第二辺は、同じ単位比較区間の懸垂・構造像そのもの。 -/
lemma OmegaSpectrum.tracedSignedLoopUnitStepInterval_path (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (Y.tracedSignedLoopUnitStepInterval n).path =
      ((Y.tracedSignedLoopUnitComparison n).suspension.forgetProjection.basedPost
        ((KanSequence.signedLoopTail Y.toKanSequence).sigma n)).path := by
  unfold OmegaSpectrum.tracedSignedLoopUnitComparison OmegaSpectrum.tracedRectifyIntoComparison
  rw [PointedMapping.VerticalPath.changeEndpoints_step_path]
  rfl

namespace RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 第二辺は前段の全 Hom 評価区間を同じ構造射で移した実区間そのもの。 -/
lemma kanAdjointTracedUnitParameterTriangle_zero_evaluation (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointTracedUnitParameterTriangle X Y φ n =
      ((kanAdjointTracedUnitEvaluationInterval X Y φ n).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  rw [kanAdjointTracedUnitParameterTriangle_zero]
  have h := PointedMapping.VerticalPath.basedIhomMap_step_path
    (OmegaSpectrum.tracedSignedLoopUnitComparison Y n)
    (φ ≫ pointedEvaluation X Y.toKanSequence n)
    ((KanSequence.signedLoopTail Y.toKanSequence).sigma n)
  rw [PointedMapping.VerticalPath.basedIhomMap_pre_path,
    ← OmegaSpectrum.tracedSignedLoopUnitStepInterval_path] at h
  change _ = ((PointedMapping.VerticalPath.basedIhomMap (X.level n).space
    (OmegaSpectrum.tracedSignedLoopUnitComparison Y n)).pre
      (φ ≫ pointedEvaluation X Y.toKanSequence n)).path ≫
    (PointedObject.basedHomMap A
      (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).right at h
  change _ = (kanAdjointTracedUnitEvaluationInterval X Y φ n).path ≫
    (PointedObject.basedHomMap A
      (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).right
  rw [kanAdjointTracedUnitEvaluationInterval_path]
  simp only [Category.assoc] at h
  change (OmegaSpectrum.tracedSignedLoopUnitStepInterval Y n).path ≫
    (kanAdjointTracedUnitStructureAction X Y φ n).right = _ at h
  exact h

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
