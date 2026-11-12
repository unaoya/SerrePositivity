module

public import SerrePositivity.KST.Spectra.SpectrumTracedActualStageDifference
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitEvaluationSquare

/-!
概要：実評価と源単位比較の同じ段三角形を、次段の源制限と前段の構造像へ移す。
方針：元の三角形全体へ同じ内部 Hom 射を後合成する。
規約：六つの面を実辺全体として保持。使われ方：共通終辺の正方形の相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ RawSpectrumMapping.pointedSpace X Y.toKanSequence)

/-- 次段の元の比較三角形を、元の源構造射への制限へ写した同じ二単体。 -/
def tracedActualRightDifferenceSourceTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (tracedActualStageRightDifference X Y φ (n + 1)).triangle.simplex ≫
    (PointedObject.basedHomMap A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).right

/-- 前段の元の比較三角形を、同じ構造像へ写した二単体。 -/
def tracedActualRightDifferenceTargetTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (tracedActualStageRightDifference X Y φ n).triangle.simplex ≫
    (PointedObject.basedHomMap A
      (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).right

/-- 次段三角形の対角辺は、元の実評価区間の源制限そのもの。 -/
lemma tracedActualRightDifferenceSourceTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ tracedActualRightDifferenceSourceTriangle X Y φ n =
      ((tracedActualStageEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
  rw [tracedActualRightDifferenceSourceTriangle, ← Category.assoc,
    PointedMapping.BasedPathCodifference.triangle_one]
  rfl

/-- 次段三角形の第二辺は、同じ源単位評価区間の源制限そのもの。 -/
lemma tracedActualRightDifferenceSourceTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ tracedActualRightDifferenceSourceTriangle X Y φ n =
      (((kanAdjointTracedSourceEvaluationInterval X Y (n + 1)).pre φ).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
  rw [tracedActualRightDifferenceSourceTriangle, ← Category.assoc,
    PointedMapping.BasedPathCodifference.triangle_zero]
  rfl

/-- 次段三角形の第一辺も、同じ段差の源制限の実辺を保持する。 -/
lemma tracedActualRightDifferenceSourceTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ tracedActualRightDifferenceSourceTriangle X Y φ n =
      (((tracedActualStageRightDifference X Y φ (n + 1)).path).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
  rw [tracedActualRightDifferenceSourceTriangle, ← Category.assoc,
    PointedMapping.BasedPathCodifference.triangle_two]
  rfl

/-- 前段三角形の対角辺は、元の実評価区間の構造像。 -/
lemma tracedActualRightDifferenceTargetTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ tracedActualRightDifferenceTargetTriangle X Y φ n =
      ((tracedActualStageEvaluationInterval X Y φ n).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  rw [tracedActualRightDifferenceTargetTriangle, ← Category.assoc,
    PointedMapping.BasedPathCodifference.triangle_one]
  rfl

/-- 前段三角形の第二辺も、同じ源単位評価区間の構造像。 -/
lemma tracedActualRightDifferenceTargetTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ tracedActualRightDifferenceTargetTriangle X Y φ n =
      (((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  rw [tracedActualRightDifferenceTargetTriangle, ← Category.assoc,
    PointedMapping.BasedPathCodifference.triangle_zero]
  rfl

/-- 前段三角形の第一辺も、同じ段差の構造像の実辺を保持する。 -/
lemma tracedActualRightDifferenceTargetTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ tracedActualRightDifferenceTargetTriangle X Y φ n =
      (((tracedActualStageRightDifference X Y φ n).path).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  rw [tracedActualRightDifferenceTargetTriangle, ← Category.assoc,
    PointedMapping.BasedPathCodifference.triangle_two]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
