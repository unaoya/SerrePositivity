module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceEvaluationInterval
public import SerrePositivity.KST.Spectra.PointedBasedPathCodifference

/-!
概要：実評価側から標的のトレース付き単位へ至る段区間と、元の辺を保持する三角形を作る。
方針：同じ終点の二組を外ホーンで比較し、標的単位の既存区間と合成する。
規約：段区間だけから全 Hom ホモトピーを推論しない。使われ方：構造正方形の指定境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

local instance sourceDifferenceTargetKan (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    KanComplex (kanAdjointParameterTarget X Y n).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 同じ源単位へ至る二辺を保持し、実評価から Kan 随伴の右側への辺を選ぶ。 -/
def tracedSourceEvaluationRightDifference (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.BasedPathCodifference (tracedSourceEvaluationInterval X Y n)
      (kanAdjointTracedSourceEvaluationInterval X Y n) :=
  PointedMapping.BasedPathCodifference.choose (tracedSourceEvaluationInterval X Y n)
    (kanAdjointTracedSourceEvaluationInterval X Y n)

/-- 保存済みの全パラメータ自然性区間を、同じ元の辺を持つ点つき区間として使う。 -/
def kanAdjointSourceNaturalityInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (kanAdjointParameterLeft X Y n) (kanAdjointParameterRight X Y n) :=
  PointedMapping.VerticalPath.ofHomotopy (kanAdjointParameterHomotopy X Y n)
    (kanAdjointParameterHomotopy_base X Y n) (toUnit_unique _ _)

/-- 同じ右側座標へ至る二辺を保持し、実評価から標的 Kan 随伴への辺を選ぶ。 -/
def tracedSourceEvaluationLeftDifference (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.BasedPathCodifference (tracedSourceEvaluationRightDifference X Y n).path
      (kanAdjointSourceNaturalityInterval X Y n) :=
  PointedMapping.BasedPathCodifference.choose (tracedSourceEvaluationRightDifference X Y n).path
    (kanAdjointSourceNaturalityInterval X Y n)

/-- 標的単位の元の段区間を恒等パラメータで使い、厳密な終点族を表示する。 -/
def tracedTargetUnitEvaluationInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (kanAdjointParameterLeft X Y n)
      ((pointedPost X (sequenceHom (tracedSignedLoopUnit Y)) ≫
        pointedPost X (signedLoopProjection Y)) ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) := by
  let P := kanAdjointTracedUnitEvaluationInterval X Y
    (𝟙 (RawSpectrumMapping.pointedSpace X Y.toKanSequence)) n
  exact P.changeEndpoints (Category.id_comp _).symm
    (by simp only [Category.id_comp, Category.assoc])

/-- 実評価から元の標的単位へ至る段区間と、選んだ二辺を持つ実合成三角形。 -/
def tracedEvaluationTargetStageComposite (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.BasedPathComposite (tracedSourceEvaluationLeftDifference X Y n).path
      (tracedTargetUnitEvaluationInterval X Y n) :=
  PointedMapping.BasedPathComposite.choose (tracedSourceEvaluationLeftDifference X Y n).path
    (tracedTargetUnitEvaluationInterval X Y n)

/-- 二つの厳密な全 Hom 写像の実際の段評価を結ぶ区間。構造正方形は後続工程。 -/
def tracedEvaluationTargetStageInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (signedEvaluationAt X Y (tracedOriginalLoopModelMap X) ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)
      ((pointedPost X (sequenceHom (tracedSignedLoopUnit Y)) ≫
        pointedPost X (signedLoopProjection Y)) ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) :=
  (tracedEvaluationTargetStageComposite X Y n).path

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
