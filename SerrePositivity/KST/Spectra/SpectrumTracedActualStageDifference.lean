module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceEvaluationHomotopy
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceEvaluationDifference

/-!
概要：元の実評価から得た全 Hom 区間を最初の辺に使う、指定三角形付き段比較。
方針：全 Hom 区間の段評価を元の座標へそろえ、同じ終点の相対外ホーンを充填する。
規約：旧段比較との辺の一致は仮定しない。使われ方：残る比較正方形の指定境界。
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

local instance actualStageTargetKan (n : ℕ) : KanComplex (kanAdjointParameterTarget X Y n).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 同じ全 Hom 区間の段評価を、元の次段座標の二端点で表示する。 -/
def tracedActualStageEvaluationInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (φ ≫ (signedEvaluationAt X Y (tracedOriginalLoopModelMap X) ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n))
      (φ ≫ tracedSourceUnitAction X Y n) :=
  (tracedActualSourceStageInterval X Y φ n).changeEndpoints
    (Category.assoc _ _ _).symm (tracedSourceUnitFamily_evaluation X Y φ n).symm

/-- 端点表示を変えても、元の全 Hom 区間の段評価の同じ辺を保つ。 -/
lemma tracedActualStageEvaluationInterval_path (n : ℕ) :
    (tracedActualStageEvaluationInterval X Y φ n).path =
      (tracedActualSourceStageInterval X Y φ n).path := rfl

/-- 新しい始辺は全 Hom 区間の評価なので、構造経路は辺全体で厳密一致する。 -/
lemma tracedActualStageEvaluationInterval_condition (n : ℕ) :
    ((tracedActualStageEvaluationInterval X Y φ (n + 1)).basedPost
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path =
    ((tracedActualStageEvaluationInterval X Y φ n).basedPost
      (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  change (tracedActualStageEvaluationInterval X Y φ (n + 1)).path ≫
      (PointedObject.basedHomMap A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).right =
    (tracedActualStageEvaluationInterval X Y φ n).path ≫
      (PointedObject.basedHomMap A
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).right
  rw [tracedActualStageEvaluationInterval_path, tracedActualStageEvaluationInterval_path]
  exact tracedActualSourceStageInterval_condition X Y φ n

/-- 元の実評価区間と源単位区間をそのまま保持する、同じ終点での比較三角形。 -/
def tracedActualStageRightDifference (n : ℕ) :
    PointedMapping.BasedPathCodifference (tracedActualStageEvaluationInterval X Y φ n)
      ((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ) :=
  PointedMapping.BasedPathCodifference.choose (tracedActualStageEvaluationInterval X Y φ n)
    ((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ)

/-- 元の自然性の辺も指定したまま、実評価から標的 Kan 随伴への比較辺を選ぶ。 -/
def tracedActualStageLeftDifference (n : ℕ) :
    PointedMapping.BasedPathCodifference (tracedActualStageRightDifference X Y φ n).path
      ((kanAdjointSourceNaturalityInterval X Y n).pre φ) :=
  PointedMapping.BasedPathCodifference.choose (tracedActualStageRightDifference X Y φ n).path
    ((kanAdjointSourceNaturalityInterval X Y n).pre φ)

/-- 標的の既存の単位区間を、元の厳密な全 Hom 終点族で表示する。 -/
def tracedActualTargetUnitStageInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (φ ≫ kanAdjointParameterLeft X Y n)
      (kanAdjointTracedUnitFamily X Y φ ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) :=
  (kanAdjointTracedUnitEvaluationInterval X Y φ n).changeEndpoints rfl
    (by simp only [kanAdjointTracedUnitFamily, Category.assoc])

/-- 同じ新しい始辺と元の標的単位区間を保持する、実際の合成三角形。 -/
def tracedActualTargetStageComposite (n : ℕ) :
    PointedMapping.BasedPathComposite (tracedActualStageLeftDifference X Y φ n).path
      (tracedActualTargetUnitStageInterval X Y φ n) :=
  PointedMapping.BasedPathComposite.choose (tracedActualStageLeftDifference X Y φ n).path
    (tracedActualTargetUnitStageInterval X Y φ n)

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
