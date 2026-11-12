module

public import SerrePositivity.KST.Spectra.SpectrumTracedActualRightDifferenceTriangles
public import SerrePositivity.KST.Spectra.SpecifiedSquareCodifference
public import SerrePositivity.KST.Spectra.PointedConstantIntervalSquare

/-!
概要：実評価と源単位の同じ段比較三角形を保ち、右側差の実構造正方形を構成する。
方針：厳密な実評価正方形と源単位正方形を共通終辺の上で相対比較する。
規約：上下の三角形・源の非定数辺を保持。使われ方：元の自然性区間との次の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ RawSpectrumMapping.pointedSpace X Y.toKanSequence)

local instance rightDifferenceSquareTargetKan (n : ℕ) : KanComplex
    (PointedObject.basedHom A (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 全 Hom 由来の同じ実評価区間は、構造方向に一定な正方形を持つ。 -/
def tracedActualEvaluationStructureSquare (n : ℕ) :
    SSet.Homotopy
      (((tracedActualStageEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path)
      (((tracedActualStageEvaluationInterval X Y φ n).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path) where
  h := ((tracedActualStageEvaluationInterval X Y φ n).basedPost
    (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).constantSquare.h
  h₀ := (((tracedActualStageEvaluationInterval X Y φ n).basedPost
    (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).constantSquare.h₀).trans
      (tracedActualStageEvaluationInterval_condition X Y φ n).symm
  h₁ := ((tracedActualStageEvaluationInterval X Y φ n).basedPost
    (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).constantSquare.h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 第一の回転正方形の終辺は、厳密な源単位族の同じ構造頂点。 -/
lemma tracedActualEvaluationStructureSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (tracedActualEvaluationStructureSquare X Y φ n).h =
      SSet.const (PointedMapping.familyVertex ((φ ≫ tracedSourceUnitAction X Y n) ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)) :=
  ((tracedActualStageEvaluationInterval X Y φ n).basedPost
    (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).constantSquare_finish

/-- 実評価正方形を、同じ終辺へ至る左右方向の実ホモトピーとして読む。 -/
def tracedActualRightDifferenceFirst (n : ℕ) :
    SSet.Homotopy
      (SquareAdjustment.leftSide ≫ (tracedActualEvaluationStructureSquare X Y φ n).h)
      (SSet.const (PointedMapping.familyVertex ((φ ≫ tracedSourceUnitAction X Y n) ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n))) where
  h := (SquareAdjustment.flip (tracedActualEvaluationStructureSquare X Y φ n)).h
  h₀ := (SquareAdjustment.flip (tracedActualEvaluationStructureSquare X Y φ n)).h₀
  h₁ := (SquareAdjustment.flip (tracedActualEvaluationStructureSquare X Y φ n)).h₁.trans
    (tracedActualEvaluationStructureSquare_finish X Y φ n)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 源単位正方形も、同じ終辺へ至る左右方向の実ホモトピーとして読む。 -/
def tracedActualRightDifferenceSecond (n : ℕ) :
    SSet.Homotopy
      (SquareAdjustment.leftSide ≫ (tracedSourceUnitEvaluationSquare X Y φ n).h)
      (SSet.const (PointedMapping.familyVertex ((φ ≫ tracedSourceUnitAction X Y n) ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n))) where
  h := (SquareAdjustment.flip (tracedSourceUnitEvaluationSquare X Y φ n)).h
  h₀ := (SquareAdjustment.flip (tracedSourceUnitEvaluationSquare X Y φ n)).h₀
  h₁ := (SquareAdjustment.flip (tracedSourceUnitEvaluationSquare X Y φ n)).h₁.trans
    (tracedSourceUnitEvaluationSquare_finish X Y φ n)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 上下の元の段差三角形を指定した、共通終辺の相対ホーン充填。 -/
def tracedActualRightDifferenceSquareData (n : ℕ) :=
  SquareAdjustment.SpecifiedCodifference.choose
    (tracedActualRightDifferenceFirst X Y φ n) (tracedActualRightDifferenceSecond X Y φ n)
    (tracedActualRightDifferenceSourceTriangle X Y φ n)
    (tracedActualRightDifferenceTargetTriangle X Y φ n)
    (((SquareAdjustment.leftSide_swap _).trans
      (tracedActualEvaluationStructureSquare X Y φ n).h₀).trans
        (tracedActualRightDifferenceSourceTriangle_one X Y φ n).symm)
    (((SquareAdjustment.rightSide_swap _).trans
      (tracedActualEvaluationStructureSquare X Y φ n).h₁).trans
        (tracedActualRightDifferenceTargetTriangle_one X Y φ n).symm)
    (((SquareAdjustment.leftSide_swap _).trans
      (tracedSourceUnitEvaluationSquare X Y φ n).h₀).trans
        (tracedActualRightDifferenceSourceTriangle_zero X Y φ n).symm)
    (((SquareAdjustment.rightSide_swap _).trans
      (tracedSourceUnitEvaluationSquare X Y φ n).h₁).trans
        (tracedActualRightDifferenceTargetTriangle_zero X Y φ n).symm)

/-- 同じ右側段差の次段の源制限と前段の構造像を結ぶ実正方形。 -/
def tracedActualRightDifferenceSquare (n : ℕ) :
    SSet.Homotopy
      ((((tracedActualStageRightDifference X Y φ (n + 1)).path).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path)
      ((((tracedActualStageRightDifference X Y φ n).path).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path) where
  h := (SquareAdjustment.SpecifiedCodifference.squareHomotopy _ _ _ _
    (tracedActualRightDifferenceSquareData X Y φ n)).h
  h₀ := (SquareAdjustment.SpecifiedCodifference.squareHomotopy _ _ _ _
    (tracedActualRightDifferenceSquareData X Y φ n)).h₀.trans
      (tracedActualRightDifferenceSourceTriangle_two X Y φ n)
  h₁ := (SquareAdjustment.SpecifiedCodifference.squareHomotopy _ _ _ _
    (tracedActualRightDifferenceSquareData X Y φ n)).h₁.trans
      (tracedActualRightDifferenceTargetTriangle_two X Y φ n)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 同じ段差正方形の左辺全体は、厳密な実評価の構造頂点で一定。 -/
lemma tracedActualRightDifferenceSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (tracedActualRightDifferenceSquare X Y φ n).h =
      SSet.const (PointedMapping.familyVertex
        ((φ ≫ (signedEvaluationAt X Y (tracedOriginalLoopModelMap X) ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)) ≫
            pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)) := by
  have h := SquareAdjustment.SpecifiedCodifference.square_left _ _ _ _
    (tracedActualRightDifferenceSquareData X Y φ n)
  exact h.trans (((tracedActualStageEvaluationInterval X Y φ n).basedPost
    (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).constantSquare_start)

/-- 同じ段差正方形の右辺全体は、元の源単位の非定数構造入力そのもの。 -/
lemma tracedActualRightDifferenceSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (tracedActualRightDifferenceSquare X Y φ n).h =
      ((OmegaSpectrum.signedLoopUnitStructurePath X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path :=
  (SquareAdjustment.SpecifiedCodifference.square_right _ _ _ _
    (tracedActualRightDifferenceSquareData X Y φ n)).trans
      (tracedSourceUnitEvaluationSquare_start X Y φ n)

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
