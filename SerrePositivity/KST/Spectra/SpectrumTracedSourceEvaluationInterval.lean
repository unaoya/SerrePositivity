module

public import SerrePositivity.KST.Spectra.SpectrumEvaluationPostAction
public import SerrePositivity.KST.Spectra.TracedOriginalLoopSourceInterval

/-!
概要：実評価側と Kan 随伴側から、同じトレース付き源単位への段比較区間を構成する。
方針：同じ源区間を前合成へ移し、内部 Hom の作用と元の次段評価へ前合成する。
規約：区間の選択をやり直さない。使われ方：実評価と既存比較の構造正方形の指定辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

/-- 次段の元の全 Hom を、トレース付き源単位の射影へ作用させた段写像。 -/
def tracedSourceUnitAction (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶ kanAdjointParameterTarget X Y n :=
  pointedEvaluation X Y.toKanSequence (n + 1) ≫
    PointedMapping.ihomAction CirclePower.space.{u}
      (X.level (n + 1)).space (Y.level (n + 1)).space ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n)
      (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space)

/-- 実際の元の評価から、同じトレース付き源単位を通る段写像への実区間。 -/
def tracedSourceEvaluationInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (signedEvaluationAt X Y (tracedOriginalLoopModelMap X) ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)
      (tracedSourceUnitAction X Y n) := by
  let P := PointedMapping.VerticalPath.basedPreAction
    (tracedOriginalLoopRawComparison_level_interval X n)
    (PointedMapping.ihomAction CirclePower.space.{u}
      (X.level (n + 1)).space (Y.level (n + 1)).space)
    (pointedEvaluation X Y.toKanSequence (n + 1))
  have hs : signedEvaluationAt X Y (tracedOriginalLoopModelMap X) ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n =
      pointedEvaluation X Y.toKanSequence (n + 1) ≫
        (PointedMapping.ihomAction CirclePower.space.{u}
          (X.level (n + 1)).space (Y.level (n + 1)).space ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((tracedOriginalLoopRawComparison X).app n)
          (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space)) := by
    rw [signedEvaluationAt_action]
    rfl
  exact P.changeEndpoints hs rfl

/-- 同じ源単位の元の比較区間は、既存の Kan 随伴の右側座標から同じ段写像へ至る。 -/
def kanAdjointTracedSourceEvaluationInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (kanAdjointParameterRight X Y n) (tracedSourceUnitAction X Y n) := by
  let P := PointedMapping.VerticalPath.basedPreAction
    (tracedSignedLoopUnitComparison X n)
    (PointedMapping.ihomAction CirclePower.space.{u}
      (X.level (n + 1)).space (Y.level (n + 1)).space)
    (pointedEvaluation X Y.toKanSequence (n + 1))
  have hs : kanAdjointParameterRight X Y n =
      pointedEvaluation X Y.toKanSequence (n + 1) ≫
        (PointedMapping.ihomAction CirclePower.space.{u}
          (X.level (n + 1)).space (Y.level (n + 1)).space ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (KanSequence.kanAdjoint X.toKanSequence n)
          (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space)) := by
    rw [PointedMapping.ihomParameterAction_eq_adjoint_pre]
    rfl
  exact P.changeEndpoints hs rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
