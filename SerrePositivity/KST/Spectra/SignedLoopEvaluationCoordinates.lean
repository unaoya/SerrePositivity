module

public import SerrePositivity.KST.Spectra.SignedLoopComparisonCoordinates
public import SerrePositivity.KST.Spectra.SpectrumEvaluationPostCoordinates
public import SerrePositivity.KST.Spectra.SpectrumCotensorParameterNaturality

/-!
概要：符号付き loop 比較を、元の BF cotensor の評価と evaluationPost の段座標へ照合する。
方針：同じ比較の通常円制限を転置し、補正済みパラメータへの前合成として表示する。
規約：全列ホモトピーや evaluationPost の同値性は未主張。
使われ方：HA §1.4.2。元の全 Hom 比較を保つ符号補正の解析。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の raw 比較の評価は、同じ普遍評価を補正済みの円パラメータへ制限したもの。 -/
lemma signedLoopRawComparison_evaluation (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.transpose ((signedLoopRawComparison X).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space) =
    CirclePower.signedEvaluationParameter n ≫
      CotensorCompatible.evaluationAt CirclePower.space.{u} X (n + 1) := by
  rw [signedLoopRawComparison_restriction, PointedMapping.transpose_pre_inner]
  rfl

/-- 同じ符号付き評価を、元の通常円の普遍評価と実際の BF 制限射で表示する。 -/
lemma signedLoopRawComparison_ordinaryEvaluation (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.transpose ((signedLoopRawComparison X).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space) =
    CotensorCompatible.evaluationAt PointedSimplicialSet.circle.{u} X (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        ((cotensorPre (CirclePower.signedEvaluationParameter n) X).app (n + 1))
        (X.level (n + 1)).space := by
  rw [signedLoopRawComparison_evaluation]
  exact (cotensorEvaluationAt_parameter (CirclePower.signedEvaluationParameter n) X (n + 1)).symm

namespace CotensorCompatible

/-- 補正済み比較の評価への後合成を、元の全段 Hom パラメータについて curry する。 -/
def signedLoopEvaluationPostAt (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedObject.basedHom (X.level (n + 1)).space (Y.level (n + 1)).space ⟶
      (ihom PointedSimplicialSet.circle.{u}).obj
        (PointedObject.basedHom ((cotensor CirclePower.space.{u} X).level (n + 1)).space
          (Y.level (n + 1)).space) :=
  curry (PointedMapping.transpose ((signedLoopRawComparison X).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space) ▷
        PointedObject.basedHom (X.level (n + 1)).space (Y.level (n + 1)).space ≫
    MonoidalClosed.comp ((cotensor CirclePower.space.{u} X).level (n + 1)).space
      (X.level (n + 1)).space (Y.level (n + 1)).space)

/-- 元の evaluationPost の同じ段座標を、同じ補正済みパラメータに制限した厳密な式。 -/
lemma signedLoopEvaluationPostAt_eq (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    signedLoopEvaluationPostAt X Y n =
      evaluationPostAt CirclePower.space.{u} X Y (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter n)
          (PointedObject.basedHom ((cotensor CirclePower.space.{u} X).level (n + 1)).space
            (Y.level (n + 1)).space) := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, uncurry_pre_app]
  simp only [signedLoopEvaluationPostAt, evaluationPostAt, uncurry_curry]
  rw [signedLoopRawComparison_evaluation, comp_whiskerRight, Category.assoc]

/-- 元の evaluationPost 全体への同じ後合成は、補正済み比較の段評価と厳密に一致する。 -/
lemma evaluationPost_signedLoop_evaluation (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (evaluationPost CirclePower.space.{u} X Y ≫ (ihom CirclePower.space.{u}).map
      (RawSpectrumMapping.pointedEvaluation (cotensor CirclePower.space.{u} X)
        Y.toKanSequence (n + 1))) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter n)
        (PointedObject.basedHom ((cotensor CirclePower.space.{u} X).level (n + 1)).space
          (Y.level (n + 1)).space) =
    RawSpectrumMapping.pointedEvaluation X Y.toKanSequence (n + 1) ≫
      signedLoopEvaluationPostAt X Y n := by
  rw [evaluationPost_evaluation, signedLoopEvaluationPostAt_eq, Category.assoc]

/-- 元の通常円の evaluationPost 自身から、同じ BF 制限を経て符号付き段評価を回収する。
補正パラメータは n に依存するので、この式だけでは全列のホモトピーを主張しない。 -/
lemma evaluationPost_circle_signedLoop_evaluation (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (evaluationPost PointedSimplicialSet.circle.{u} X Y ≫
      (ihom PointedSimplicialSet.circle.{u}).map
        (RawSpectrumMapping.pointedPre
          (cotensorPre (CirclePower.signedEvaluationParameter n) X) Y.toKanSequence)) ≫
      (ihom PointedSimplicialSet.circle.{u}).map
        (RawSpectrumMapping.pointedEvaluation (cotensor CirclePower.space.{u} X)
          Y.toKanSequence (n + 1)) =
    RawSpectrumMapping.pointedEvaluation X Y.toKanSequence (n + 1) ≫
      signedLoopEvaluationPostAt X Y n := by
  rw [evaluationPost_parameter]
  have hn := (MonoidalClosed.pre (CirclePower.signedEvaluationParameter.{u} n)).naturality
    (RawSpectrumMapping.pointedEvaluation (cotensor CirclePower.space.{u} X)
      Y.toKanSequence (n + 1))
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  rw [Category.assoc, ← hn, ← Category.assoc]
  exact evaluationPost_signedLoop_evaluation X Y n

end CotensorCompatible
end SerrePositivity.KST.Spectra.OmegaSpectrum
