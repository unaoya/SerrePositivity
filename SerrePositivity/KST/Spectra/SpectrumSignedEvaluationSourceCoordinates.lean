module

public import SerrePositivity.KST.Spectra.SpectrumSignedEvaluationSourceChoice
public import SerrePositivity.KST.Spectra.SignedLoopComparisonCoordinates
public import SerrePositivity.KST.Spectra.TracedOriginalLoopRawInterval

/-!
概要：選んだ源比較を使う実評価由来の写像を、元の次段評価の同じ座標へ戻す。
方針：raw 評価の厳密な交換公式、一段移動、符号補正、前合成の評価公式を順に適用する。
規約：全 Hom の厳密等式。使われ方：実評価側の構造正方形を指定する際の段射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra
namespace KanSequence

/-- 符号補正の段成分は、元の Kan 円の同じ反転反復への前合成。 -/
lemma signedLoopTailTwistComparison_app (Y : KanSequence.{u}) (n : ℕ) :
    (signedLoopTailTwistComparison Y).app n =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.reversalIterate n) (Y.level (n + 1)).space := by
  change (iterateHom (tailHom (mappingPre (CirclePower.integerPowerMap.{u} (-1)) Y)) n).app n = _
  exact iterateHom_tail_mappingPre_app Y n n

end KanSequence
namespace OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

/-- 元の評価の符号付き一段移動を、元の次段評価と同じ厳密交換で表示する。 -/
lemma signedEvaluationPost_evaluation (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    signedEvaluationPost X Y ≫
      pointedEvaluation (tail (cotensor CirclePower.space.{u} X))
        (KanSequence.signedLoopTail Y.toKanSequence) n =
    pointedEvaluation X Y.toKanSequence (n + 1) ≫
      evaluationPostAt CirclePower.space.{u} X Y (n + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso ((cotensor CirclePower.space.{u} X).level (n + 1)).space
        CirclePower.space.{u} (Y.level (n + 1)).space).inv ≫
      (ihom ((cotensor CirclePower.space.{u} X).level (n + 1)).space).map
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.reversalIterate n) (Y.level (n + 1)).space) := by
  rw [signedEvaluationPost, Category.assoc, Category.assoc, pointedPost_evaluation,
    pointedTail_evaluation_assoc, ← Category.assoc, rawEvaluationPost_evaluation]
  rw [KanSequence.signedLoopTailTwistComparison_app]
  simp only [Category.assoc]
  rfl

/-- 指定した源比較を含む実写像の段射。元の次段評価のパラメータを保つ。 -/
lemma signedEvaluationAt_evaluation (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X)) (n : ℕ) :
    signedEvaluationAt X Y e ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n =
    pointedEvaluation X Y.toKanSequence (n + 1) ≫
      evaluationPostAt CirclePower.space.{u} X Y (n + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso ((cotensor CirclePower.space.{u} X).level (n + 1)).space
        CirclePower.space.{u} (Y.level (n + 1)).space).inv ≫
      (ihom ((cotensor CirclePower.space.{u} X).level (n + 1)).space).map
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.reversalIterate n) (Y.level (n + 1)).space) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (e.app n)
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space) := by
  rw [signedEvaluationAt, Category.assoc, pointedPre_evaluation, ← Category.assoc,
    signedEvaluationPost_evaluation]
  simp only [Category.assoc]
  rfl

/-- 実際の BF 比較族の段射も、射影後は同じ元の評価由来の段射へ厳密に戻る。 -/
lemma signedEvaluationCompatibleAt_projected_evaluation (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X)) (n : ℕ) :
    signedEvaluationCompatibleAt X Y e ≫ pointedPost X (signedLoopProjection Y) ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n =
    sourceMap CirclePower.space.{u} X Y ≫ (signedEvaluationAt X Y e ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) := by
  rw [← Category.assoc, signedEvaluationCompatibleAt_projection, Category.assoc]

end OmegaSpectrum.CotensorCompatible
end SerrePositivity.KST.Spectra
