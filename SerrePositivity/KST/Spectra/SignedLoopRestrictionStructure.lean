module

public import SerrePositivity.KST.Spectra.SignedLoopParameterRecurrence

/-!
概要：元の符号付き loop 比較の構造可換式を、補正済みパラメータの通常円評価へ移す。
方針：符号付き構造射の源制限を計算し、同じ raw 比較の構造正方形を後合成する。
規約：前段の評価では次段の補正パラメータを用いる。段に依存しない比較とは主張しない。
使われ方：HA §1.4.2。元の全列比較の構造境界に残る符号の特定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra
namespace KanSequence

/-- 符号付き構造の源制限では、同じパラメータに一回の反転を合成する。 -/
lemma signedLoopTail_restriction (X : KanSequence.{u})
    {A : PointedSimplicialSet.{u}} (i : A ⟶ CirclePower.space.{u}) (n : ℕ) :
    (signedLoopTail X).sigma n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level (n + 2)).space =
    PointedSimplicialSet.circle.{u} ◁
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (i ≫ CirclePower.integerPowerMap.{u} (-1))
        (X.level (n + 1)).space ≫
      (mapping A X).sigma (n + 1) := by
  change ((mapping CirclePower.space.{u} X).sigma (n + 1) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1))
      (X.level (n + 2)).space) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  exact ((mappingPre (i ≫ CirclePower.integerPowerMap.{u} (-1)) X).comm (n + 1)).symm

end KanSequence
namespace OmegaSpectrum

/-- 前段の比較を一回反転した通常円で評価すると、次段の補正パラメータが現れる。 -/
lemma signedLoopRawComparison_restriction_next (X : OmegaSpectrum.{u}) (n : ℕ) :
    (signedLoopRawComparison X).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.unit.{u} ≫ CirclePower.integerPowerMap.{u} (-1))
        (X.level (n + 1)).space =
    (cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter (n + 1))
        (X.level (n + 1)).space := by
  rw [signedLoopRawComparison_app, Category.assoc,
    CirclePower.signedEvaluationParameter_pre_succ]

/-- 同じ raw 比較の構造像を通常円へ制限した側の厳密な座標。 -/
lemma signedLoopRawComparison_circle_step (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedSimplicialSet.circle.{u} ◁ (signedLoopRawComparison X).app n ≫
      (KanSequence.signedLoopTail X.toKanSequence).sigma n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 2)).space =
    PointedSimplicialSet.circle.{u} ◁
      ((cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter (n + 1))
          (X.level (n + 1)).space) ≫
      (KanSequence.mapping PointedSimplicialSet.circle.{u} X.toKanSequence).sigma (n + 1) := by
  have hs := KanSequence.signedLoopTail_restriction X.toKanSequence CirclePower.unit.{u} n
  erw [hs]
  rw [← whiskerLeft_comp_assoc]
  erw [signedLoopRawComparison_restriction_next X n]

/-- 元の同じ構造正方形は、両段に次段の補正パラメータを用いた通常円の正方形となる。 -/
lemma signedLoopRawComparison_circle_square (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedSimplicialSet.circle.{u} ◁
      ((cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter (n + 1))
          (X.level (n + 1)).space) ≫
      (KanSequence.mapping PointedSimplicialSet.circle.{u} X.toKanSequence).sigma (n + 1) =
    (cotensor CirclePower.space.{u} X).sigma (n + 1) ≫
      (cotensorProjection CirclePower.space.{u} X).app (n + 2) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter (n + 1))
        (X.level (n + 2)).space := by
  have hc := congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u}
    (X.level (n + 2)).space) ((signedLoopRawComparison X).comm n)
  simp only [Category.assoc] at hc
  rw [signedLoopRawComparison_circle_step, signedLoopRawComparison_restriction] at hc
  exact hc

end OmegaSpectrum
end SerrePositivity.KST.Spectra
