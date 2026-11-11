module

public import SerrePositivity.KST.Spectra.SignedLoopComparisonCoordinates

/-!
概要：段数に依存する円の符号補正の厳密な漸化式。
方針：同じ反転の反復を結合則で移し、通常円からのパラメータに合成する。
規約：反転の二回合成の厳密な対合性は要求しない。
使われ方：元の符号付き比較の構造正方形の通常円への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.CirclePower

/-- 実際の反転の反復は、同じ反転を右端に一回増やしても同じ射。 -/
lemma reversalIterate_succ_right (n : ℕ) :
    reversalIterate.{u} (n + 1) = reversalIterate n ≫ integerPowerMap.{u} (-1) := by
  induction n with
  | zero => simp only [reversalIterate, Category.comp_id, Category.id_comp]
  | succ n ih =>
    change integerPowerMap.{u} (-1) ≫ reversalIterate (n + 1) =
      (integerPowerMap.{u} (-1) ≫ reversalIterate n) ≫ integerPowerMap.{u} (-1)
    rw [ih, Category.assoc]

/-- 次段の補正済みパラメータは、同じ前段のパラメータの後の一回の反転。 -/
lemma signedEvaluationParameter_succ (n : ℕ) :
    signedEvaluationParameter.{u} (n + 1) =
      signedEvaluationParameter n ≫ integerPowerMap.{u} (-1) := by
  rw [signedEvaluationParameter, reversalIterate_succ_right]
  rfl

/-- 同じ補正の漸化式を、任意の標的の実際の内部 Hom の制限へ移す。 -/
lemma signedEvaluationParameter_pre_succ (V : PointedSimplicialSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (reversalIterate n) V ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (unit.{u} ≫ integerPowerMap.{u} (-1)) V =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (signedEvaluationParameter (n + 1)) V := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, signedEvaluationParameter, reversalIterate,
    ← Category.assoc]

end SerrePositivity.KST.Spectra.CirclePower
