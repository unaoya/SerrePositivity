module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
/-!
概要：右ファイブレーションに沿う left cofinal 写像の基底変換も left cofinal。
方針：反転後の左ファイブレーションの既存定理を、引き戻し保存の厳密同型で戻す。
規約：単射性も quasicategory 性も追加しない。使われ方：実屋根比較の商側三角形への基底変換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
/-- 右ファイブレーションに沿う実 left cofinal 写像の引き戻しは left cofinal。 -/
lemma rightFibration_pullback_isLeftCofinal {E A B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (pullback.fst p f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_isRightCofinal_op _).mpr
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_isRightCofinal (SSet.opFunctor.map p)
    (SSet.opFunctor.map f) hf.op
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let e := PreservesPullback.iso SSet.opFunctor p f
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne e.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.of_isIso e.hom)
  have hc := he.comp h
  dsimp only [e] at hc
  rw [PreservesPullback.iso_hom_fst] at hc
  exact hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories
