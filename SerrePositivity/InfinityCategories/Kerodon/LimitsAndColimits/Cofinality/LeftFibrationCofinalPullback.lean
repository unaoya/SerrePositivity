module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationAnodynePullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFactorizationCriterion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：left fibration に沿う right cofinal な射の引き戻しは right cofinal。
方針：right anodyne と trivial Kan の因子分解を引き戻し、合成と pullback の貼合せを使う。
規約：一般の cocartesian fibration の場合はまだ主張しない。
使われ方：Quillen A の必要性と、coslice の引き戻しの比較。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：left fibration に沿う right cofinal な射の引き戻しは right cofinal。
方針：anodyne・trivial Kan 因子分解の各因子を引き戻し、貼合せ同型で元の第一射影へ戻す。
規約：元の cofinal な射に単射性や quasicategory 性を要求しない。
使われ方：Kerodon Proposition 7.2.3.10（Tag 02P6） の left fibration の場合。 -/
lemma leftFibration_pullback_isRightCofinal {E A B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (pullback.fst p f) := by
  obtain ⟨M, j, q, hm, hj, hq, he⟩ := hf.exists_anodyne_trivialKan_factorization
  subst f
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := hq
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.fst p q) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_fst p q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q))⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p q) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_rightAnodyne (pullback.snd p q) j hj)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration (pullback.fst p q)
  let e := pullbackLeftPullbackSndIso p q j
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne e.inv
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions e.inv)
  have h := h₀.comp (h₁.comp h₂)
  dsimp only [e] at h
  rw [pullbackLeftPullbackSndIso_inv_fst] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
