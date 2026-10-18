module

public import SerrePositivity.InfinityCategories.F1B.LeftFibrationAnodynePullback
public import SerrePositivity.InfinityCategories.F1B.CofinalFactorizationCriterion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：left fibration に沿う right cofinal な射の引き戻しは right cofinal。
方針：right anodyne と trivial Kan の因子分解を引き戻し、合成と pullback の貼合せを使う。
規約：一般の cocartesian fibration の場合はまだ主張しない。
使われ方：Quillen A の必要性と、coslice の引き戻しの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：left fibration に沿う right cofinal な射の引き戻しは right cofinal。
方針：anodyne・trivial Kan 因子分解の各因子を引き戻し、貼合せ同型で元の第一射影へ戻す。
規約：元の cofinal な射に単射性や quasicategory 性を要求しない。
使われ方：Kerodon Proposition 7.2.3.10 の left fibration の場合。 -/
lemma leftFibration_pullback_isRightCofinal {E A B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (f : A ⟶ B) (hf : IsRightCofinal f) :
    IsRightCofinal (pullback.fst p f) := by
  obtain ⟨M, j, q, hm, hj, hq, he⟩ := hf.exists_anodyne_trivialKan_factorization
  subst f
  have : TrivialKanFibration q := hq
  have : TrivialKanFibration (pullback.fst p q) :=
    ⟨trivialKanFibrations.pullback_fst p q (TrivialKanFibration.mem (p := q))⟩
  have : LeftFibration (pullback.snd p q) :=
    ⟨leftFibrations.pullback_snd p q (LeftFibration.mem (p := p))⟩
  have h₁ := isRightCofinal_of_rightAnodyne _
    (leftFibration_pullback_rightAnodyne (pullback.snd p q) j hj)
  have h₂ := isRightCofinal_of_trivialKanFibration (pullback.fst p q)
  let e := pullbackLeftPullbackSndIso p q j
  have h₀ := isRightCofinal_of_rightAnodyne e.inv
    (MorphismProperty.of_isIso rightAnodyneExtensions e.inv)
  have h := h₀.comp (h₁.comp h₂)
  dsimp only [e] at h
  rw [pullbackLeftPullbackSndIso_inv_fst] at h
  exact h

end SerrePositivity.InfinityCategories
