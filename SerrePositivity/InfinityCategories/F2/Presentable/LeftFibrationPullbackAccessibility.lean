module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftFibrationPullbackClassification
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitFamilyAccessibility
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackExchangeShape

/-!
概要：三つの分類図式の filtered 余極限保存から、引き戻しの分類図式の保存性を導く。
方針：同じ全極限錐族の三脚を厳密に回収し、実証済みの cospan 交換を適用する。
規約：全空間の引き戻しや関手の accessibility を結論として仮定しない。
使われ方：引き戻し内の対象の共変 Hom の compact 性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：一脚 left fibration の引き戻しの分類図式は、三成分と同じ μ-filtered 余極限を保つ。
方針：全分類錐族の各脚の保存性を元の三つの関手から回収し、全頂点へ反映する。
規約：濃度変更の明示的条件を用い、一般有限交換入力を要求しない。
使われ方：引き戻し内の compact 候補の Hom 保存性。 -/
lemma leftFibrationPullbackClassification_isKappaAccessibleFunctor
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {E D B X : SSet.{u}} [Quasicategory X]
    (p : E ⟶ B) (q : D ⟶ B) (e : E ⟶ X) (d : D ⟶ X) (b : B ⟶ X)
    (hp : p ≫ b = e) (hq : q ≫ b = d)
    [LeftFibration e] [LeftFibration d] [LeftFibration b] [LeftFibration p]
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (leftStraighteningInfinityDiagram e))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (leftStraighteningInfinityDiagram d))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (leftStraighteningInfinityDiagram b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ
      (@leftStraighteningInfinityDiagram _ _ (pullback.fst p q ≫ e)
        (relativePullbackProjection_leftFibration p q e d b hp hq)) := by
  have hfull := isKappaAccessibleFunctor_limitFamily_apex
    (leftFibrationPullbackLimitFamily p q e d b hp hq)
    (leftFibrationPullbackLimitFamily_isLimit p q e d b hp hq)
    (cardinalFilteredLimitExchangeShape_cospan h) (fun k ↦ ?_)
  · rw [leftFibrationPullbackLimitFamily_apex] at hfull
    exact hfull
  · rcases k with ⟨k⟩
    obtain ⟨j, rfl⟩ := ComposableArrows.mk₀_surjective k
    rcases j with ⟨j⟩
    cases j with
    | none =>
      exact (leftFibrationPullbackLimitFamily_base p q e d b hp hq).symm ▸ hb
    | some j =>
      cases j with
      | left =>
        exact (leftFibrationPullbackLimitFamily_left p q e d b hp hq).symm ▸ he
      | right =>
        exact (leftFibrationPullbackLimitFamily_right p q e d b hp hq).symm ▸ hd

end SerrePositivity.InfinityCategories.F2.Presentable
