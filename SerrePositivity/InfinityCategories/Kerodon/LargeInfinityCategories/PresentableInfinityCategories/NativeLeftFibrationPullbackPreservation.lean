module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFibrationPullbackClassification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeLimitFamilyPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackExchangeShape

/-!
概要：大きい三つの分類図式の小さい filtered 余極限保存から、引き戻しの分類図式の保存性を導く。
方針：同じ全極限錐族の三脚を厳密に回収し、実証済みの cospan 交換を適用する。
規約：全空間の引き戻しや関手の accessibility を結論として仮定しない。
使われ方：引き戻し内の対象の共変 Hom の compact 性の判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：一脚 left fibration の引き戻しの分類図式は、三成分と同じ小さい μ-filtered 余極限を保つ。
方針：全分類錐族の各脚の保存性を元の三つの関手から回収し、全頂点へ反映する。
規約：濃度変更の明示的条件を用い、一般有限交換入力を要求しない。
使われ方：引き戻し内の compact 候補の Hom 保存性。 -/
lemma leftFibrationPullbackClassification_preservesKappaFilteredColimits
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {E D B X : SSet.{u + 1}} [Quasicategory X]
    (p : E ⟶ B) (q : D ⟶ B) (e : E ⟶ X) (d : D ⟶ X) (b : B ⟶ X)
    (hp : p ≫ b = e) (hq : q ≫ b = d)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration b] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram e))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram d))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      (@_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram _ _ (pullback.fst p q ≫ e)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativePullbackProjection_leftFibration p q e d b hp hq)) := by
  have : Fact (Cardinal.lift.{u + 1} κ).IsRegular := ⟨(Fact.out : κ.IsRegular).lift⟩
  have : Fact (Cardinal.lift.{u + 1} μ).IsRegular := ⟨(Fact.out : μ.IsRegular).lift⟩
  have hfull := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesKappaFilteredColimits_limitFamily_apex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackLimitFamily p q e d b hp hq)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackLimitFamily_isLimit p q e d b hp hq)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredLimitExchangeShape_cospan h.lift) (fun k ↦ ?_)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackLimitFamily_apex] at hfull
    exact hfull
  · rcases k with ⟨k⟩
    obtain ⟨j, rfl⟩ := ComposableArrows.mk₀_surjective k
    rcases j with ⟨j⟩
    cases j with
    | none =>
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackLimitFamily_base p q e d b hp hq).symm ▸ hb
    | some j =>
      cases j with
      | left =>
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackLimitFamily_left p q e d b hp hq).symm ▸ he
      | right =>
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPullbackLimitFamily_right p q e d b hp hq).symm ▸ hd

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
