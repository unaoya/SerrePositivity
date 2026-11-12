module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjunctionFromSmallHomModels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightAdjointAccessibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits

/-!
概要：指定宇宙反映界面を用いる presentable 圏の右随伴関手判定。
方針：小さい Hom 模型の余表現可能性で存在を構成し、全 Hom 族で accessibility を戻す。
規約：宇宙変更の充満忠実性を明示し、その無条件の供給は別の所有界面に残す。
使われ方：Compact の反映界面を適用して HTT 5.5.2.9 の必要十分条件を閉じる。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：宇宙反映界面の下で、presentable 圏の右随伴は accessible な小極限保存関手と同値。
方針：必要方向は右随伴の保存と Hom 濃度、十分方向は小さい Hom 模型の余表現を使う。
規約：指定宇宙変更の充満忠実性を明示し、無条件の判定とは区別する。
使われ方：所有レーンから反映界面を供給した後の最終接続。 -/
lemma exists_leftAdjoint_iff_accessible_preservesLimits_of_spaceUniverseFullyFaithful
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (R : D ⟶ C) :
    (∃ L : C ⟶ D, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor R ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits R := by
  constructor
  · rintro ⟨L, ⟨a⟩⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible_of_spaceUniverseFullyFaithful hU
      hC.isAccessible hD.isAccessible a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.adjunction_preservesSmallLimits a⟩
  · rintro ⟨hRa, hRl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_of_accessible_limitPreserving_HomModels R
      hD.isAccessible hD.hasSmallLimits
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_limitPreservingHomModels_of_spaceUniverseFullyFaithful
        hU hC.isAccessible R hRa hRl)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
