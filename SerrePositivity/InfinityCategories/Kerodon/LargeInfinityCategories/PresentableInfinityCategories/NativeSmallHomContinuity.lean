module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallHomCompositeContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeSpaceUniverseReflection

/-!
概要：小さい Hom 合成の accessibility と全小極限保存を無条件に回収する。
方針：指定宇宙変更による小さい錐の反映を利用する。
規約：元の Hom 模型と関手を保持し、充満忠実性を追加入力にしない。
使われ方：随伴関手定理の Hom 模型の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：accessible な関手との小さい Hom 合成は、accessible。
方針：元の Hom 対象の compact 濃度を取り、全 Hom 保存を比較して反映する。
規約：濃度は元の宇宙 u に取る。
使われ方：余表現可能性に必要な小さい解関手の accessibility。 -/
lemma smallHomComposite_isAccessible_native {X Y : SSet.{u + 1}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible X)
    (G : Y ⟶ X) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor G) (x : X _⦋0⦌)
    (H : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor (G ≫ H) := by
  obtain ⟨κ, _, hκG⟩ := hG
  obtain ⟨μ, hμ, hκμ, hx⟩ := hX.exists_compactCardinal x κ
  have hGμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G := hκG.of_le hκμ.le
  have h := (hGμ.comp_universe hx).of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomCompositeIso G x H hH)
  exact ⟨μ, hμ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaAccessibleFunctor_of_spaceUniverse_image h⟩

/-- 概要：極限保存関手との小さい Hom 合成は、全小極限を保つ。
方針：元の Hom の全極限保存を比較で移し、同じ指定錐へ反映する。
規約：全ての元の小さい形状を保つ。
使われ方：d3 による Hom 合成の余表現可能性。 -/
lemma smallHomComposite_preservesSmallLimits_native {X Y : SSet.{u + 1}} [Quasicategory X]
    (G : Y ⟶ X) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits G) (x : X _⦋0⦌)
    (H : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits (G ≫ H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallLimits_of_spaceUniverse_image
  intro K D c hc
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.covariantRepresentableInfinity_isLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone G c) (hG K D c hc) x
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.mapJoinCone_universe_comp] at h
  exact h.of_functorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomCompositeIso G x H hH).precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c).val)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
