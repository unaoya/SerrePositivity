module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndRestrictionEquivalence

/-!
概要：κ-accessible 圏の小さい生成圏から、Indκ 上の保存的延長を構成する。
方針：F1 の同じ Yoneda に沿う左 Kan 延長と指定単位の回収比較を再利用する。
規約：比較の同値性はここでは結論しない。生成関手を全自然同型で回収する。
使われ方：HTT 5.4.2、compact 生成から Ind 表現への比較関手。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 小さい生成圏の元の関手を回収する、κ-filtered 余極限を保つ Ind 上の延長。 -/
lemma exists_indComparison {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) i) := by
  obtain ⟨G, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension κ hC i
  exact ⟨G, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits κ β hβ,
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtensionRecoveryIso κ β hβ⟩⟩

/-- accessibility の定義の実際の小さい生成圏と、それからの同じ Ind 比較を得る。 -/
lemma IsKappaAccessible.exists_indComparison {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ C),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G ∧
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) i) := by
  obtain ⟨hκ, hC, A, hA, i, hi⟩ := h
  have := hA
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨G, hG, e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison hC i
  exact ⟨A, hA, i, G, hi, hG, e⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaAccessible (exists_indComparison)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
