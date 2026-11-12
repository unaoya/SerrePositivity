module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable

/-!
概要：小さい Ind 模型の presentable 性に必要な余極限条件を明示し、実際の前層模型に供給する。
方針：既証明の Ind の accessibility と全小余極限を合わせ、前層の compact 生成圏には全同値で供給する。
規約：任意の小さい圏の Ind が無条件に余完備とは主張しない。余極限条件は明示入力である。
使われ方：presentable 圏の Ind 模型による特徴づけと、具体的な前層の余完備 Ind 模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：正則 κ に対し、全小余極限を持つ小さい圏の Indκ は presentable である。
方針：元の Yoneda の compact 生成による accessibility と明示された余完備性を合わせる。
規約：余完備性は Indκ(A) 自体について要求し、A の小ささだけから推論しない。
使われ方：余完備な Ind 模型からの presentable 圏の構成。 -/
lemma indInfinity_isPresentable_of_hasSmallColimits (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (A : SSet.{u}) [Quasicategory A] (h : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible κ A).isAccessible, h⟩

/-- 概要：正則 κ の小さい Ind 模型の presentable 性は、全小余極限の存在と同値である。
方針：accessibility を既存の実証された Ind 定理から供給する。
規約：任意の小さい A について、未証明の余極限存在を自動的に仮定しない。
使われ方：Ind の presentable 性に残る条件の公開界面。 -/
lemma indInfinity_isPresentable_iff_hasSmallColimits (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (A : SSet.{u}) [Quasicategory A] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) :=
  ⟨fun h ↦ h.hasSmallColimits, indInfinity_isPresentable_of_hasSmallColimits κ A⟩

/-- 概要：presentable 圏を κ-compact 生成する小さい圏の Indκ は presentable である。
方針：同じ生成関手から構成した Ind 比較の全同値で presentable 性を戻す。
規約：Ind 自身の余完備性は仮定せず、元の生成性から回収する。
使われ方：小さい compact 生成圏による余完備 Ind 模型の供給。 -/
lemma indInfinity_isPresentable_of_compactGenerating {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison
    (hC.hasSmallColimits.hasSmallKappaFilteredColimits κ) i
  exact hC.of_equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence hi hG e).symm

/-- 概要：構成した前層の小さい compact 生成圏の Ind は、実際に全小余極限を持つ。
方針：構成した元の前層との全同値で、全小余極限を戻す。
規約：この具体的な Ind 模型の余完備性を追加入力にしない。
使われ方：実際に余完備な Ind 模型の基本例。 -/
lemma presheafCompactGeneratorInd_hasSmallColimits (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity Cardinal.aleph0 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorCategory C)) := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_exists_compactGeneratorIndEquivalence C
  exact (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits C).of_equivalence e.symm

/-- 概要：構成した前層の小さい compact 生成圏の Ind は presentable である。
方針：同じ元の Ind と前層との全同値に、前層の presentable 性を渡す。
規約：一般の Ind の余完備性の入力を、この具体的な例には残さない。
使われ方：前層と小さい compact 生成 Ind 模型の presentable な比較。 -/
lemma presheafCompactGeneratorInd_isPresentable (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity Cardinal.aleph0 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorCategory C)) := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_exists_compactGeneratorIndEquivalence C
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isPresentable C).of_equivalence e.symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
