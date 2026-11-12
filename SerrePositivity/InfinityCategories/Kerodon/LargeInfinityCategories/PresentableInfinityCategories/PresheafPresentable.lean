module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafCompactGenerators
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence

/-!
概要：一般の小さい ∞ 圏上の前層は、小さい compact 生成圏により presentable である。
方針：構成した小さい全部分生成圏に既存の全小余極限を合わせ、同じ Ind 比較も提供する。
規約：accessibility と余極限の存在を実証し、任意の小さい圏の Ind の余完備性は仮定と区別する。
使われ方：presentable ∞ 圏の小さい極限・余極限と随伴関手定理の基礎例。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (C : SSet.{u}) [Quasicategory C]

/-- 概要：元の前層 ∞ 圏は ℵ₀-accessible である。
方針：小さい compact 全部分生成圏と全小余極限の既存の存在定理を組み合わせる。
規約：元の各前層を厳密な頂点とする filtered 全表示を用いる。
使われ方：前層の presentable 性と Ind 表現。 -/
lemma presheaf_isKappaAccessible_aleph0 : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible Cardinal.aleph0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :=
  ⟨Cardinal.isRegular_aleph0, (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits C).hasSmallKappaFilteredColimits _,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorCategory C, inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorInclusion C,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorInclusion_isCompactGenerating C⟩

/-- 概要：一般の小さい ∞ 圏上の空間値前層の ∞ 圏は presentable である。
方針：同じ宇宙の compact 生成による accessibility と全小余極限を合わせる。
規約：モデル圏の instance や生成性の存在入力を追加しない。
使われ方：presentable ∞ 圏の基本例。 -/
lemma presheaf_isPresentable : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :=
  ⟨(presheaf_isKappaAccessible_aleph0 C).isAccessible, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits C⟩

/-- 概要：構成した前層の小さい compact 生成圏の Ind は、元の前層と全同値を持つ。
方針：元の小さい生成関手に accessibility の Ind 比較定理を適用する。
規約：順方向の定義に全充満忠実性や Ind 同値を仮定しない。
使われ方：実際に余完備な小さい Ind 模型の供給。 -/
lemma presheaf_exists_compactGeneratorIndEquivalence :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity Cardinal.aleph0 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorCategory C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)) := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  obtain ⟨G, hG, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison
    ((_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits C).hasSmallKappaFilteredColimits Cardinal.aleph0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorInclusion C)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafCompactGeneratorInclusion_isCompactGenerating C) hG e⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
