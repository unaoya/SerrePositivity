module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndComparisonEquivalence

/-!
概要：κ-accessible 圏を、小さい ∞ 圏の Indκ と同値として表現する。
方針：定義の compact 生成圏から構成した元の κ-連続比較を、そのまま同値へ束ねる。
規約：同値性・充満忠実性・延長存在は定義のフィールドへ仮定しない。
使われ方：HTT 5.4.2 の accessible 圏の Ind 表現。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- κ-accessible 圏は、元の小さい compact 生成圏からの κ-連続な Ind 同値を持つ。 -/
lemma IsKappaAccessible.exists_indRepresentation {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
        (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ e.hom ∧
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ e.hom) i) := by
  obtain ⟨A, hA, i, G, hi, hG, ⟨e⟩⟩ := h.exists_indComparison
  have := hA
  have : Fact κ.IsRegular := ⟨h.1⟩
  exact ⟨A, hA, i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence hi hG e, hi, hG, ⟨e⟩⟩

/-- κ-accessibility の定義から、小さい ∞ 圏の Indκ との全 ∞ 圏同値を得る。 -/
lemma IsKappaAccessible.exists_indEquivalence {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C) := by
  obtain ⟨A, hA, i, e, _, _, _⟩ := h.exists_indRepresentation
  exact ⟨A, hA, ⟨e⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.3.6" (partial := direction) "仮定：accessible な小準圏 C（HTT と一致）。結論：C は idempotent complete（同値の必要方向と一致）。一般の accessible C の実 Ind 模型の冪等完備性を同じ全同値で戻す。小 idempotent complete C の accessibility、およびそこからの任意の関手の accessibility は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible.exists_indEquivalence
