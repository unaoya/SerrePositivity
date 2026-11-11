module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost

/-!
概要：小さい生成圏を回収する κ-連続な Ind 比較は、本質的全射である。
方針：元の対象の生成表示と、同じ生成図式の Ind 内の余極限の像を比較する。
規約：対象ごとの生成表示は全余錐。比較関手の充満忠実性は別に証明する。
使われ方：HTT 5.4.2 の compact 生成から Ind 表現への本質全射性。

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


/-- 同じ生成関手を回収し κ-filtered 余極限を保つ比較は、元の全対象を回収する。 -/
lemma indComparison_isEssentiallySurjective {κ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hp : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.HasKappaFilteredGeneratorPresentation κ i x)
    {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ C} (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective G := by
  intro x
  obtain ⟨I, hI, hκ, a, c, hc, hcol⟩ := hp x
  have := hI
  have := hκ
  let D := (SSet.uliftFunctor.{u + 1, u}).map a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasColimit κ D
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (D ≫ G) ((SSet.uliftFunctor.{u + 1, u}).map a ≫ i) := by
    simpa only [D, Category.assoc] using e.precomp ((SSet.uliftFunctor.{u + 1, u}).map a)
  obtain ⟨b, hb, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex he
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G d) (hG I D d hd)
  refine ⟨d.vertex, ⟨?_⟩⟩
  have ev := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso b c hb hcol
  rw [hv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hc] at ev
  exact ev

/-- κ-accessible 圏には、元の生成圏を回収する本質的全射な κ-連続 Ind 比較がある。 -/
lemma IsKappaAccessible.exists_surjective_indComparison {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ C),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G ∧
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) i) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective G := by
  obtain ⟨A, hA, i, G, hi, hG, ⟨e⟩⟩ := h.exists_indComparison
  have := hA
  exact ⟨A, hA, i, G, hi, hG, ⟨e⟩, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indComparison_isEssentiallySurjective hi.presentation hG e⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_surjective_indComparison)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
