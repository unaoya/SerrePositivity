module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceColimitMapping
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndGeneratorMapping

/-!
概要：presentation を要求せず、compact 全部分圏を回収する Ind 比較の充満忠実性を示す。
方針：Yoneda 対象からの比較を compact 性で延長し、始域の Ind 表示で一般の二対象へ延長する。
規約：標的の生成表示は使わず、既存の Ind 比較の宣言は変更しない。
使われ方：P-f の局所化における Ind 比較の充満忠実性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 概要：compact 全部分圏を回収する Ind 比較は、Yoneda 対象からの全写像空間で同値。
方針：始域内の任意対象の Ind 表示と、両側の compact 性による比較の延長を使う。
規約：標的の小さい生成表示を要求しない。
使われ方：presentation を持たない Ind 比較の充満忠実性の第一段階。 -/
lemma indComparison_yoneda_pinchedHomMap_isEquivalence_of_compact
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    (hcompact : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (i.app _ (ULift.up a)))
    {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ C} (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) i) (a : A _⦋0⦌)
    (y : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app _ (ULift.up a)) y) := by
  obtain ⟨I, hI, hκ, b, c, hv, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_generatorPresentation κ A y
  have := hI
  have := hκ
  have hGx := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (κ := κ) (e.app (ULift.up a))).mpr
    (hcompact a)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pinchedHomMap_equivalence_of_compact_colimit G hG
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app _ (ULift.up a))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.indYoneda_isKappaCompact κ a) hGx
    ((SSet.uliftFunctor.{u + 1, u}).map b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A) c hc (by
      intro j
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app _ (ULift.up (b.app (Opposite.op ⦋0⦌) j))))
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indComparison_generator_pinchedHomMap_isEquivalence hff e a
        (b.app (Opposite.op ⦋0⦌) j))
  rwa [hv] at h

/-- 概要：compact 全部分圏を回収する κ-連続な元の Ind 比較は充満忠実。
方針：始点の元の Ind 表示と全 Hom の極限表示で Yoneda 上の比較を延長する。
規約：IsKappaCompactGenerating や標的の presentation を引数に取らない。
使われ方：P-f f2 の Ind 比較の充満忠実性。 -/
lemma indComparison_isFullyFaithful_of_compact
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    (hcompact : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (i.app _ (ULift.up a)))
    {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ C} (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G := by
  intro x y
  obtain ⟨I, hI, hκ, b, c, hv, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_generatorPresentation κ A x
  have := hI
  have := hκ
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pinchedHomMap_equivalence_of_source_colimit G y c hc
    (hG I _ c hc) (by
      rintro ⟨j⟩
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app _ (ULift.up (b.app (Opposite.op ⦋0⦌) j))) y)
      exact indComparison_yoneda_pinchedHomMap_isEquivalence_of_compact
        hff hcompact hG e _ y)
  rwa [hv] at h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
