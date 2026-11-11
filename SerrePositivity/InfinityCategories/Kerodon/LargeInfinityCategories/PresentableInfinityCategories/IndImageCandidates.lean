module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImage
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndComparisonFullyFaithful

/-!
概要：公開された引数分離済みの比較定理から、全生成射を含む accessible な実像を構成。
方針：元の小さい compact 包含の全自然回収を使い、未証明の presentation を渡さない。
規約：実像と生成閉包全体の一致・全小余極限閉性・強飽和性は依然として未証明。
使われ方：HTT 5.5.4.14 の Ind 像の強飽和性の検証の出発点。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 全生成射を含み、元の射圏で κ-filtered 余極限に閉じた accessible な実 Ind 像。 -/
lemma exists_generatorContainingAccessibleIndImage (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G) ∧
          ∀ j : I, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges j) := by
  obtain ⟨μ, hμ, hσ, hCμ, A, hA, i, G, hi, hcompact, hG, ⟨e⟩, hgen⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_generatorContainingIndComparison hC edges σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  have := hA
  have hff := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact hi hcompact hG e
  refine ⟨μ, hμ, hσ, hCμ, A, hA, G, hff, hG,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_isKappaAccessible edges G hff,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion_isKappaAccessible edges G hC.hasSmallColimits hff hG, ?_⟩
  intro j
  obtain ⟨a, ⟨ha⟩⟩ := hgen j
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A).app _ (ULift.up a),
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app e (ULift.up a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges) ≪≫ ha⟩⟩

/-- 同じ正則濃度で compact な閉包内の全射を含む accessible な実像を選べる。 -/
lemma exists_compactCoveringAccessibleIndImage (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G) ∧
          (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
            _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f →
            _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f) ∧
          (∀ j : I, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges j)) := by
  obtain ⟨μ, hμ, hσ, hCμ, hArμ, hgen, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_generatorArrowCardinal hC edges σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A, hA, i, hi, hcompact, hcover⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallCompactArrowCandidates hC.hasSmallColimits hArμ edges
  have := hA
  obtain ⟨G, hG, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrow_hasSmallColimits hC.hasSmallColimits edges).hasSmallKappaFilteredColimits μ) i
  have hff := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact hi hcompact hG e
  have hmem (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
      (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f)
      (hs : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f := by
    obtain ⟨a, ⟨ha⟩⟩ := hcover (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrowVertex μ edges f hf hs)
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A).app _ (ULift.up a), ⟨?_⟩⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app e (ULift.up a) ≪≫ ha)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges)
  refine ⟨μ, hμ, hσ, hCμ, hArμ, A, hA, G, hff, hG,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_isKappaAccessible edges G hff,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion_isKappaAccessible edges G hC.hasSmallColimits hff hG, hmem, ?_⟩
  intro j
  apply hmem _ (hgen j)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex_edge]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.subset_stronglySaturatedClosure _ _ (Set.mem_range_self j)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
