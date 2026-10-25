module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImage
public import SerrePositivity.InfinityCategories.F2.Presentable.IndComparisonFullyFaithful

/-!
概要：公開された引数分離済みの比較定理から、全生成射を含む accessible な実像を構成。
方針：元の小さい compact 包含の全自然回収を使い、未証明の presentation を渡さない。
規約：実像と生成閉包全体の一致・全小余極限閉性・強飽和性は依然として未証明。
使われ方：HTT 5.5.4.14 の Ind 像の強飽和性の検証の出発点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 全生成射を含み、元の射圏で κ-filtered 余極限に閉じた accessible な実 Ind 像。 -/
lemma exists_generatorContainingAccessibleIndImage (hC : IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ IsKappaAccessible μ C ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges,
          IsFullyFaithful G ∧ IsKappaAccessibleFunctor μ G ∧
          IsKappaAccessible μ (indArrowImageCategory edges G) ∧
          IsKappaAccessibleFunctor μ (indArrowImageInclusion edges G) ∧
          ∀ j : I, IndArrowImageVertex edges G (generatorArrowVertex edges j) := by
  obtain ⟨μ, hμ, hσ, hCμ, A, hA, i, G, hi, hcompact, hG, ⟨e⟩, hgen⟩ :=
    exists_generatorContainingIndComparison hC edges σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  have := hA
  have hff := indComparison_isFullyFaithful_of_compact hi hcompact hG e
  refine ⟨μ, hμ, hσ, hCμ, A, hA, G, hff, hG,
    indArrowImage_isKappaAccessible edges G hff,
    indArrowImageInclusion_isKappaAccessible edges G hC.hasSmallColimits hff hG, ?_⟩
  intro j
  obtain ⟨a, ⟨ha⟩⟩ := hgen j
  exact ⟨(Ind.indYoneda μ A).app _ (ULift.up a),
    ⟨VertexIso.map (FunctorIso.app e (ULift.up a)) (generatedArrowInclusion edges) ≪≫ ha⟩⟩

/-- 同じ正則濃度で compact な閉包内の全射を含む accessible な実像を選べる。 -/
lemma exists_compactCoveringAccessibleIndImage (hC : IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ IsKappaAccessible μ C ∧
      IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges,
          IsFullyFaithful G ∧ IsKappaAccessibleFunctor μ G ∧
          IsKappaAccessible μ (indArrowImageCategory edges G) ∧
          IsKappaAccessibleFunctor μ (indArrowImageInclusion edges G) ∧
          (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
            Compact.IsKappaCompact.{u, u + 1} μ f →
            arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f) ∧
          (∀ j : I, IndArrowImageVertex edges G (generatorArrowVertex edges j)) := by
  obtain ⟨μ, hμ, hσ, hCμ, hArμ, hgen, _⟩ :=
    exists_regular_generatorArrowCardinal hC edges σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A, hA, i, hi, hcompact, hcover⟩ :=
    exists_smallCompactArrowCandidates hC.hasSmallColimits hArμ edges
  have := hA
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_indComparison
    ((generatedArrow_hasSmallColimits hC.hasSmallColimits edges).hasSmallKappaFilteredColimits μ) i
  have hff := indComparison_isFullyFaithful_of_compact hi hcompact hG e
  have hmem (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
      (hf : Compact.IsKappaCompact.{u, u + 1} μ f)
      (hs : arrowVertexEdge f ∈ generatedEdges edges) : IndArrowImageVertex edges G f := by
    obtain ⟨a, ⟨ha⟩⟩ := hcover (compactGeneratedArrowVertex μ edges f hf hs)
    refine ⟨(Ind.indYoneda μ A).app _ (ULift.up a), ⟨?_⟩⟩
    exact VertexIso.map (FunctorIso.app e (ULift.up a) ≪≫ ha)
      (generatedArrowInclusion edges)
  refine ⟨μ, hμ, hσ, hCμ, hArμ, A, hA, G, hff, hG,
    indArrowImage_isKappaAccessible edges G hff,
    indArrowImageInclusion_isKappaAccessible edges G hC.hasSmallColimits hff hG, hmem, ?_⟩
  intro j
  apply hmem _ (hgen j)
  rw [generatorArrowVertex_edge]
  exact subset_stronglySaturatedClosure _ _ (Set.mem_range_self j)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
