module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratorCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.IndComparison

/-!
概要：元の全生成射を含む小さい compact 候補から、飽和射圏への実 Ind 比較を構成する。
方針：構成した小余極限と公開済みの Ind 延長を使い、元の包含を全自然同型で回収する。
規約：比較の充満忠実性・本質的全射性はここでは未主張。
使われ方：P-1 f2、Ind 比較の像の強飽和性の検証に使う実関手。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の全生成射を含む小さい compact 候補の、同じ飽和射圏への実 Ind 延長。 -/
lemma exists_generatorContainingIndComparison (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ IsKappaAccessible μ C ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ generatedArrowCategory edges)
          (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges),
          IsFullyFaithful i ∧
          (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (i.app _ (ULift.up a))) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G ∧ Nonempty (FunctorIso (Ind.indYoneda μ A ≫ G) i) ∧
          ∀ j : I, ∃ a : A _⦋0⦌, Nonempty (VertexIso
            ((i ≫ generatedArrowInclusion edges).app _ (ULift.up a))
            (generatorArrowVertex edges j)) := by
  obtain ⟨μ, hμ, hσ, hCμ, A, hA, i, hi, hcompact, hgen⟩ :=
    exists_generatorContainingCompactArrowCandidates hC edges σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  have := hA
  obtain ⟨G, hG, he⟩ := exists_indComparison
    ((generatedArrow_hasSmallColimits hC.hasSmallColimits edges).hasSmallKappaFilteredColimits μ) i
  exact ⟨μ, hμ, hσ, hCμ, A, hA, i, G, hi, hcompact, hG, he, hgen⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
