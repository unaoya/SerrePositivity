module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PresentableIndImageCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageRetracts
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.OperationsCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCancellation

/-!
概要：compact 被覆・端点の compact 性・演算を、同じ presentable な実 Ind 像に保持する。
方針：演算用の共通濃度と実比較の全データを返し、後続の表示構成で選び直さない。
規約：生成閉包全体との一致・二対三則の残りは結論しない。
使われ方：HTT 5.5.4.13–14 の共通部分表示を組み立てる公開入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 同じ選択で、presentable 性・全恒等射・指定 pushout と左消去を同時に得る。 -/
lemma exists_compactCoveringOperationsPresentableIndImage (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (κ μ : Cardinal.{u}) (_ : κ.IsRegular) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ IsCardinalChangeBound κ μ ∧ IsKappaAccessible μ C ∧
      (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
        Compact.IsKappaCompact.{u, u + 1} μ f → ∀ j : Fin 2,
          Compact.IsKappaCompact.{u, u + 1} μ
            ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)).app _ f)) ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges,
          IsFullyFaithful G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G ∧
          (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
            ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a))) ∧
          (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
            Compact.IsKappaCompact.{u, u + 1} μ f →
            arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f) ∧
          _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (indArrowImageCategory edges G) ∧
          _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G) ∧
          (∀ j : I, IndArrowImageVertex edges G (generatorArrowVertex edges j)) ∧
          (∀ x : C _⦋0⦌, IndArrowImageVertex edges G
            ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x)) ∧
          (∀ (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C), IsPushoutSquare R →
            IndArrowImageVertex edges G (functorVertex (squareBottomEdge ≫ R)) →
            IndArrowImageVertex edges G (functorVertex (squareTopEdge ≫ R))) ∧
          ∀ τ : (Δ[2] : SSet.{u + 1}) ⟶ C,
            IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (2 : Fin 3) ≫ τ)) →
            IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (1 : Fin 3) ≫ τ)) →
            IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (0 : Fin 3) ≫ τ)) := by
  obtain ⟨κ, μ, hκ, hμ, hσ, hb, hCμ, hArμ, hgen, hend, hid⟩ :=
    exists_operationsCompactArrowCardinal hC edges σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A, hA, G, hff, hG, hcompact, hcover⟩ :=
    exists_ambientCompactIndComparison hC.hasSmallColimits hArμ edges
  have := hA
  have hmem (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
      (hf : Compact.IsKappaCompact.{u, u + 1} μ f)
      (hs : arrowVertexEdge f ∈ generatedEdges edges) : IndArrowImageVertex edges G f :=
    hcover (compactGeneratedArrowVertex μ edges f hf hs)
  refine ⟨κ, μ, hκ, hμ, hσ, hb, hCμ, hend, A, hA, G, hff, hG, hcompact, hmem,
    indArrowImage_isPresentable edges hC.hasSmallColimits hb G hff hG hcompact hmem,
    indArrowImageInclusion_preservesSmallColimits
      edges hC.hasSmallColimits hb G hff hG hcompact hmem, ?_,
    indArrowImage_identityArrow edges hC.hasSmallColimits hCμ G hff hG hid hmem,
    indArrowImage_pushout_bottom_top
      edges hC.hasSmallColimits hCμ hb G hff hG hcompact hid hmem,
    indArrowImage_cancel_left edges hC.hasSmallColimits hCμ hb G hff hG hcompact hid hmem⟩
  intro j
  apply hmem _ (hgen j)
  rw [generatorArrowVertex_edge]
  exact subset_stronglySaturatedClosure _ _ (Set.mem_range_self j)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
