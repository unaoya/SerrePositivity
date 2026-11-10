module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactOperationsIndImageCandidates

/-!
概要：presentable な実 Ind 像を、恒等射・pushout・左消去と同時に選ぶ。
方針：恒等射図式も compact 保存となる共通濃度で、実比較を一度だけ選択する。
規約：元の圏と生成族以外の存在仮定を追加しない。二対三則の残りは主張しない。
使われ方：HTT 5.5.4.14 の強飽和性に必要な、同じ実像の検証済み演算を回収する。
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
lemma exists_operationsPresentableIndImage (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges,
          IsFullyFaithful G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G ∧
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
  obtain ⟨κ, μ, hκ, hμ, hσ, _hb, _hCμ, _hend, A, hA, G, hff, hG,
    _hcompact, _hcover, hI, hU, hgen, hids, hpush, hcancel⟩ :=
    exists_compactCoveringOperationsPresentableIndImage hC edges σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  have := hA
  exact ⟨μ, hμ, hσ, A, hA, G, hff, hG, hI, hU, hgen, hids, hpush, hcancel⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
