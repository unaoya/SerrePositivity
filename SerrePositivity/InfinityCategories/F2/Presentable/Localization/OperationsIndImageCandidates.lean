module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PresentableIndImageCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.OperationsCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCancellation

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
lemma exists_operationsPresentableIndImage (hC : IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ (μ : Cardinal.{u}) (hμ : μ.IsRegular),
      letI : Fact μ.IsRegular := ⟨hμ⟩
      σ < μ ∧ ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges,
          IsFullyFaithful G ∧ IsKappaAccessibleFunctor μ G ∧
          IsPresentable (indArrowImageCategory edges G) ∧
          PreservesSmallColimits (indArrowImageInclusion edges G) ∧
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
  obtain ⟨κ, μ, hκ, hμ, hσ, hb, hCμ, hArμ, hgen, _, hid⟩ :=
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
  refine ⟨μ, hμ, hσ, A, hA, G, hff, hG,
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
