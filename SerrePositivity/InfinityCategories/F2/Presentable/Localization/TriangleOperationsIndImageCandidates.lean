module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PresentableIndImageCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageRetracts
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleOperationsCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleCompactPresentations
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCancellation

/-!
概要：同じ濃度・同じ実 Ind 像に、compact 被覆・演算・全三角形の同時表示を保持する。
方針：生成辺と三つの全関手圏を同時に濃度調整し、実比較を一回だけ選ぶ。
規約：辺の所属を各三角形の全段階へ揃える細分は、なお未構成。
使われ方：HTT 5.5.4.13–14 の最後の同時部分表示のための全データ。
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
lemma exists_triangleOperationsPresentableIndImage (hC : IsPresentable C)
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
          IsFullyFaithful G ∧ IsKappaAccessibleFunctor μ G ∧
          (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
            ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a))) ∧
          (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
            Compact.IsKappaCompact.{u, u + 1} μ f →
            arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f) ∧
          IsPresentable (indArrowImageCategory edges G) ∧
          PreservesSmallColimits (indArrowImageInclusion edges G) ∧
          (∀ j : I, IndArrowImageVertex edges G (generatorArrowVertex edges j)) ∧
          (∀ x : C _⦋0⦌, IndArrowImageVertex edges G
            ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x)) ∧
          (∀ (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C), IsPushoutSquare R →
            IndArrowImageVertex edges G (functorVertex (squareBottomEdge ≫ R)) →
            IndArrowImageVertex edges G (functorVertex (squareTopEdge ≫ R))) ∧
          (∀ τ : (Δ[2] : SSet.{u + 1}) ⟶ C,
            IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (2 : Fin 3) ≫ τ)) →
            IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (1 : Fin 3) ≫ τ)) →
            IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (0 : Fin 3) ≫ τ))) ∧
          ∀ τ : (Δ[2] : SSet.{u + 1}) ⟶ C, HasCompactTrianglePosetPresentation μ τ := by
  obtain ⟨κ, μ, hκ, hμ, hσ, hb, hCμ, hArμ, hTμ, hgen, hend, hid, hfaces⟩ :=
    exists_triangleOperationsCompactCardinal hC edges σ
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
    indArrowImage_cancel_left edges hC.hasSmallColimits hCμ hb G hff hG hcompact hid hmem,
    triangle_hasCompactPosetPresentation hC.hasSmallColimits hTμ hfaces⟩
  intro j
  apply hmem _ (hgen j)
  rw [generatorArrowVertex_edge]
  exact subset_stronglySaturatedClosure _ _ (Set.mem_range_self j)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
