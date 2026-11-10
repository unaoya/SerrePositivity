module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TwoMappedRefinementPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageTriangleRefinement
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleCompactPresentations

/-!
概要：元の compact 三角形表示を実際に同時細分し、実 Ind 像の一般の二対三則を得る。
方針：二つの既知辺を各段で揃え、compact な残る辺を元の指定辺の余極限へ戻す。
規約：同時細分の存在を仮定引数にはしない。使われ方：HTT 5.5.4.14 の実像の強飽和性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 元の全三角形を同時細分し、任意の既知の二辺から残る一般の辺の所属を得る。 -/
lemma indArrowImage_triangle_twoOfThree
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G))
    (τ : (Δ[2] : SSet.{u + 1}) ⟶ C) (hτ : HasCompactTrianglePosetPresentation μ τ)
    (j₀ j₁ j₂ : Fin 3) (hrest : ∀ i : Fin 3, i ≠ j₂ → i = j₀ ∨ i = j₁)
    (hf₀ : IndArrowImageVertex edges G (functorVertex (stdSimplex.δ j₀ ≫ τ)))
    (hf₁ : IndArrowImageVertex edges G (functorVertex (stdSimplex.δ j₁ ≫ τ))) :
    IndArrowImageVertex edges G (functorVertex (stdSimplex.δ j₂ ≫ τ)) := by
  obtain ⟨P, o, hP, hPN, D, c, hv, hc, _, hfaces, _⟩ := hτ
  letI := o
  have := hP
  have := hPN
  have hf₀' : IndArrowImageVertex edges G (((pre (stdSimplex.δ j₀)).app C).app _ c.vertex) := by
    rw [hv]
    exact hf₀
  have hf₁' : IndArrowImageVertex edges G (((pre (stdSimplex.δ j₁)).app C).app _ c.vertex) := by
    rw [hv]
    exact hf₁
  obtain ⟨F, hB, hF₀, hF₁, hF₂, d, hd, hvd⟩ :=
    exists_twoMappedRefinementPresentation hμ edges hC G hG hcompact hcol hpres
      (functor_hasSmallColimits (Δ[2] : SSet.{u + 1}) hC)
      ((pre (stdSimplex.δ j₀)).app C) ((pre (stdSimplex.δ j₁)).app C)
      ((pre (stdSimplex.δ j₂)).app C)
      (triangleFace_preservesSmallColimits hC j₀) (triangleFace_preservesSmallColimits hC j₁)
      (triangleFace_preservesSmallColimits hC j₂) c hc
      (fun k ↦ hfaces (ULift.up k) j₀) (fun k ↦ hfaces (ULift.up k) j₁)
      (fun k ↦ hfaces k j₂) hf₀' hf₁'
  have := hB
  apply indArrowImage_triangle_missing_of_refinedPresentation edges G hcover hC hff hG
    F d hd τ (hvd.trans hv) j₂ hF₂
  intro k i hi
  rcases hrest i hi with rfl | rfl
  · exact hF₀ k
  · exact hF₁ k

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
