module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageTriangleColimits

/-!
概要：元の三角形の既知の二辺の所属が各段階で揃えば、残る辺を実像へ回収する。
方針：compact な段階での二対三則と、元の指定辺の filtered 余極限を接続する。
規約：同時細分の存在は入力に明示されたままであり、一般の二対三則は主張しない。
使われ方：HTT 5.5.4.13 の同時細分を 5.5.4.14 の三方向の結論へ渡す境界。

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

variable {μ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 三角形の辺制限は、元の同じ二単体の面を射圏の頂点として読むもの。 -/
lemma triangleFace_vertex (τ : (Δ[2] : SSet.{u + 1}) ⟶ C) (j : Fin 3) :
    (((pre (stdSimplex.δ j)).app C).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex τ)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (C.δ j (SSet.yonedaEquiv τ))) := by
  have h : stdSimplex.δ j ≫ τ =
      SSet.yonedaEquiv.symm (C.δ j (SSet.yonedaEquiv τ)) := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h

variable (edges : I → C _⦋1⦌) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
  (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f →
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f)
include hcover

private lemma missingFace_mem (s : C _⦋2⦌) (j : Fin 3)
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (C.δ j s))))
    (hknown : ∀ i : Fin 3, i ≠ j → C.δ i s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G) :
    C.δ j s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
  obtain ⟨x, y, z, f, g, h, t, rfl⟩ := SSet.Edge.CompStruct.exists_of_simplex s
  have h₀ : C.δ (0 : Fin 3) t.simplex = g.edge := t.d₀
  have h₁ : C.δ (1 : Fin 3) t.simplex = h.edge := t.d₁
  have h₂ : C.δ (2 : Fin 3) t.simplex = f.edge := t.d₂
  fin_cases j
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (C.δ (0 : Fin 3) t.simplex))) at hj
    change C.δ (0 : Fin 3) t.simplex ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G
    rw [h₀] at hj ⊢
    have hf : f.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
      simpa only [h₂] using hknown 2 (by decide)
    have hh : h.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
      simpa only [h₁] using hknown 1 (by decide)
    have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge)) := by simpa only [h₀] using hj
    have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_cancel_left_of_compact edges G hcover t.toTruncated hf hh hg
    change g.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G at hr
    exact hr
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (C.δ (1 : Fin 3) t.simplex))) at hj
    change C.δ (1 : Fin 3) t.simplex ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G
    rw [h₁] at hj ⊢
    have hf : f.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
      simpa only [h₂] using hknown 2 (by decide)
    have hg : g.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
      simpa only [h₀] using hknown 0 (by decide)
    have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm h.edge)) := by simpa only [h₁] using hj
    have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_comp_of_compact edges G hcover t.toTruncated hf hg hh
    change h.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G at hr
    exact hr
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (C.δ (2 : Fin 3) t.simplex))) at hj
    change C.δ (2 : Fin 3) t.simplex ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G
    rw [h₂] at hj ⊢
    have hg : g.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
      simpa only [h₀] using hknown 0 (by decide)
    have hh : h.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G := by
      simpa only [h₁] using hknown 1 (by decide)
    have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge)) := by simpa only [h₂] using hj
    have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_cancel_right_of_compact edges G hcover t.toTruncated hg hh hf
    change f.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G at hr
    exact hr

/-- 一つの全三角形について、compact な指定結論辺を残る二辺から回収する。 -/
lemma indArrowImage_triangle_missing_of_compact
    (v : ((ihom (Δ[2] : SSet.{u + 1})).obj C) _⦋0⦌) (j : Fin 3)
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (((pre (stdSimplex.δ j)).app C).app _ v))
    (hknown : ∀ i : Fin 3, i ≠ j →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (((pre (stdSimplex.δ i)).app C).app _ v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (((pre (stdSimplex.δ j)).app C).app _ v) := by
  obtain ⟨τ, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] C).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
    (((pre (stdSimplex.δ j)).app C).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex τ)) at hj
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G
    (((pre (stdSimplex.δ j)).app C).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex τ))
  rw [triangleFace_vertex τ j] at hj ⊢
  apply missingFace_mem edges G hcover (SSet.yonedaEquiv τ) j hj
  intro i hi
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (C.δ i (SSet.yonedaEquiv τ))))
  rw [← triangleFace_vertex]
  exact hknown i hi

/-- 同時細分された三角形表示から、元の同じ結論辺の実像所属が従う。 -/
lemma indArrowImage_triangle_missing_of_refinedPresentation
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    {K : SSet.{u}} [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (τ : (Δ[2] : SSet.{u + 1}) ⟶ C)
    (hv : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex τ) (j : Fin 3)
    (hj : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      (((pre (stdSimplex.δ j)).app C).app _ (D.app _ k)))
    (hknown : ∀ k (i : Fin 3), i ≠ j →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (((pre (stdSimplex.δ i)).app C).app _ (D.app _ k))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stdSimplex.δ j ≫ τ)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_triangleFace_colimit_mem edges hC G hff hG D c hc τ hv j
  intro k
  exact indArrowImage_triangle_missing_of_compact edges G hcover (D.app _ k) j (hj k)
    (hknown k)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
