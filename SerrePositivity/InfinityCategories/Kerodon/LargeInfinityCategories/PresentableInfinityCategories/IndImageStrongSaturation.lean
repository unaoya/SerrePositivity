module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageTriangleTwoOfThree
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TriangleOperationsIndImageCandidates

/-!
概要：同じ実 Ind 像の辺クラスの強飽和性を、実際の同時細分から証明する。
方針：可逆辺・pushout・全小余極限と、三角形の三方向の二対三則を接続する。
規約：生成閉包との一致や反射の存在はこの宣言の入力にはしない。
使われ方：HTT 5.5.4.14 の小生成な飽和射圏の presentable 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


private lemma truncatedCompStruct_faceMaps
    {C : SSet.{u + 1}} {x y z : C _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj C) x y}
    {g : Truncated.Edge (X := (truncation 2).obj C) y z}
    {h : Truncated.Edge (X := (truncation 2).obj C) x z} (t : f.CompStruct g h) :
    stdSimplex.δ (0 : Fin 3) ≫ (SSet.yonedaEquiv (X := C) (n := ⦋2⦌)).symm t.simplex = (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm g.edge ∧
    stdSimplex.δ (1 : Fin 3) ≫ (SSet.yonedaEquiv (X := C) (n := ⦋2⦌)).symm t.simplex = (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm h.edge ∧
    stdSimplex.δ (2 : Fin 3) ≫ (SSet.yonedaEquiv (X := C) (n := ⦋2⦌)).symm t.simplex = (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm f.edge := by
  let f' : C.Edge x y := SSet.Edge.ofTruncated f
  let g' : C.Edge y z := SSet.Edge.ofTruncated g
  let h' : C.Edge x z := SSet.Edge.ofTruncated h
  let t' : f'.CompStruct g' h' := t
  refine ⟨?_, ?_, ?_⟩
  · convert SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm t' using 1 <;> rfl
  · convert SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm t' using 1 <;> rfl
  · convert SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm t' using 1 <;> rfl

/-- compact 被覆を持つ実 Ind 像は、全三角形の実同時細分により強飽和である。 -/
lemma indArrowImageEdges_stronglySaturated
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f →
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f)
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G))
    (hids : ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x))
    (hpush : ∀ R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R)) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R)))
    (htri : ∀ τ : (Δ[2] : SSet.{u + 1}) ⟶ C, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasCompactTrianglePosetPresentation μ τ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y e he
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_mem_of_isInvertible edges G hids e he
  · intro R hR he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R)))) at he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R))))
    rw [Equiv.symm_apply_apply] at he ⊢
    exact hpush R hR he
  · intro K E c hc hE
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_arrowVertex_iff edges G c.vertex).mpr
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_ambientSmall_colimit_mem edges G hcol hpres K E
      (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_arrowVertex_iff edges G (E.app _ k)).mp (hE k)) c hc
  · intro x y z f g h t hf hg
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm f.edge)) at hf
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm g.edge)) at hg
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm h.edge))
    obtain ⟨h₀, h₁, h₂⟩ := truncatedCompStruct_faceMaps t
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_triangle_twoOfThree hμ edges hC G hff hG hcompact hcover hcol hpres
      ((SSet.yonedaEquiv (X := C) (n := ⦋2⦌)).symm t.simplex) (htri _) 2 0 1 (by intro i hi; omega)
      (by simpa only [h₂] using hf)
      (by simpa only [h₀] using hg)
    simpa only [h₁] using hm
  · intro x y z f g h t hf hh
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm f.edge)) at hf
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm h.edge)) at hh
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm g.edge))
    obtain ⟨h₀, h₁, h₂⟩ := truncatedCompStruct_faceMaps t
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_triangle_twoOfThree hμ edges hC G hff hG hcompact hcover hcol hpres
      ((SSet.yonedaEquiv (X := C) (n := ⦋2⦌)).symm t.simplex) (htri _) 2 1 0 (by intro i hi; omega)
      (by simpa only [h₂] using hf)
      (by simpa only [h₁] using hh)
    simpa only [h₀] using hm
  · intro x y z f g h t hg hh
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm g.edge)) at hg
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm h.edge)) at hh
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).symm f.edge))
    obtain ⟨h₀, h₁, h₂⟩ := truncatedCompStruct_faceMaps t
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_triangle_twoOfThree hμ edges hC G hff hG hcompact hcover hcol hpres
      ((SSet.yonedaEquiv (X := C) (n := ⦋2⦌)).symm t.simplex) (htri _) 0 1 2 (by intro i hi; omega)
      (by simpa only [h₀] using hg)
      (by simpa only [h₁] using hh)
    simpa only [h₂] using hm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
