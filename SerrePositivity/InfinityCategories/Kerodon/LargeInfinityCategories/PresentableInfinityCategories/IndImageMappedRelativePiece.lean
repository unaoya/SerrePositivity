module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageRelativePiece

/-!
概要：余極限保存関手の像が実像に属すなら、元の図式の実部分余極限も同じ条件に揃う。
方針：像側の小部分余極限を構成し、元の部分余極限を写して指定余錐と比較する。
規約：元の全図式の部分余錐を返す。使われ方：三角形の辺への制限での相対細分。

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


/-- 保存関手の像の所属条件を満たす、元の図式の小部分余極限を実際に構成する。 -/
lemma indArrowImage_exists_mappedSmallPartialPiece
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G))
    {T : SSet.{u + 1}} [Quasicategory T] (hT : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits T)
    (H : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C) (hH : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H)
    {J : Type u} [PartialOrder J] [IsCardinalFiltered J μ] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve J)]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hD : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((D ≫ H).app _ (ULift.up j)))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H.app _ c.vertex))
    (seed : Set J) (hs : HasCardinalLT seed μ) :
    ∃ P : Set J, seed ⊆ P ∧ HasCardinalLT P μ ∧ IsFiltered P ∧
      ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P)) ≫ D),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H.app _ a.vertex) := by
  have hfc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone H c).vertex := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex]
    exact hf
  obtain ⟨P, hseed, hsmall, hfiltered, b, hb, hm⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_exists_smallPartialPiece hμ edges hC G hG hcompact hcol hpres
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone H c) (hH (nerve J) D c hc) hD hfc seed hs
  let E := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P)) ≫ D
  obtain ⟨a, ha⟩ := hT (nerve P) E
  have hHa := hH (nerve P) E a ha
  have he : (E ≫ H) = (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P)) ≫ (D ≫ H) := Category.assoc _ _ _
  let d := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq he (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone H a)
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff he _).mp hHa
  have hdv : d.vertex = H.app _ a.vertex :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex he _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex H a)
  have hm' := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageVertex_iff_vertexIso edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso b d hb hd)).mp hm
  rw [hdv] at hm'
  exact ⟨P, hseed, hsmall, hfiltered, a, ha, hm'⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
