module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageCandidates

/-!
概要：実 Ind 像の各元の射には、小さい同じ濃度の filtered な実表示がある。
方針：元の Ind 頂点の単一 Yoneda 表示を送り、最後の同型だけ余錐頂点に移す。
規約：表示の図式全体と元の指定頂点を保持し、単なる対象ごとの像とはしない。
使われ方：HTT 5.5.4.13–14 の二つの実表示の同時細分。

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

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)

/-- 実像の各頂点は、元の全包含を通る一つの小さい filtered 表示の指定頂点である。 -/
lemma indArrowImageVertex_hasPresentation (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    {f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f) :
    ∃ (K : SSet.{u}) (_hK : Quasicategory K) (_hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K)
      (b : K ⟶ A)
      (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (((SSet.uliftFunctor.{u + 1, u}).map b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges)), c.vertex = f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  obtain ⟨a, ⟨ha⟩⟩ := hf
  obtain ⟨K, hK, hκ, b, c, hv, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_generatorPresentation κ A a
  have := hK
  have := hκ
  let H := G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ H := hG.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion_preservesSmallColimits hC edges).isKappaAccessibleFunctor κ)
  have hd := hp K _ c hc
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone H c).vertex f :=
    eqToIso (congrArg HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex H c).trans
      (congrArg (H.app _) hv))) ≪≫ ha
  obtain ⟨d, hd, hvd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone H c) hd he
  exact ⟨K, hK, hκ, b, d, hvd, hd⟩

/-- 周囲で compact な Yoneda 像を持つ実像の表示は、元の全項も周囲で compact。 -/
lemma indArrowImageVertex_hasCompactPresentation (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
    {f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f) :
    ∃ (K : SSet.{u}) (_hK : Quasicategory K) (_hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K)
      (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
      (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges)),
      c.vertex = f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧
      ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
        ((D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ k) := by
  obtain ⟨K, hK, hκ, b, c, hv, hc⟩ := indArrowImageVertex_hasPresentation edges hC G hG hf
  refine ⟨K, hK, hκ, (SSet.uliftFunctor.{u + 1, u}).map b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A ≫ G,
    c, hv, hc, ?_⟩
  rintro ⟨k⟩
  exact hcompact (b.app _ k)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
