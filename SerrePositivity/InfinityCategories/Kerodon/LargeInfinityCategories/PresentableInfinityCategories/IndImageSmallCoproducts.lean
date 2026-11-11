module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageCommonPresentations
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiscreteArrowFamilies
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallQuasicategoryColimitCompact
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ChosenColimitAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftAdjointCoconePreservation

/-!
概要：同じ濃度で小さい離散形状の余積について、実 Ind 像の閉性を構成する。
方針：P-10 で同期した compact 表示を全離散図式族にし、余積の左随伴を適用する。
規約：元の指定全余錐の頂点を結論し、余積閉性を仮定しない。
使われ方：飽和射圏の小生成性の余積工程。

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

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

private lemma chosenColimitVertex {T Y : SSet.{u + 1}} [Quasicategory Y]
    (hT : ∀ p : T ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (p : T ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone T Y hT p).vertex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor T Y hT).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.functorVertexCocone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCoconeFamily T Y hT).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))).vertex = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorVertexCocone_apex _

/-- compact な行の余積閉性から、同期した全実像対象の余積閉性を組み立てる。 -/
lemma indArrowImage_coproduct_colimit_mem_of_compactRows
    (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
    {B : Type u}
    (hrows : ∀ (q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
        (ihom (Δ[1] : SSet.{u + 1})).obj C) (cq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cq →
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ t)) →
      (∀ t, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (q.app _ t) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G cq.vertex)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G c.vertex := by
  let Y := (ihom (Δ[1] : SSet.{u + 1})).obj C
  let T := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B))
  let E := D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G
  let f := fun b ↦ E.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)))
  obtain ⟨K, hK, hμK, d, a, hv, ha, hcomp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageFamily_hasCommonCompactPresentation edges hC G hG hcompact f
      (fun b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (D.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)))))
  have := hK
  have := hμK
  let dY := fun b ↦ d b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteArrowFamily dY
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteArrowFamilyCocone dY a
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteArrowFamilyCocone_isColimit dY a ha
  have hvR : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y).symm r.vertex = E := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftedDiscreteDiagram_hom_ext
    intro b
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteArrowFamilyCocone_apex_evaluate dY a b
    rw [hv b] at he
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y).symm r.vertex)) = _
    rw [Equiv.apply_symm_apply]
    exact he
  have hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.functor_hasSmallColimits Δ[1] hC
  let hT := hY (nerve (Discrete B))
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor T Y hT
  have hLr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L r) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitAdjunction T Y hT) r hr
  have hstage (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G ((R ≫ L).app _ k) := by
    let q := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y).symm (R.app _ k)
    let cq := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone T Y hT q
    have hcq := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone_isColimit T Y hT q
    have hq (b : B) : q.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b))) = (dY b).app _ k := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y).symm (R.app _ k))) = _
      rw [Equiv.apply_symm_apply]
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteArrowFamily_evaluate dY b) (Opposite.op ⦋0⦌)) k
    have hqc : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ t) := by
      rintro ⟨t⟩
      obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective t
      cases b with
      | mk b =>
        change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
          (q.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b))))
        rw [hq b]
        exact hcomp b k
    have hqs : ∀ t, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (q.app _ t) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
      rintro ⟨t⟩
      obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective t
      cases b with
      | mk b =>
        change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (q.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)))) ∈
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges
        rw [hq b]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((d b).app _ k)
    have him := hrows q cq hcq hqc hqs
    have hval : cq.vertex = (R ≫ L).app _ k := by
      rw [chosenColimitVertex]
      change L.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y).symm (R.app _ k))) = L.app _ (R.app _ k)
      rw [Equiv.apply_symm_apply]
    exact hval ▸ him
  let Z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G) (R ≫ L) hstage
  have hz : Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G = R ≫ L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L r).vertex := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImage_colimit_mem edges G hC hff hG Z
    simpa only [hz] using hLr
  have heq : L.app _ r.vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone T Y hT E).vertex := by
    rw [chosenColimitVertex, ← hvR]
    change L.app _ r.vertex = L.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T Y).symm r.vertex))
    rw [Equiv.apply_symm_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, heq] at hm
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone T Y hT E).vertex c.vertex :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso _ c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone_isColimit T Y hT E) hc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection E)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageVertex_iff_vertexIso edges G hi).mp hm

/-- 同じ濃度で小さい離散形状の元の指定余極限は、実 Ind 像に属する。 -/
lemma indArrowImage_smallCoproduct_colimit_mem
    (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hμ : Cardinal.aleph0 < μ)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hff : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f →
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f)
    {B : Type u} (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve (Discrete B)))
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G c.vertex := by
  apply indArrowImage_coproduct_colimit_mem_of_compactRows edges hC G hff hG hcompact
    (B := B) ?_ D c hc
  intro q cq hcq hqc hqs
  apply hcover cq.vertex
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hμ
      (nerve (Discrete B)) hB cq hcq hqc
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated
      (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1
        (nerve (Discrete B)) q cq hcq hqs

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
