module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCommonPresentations
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.DiscreteArrowFamilies
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallQuasicategoryColimitCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitAdjunction
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointCoconePreservation

/-!
概要：同じ濃度で小さい離散形状の余積について、実 Ind 像の閉性を構成する。
方針：P-10 で同期した compact 表示を全離散図式族にし、余積の左随伴を適用する。
規約：元の指定全余錐の頂点を結論し、余積閉性を仮定しない。
使われ方：飽和射圏の小生成性の余積工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

private lemma chosenColimitVertex {T Y : SSet.{u + 1}} [Quasicategory Y]
    (hT : ∀ p : T ⟶ Y, HasColimit p) (p : T ⟶ Y) :
    (chosenColimitCocone T Y hT p).vertex =
      (chosenColimitFunctor T Y hT).app _ (functorVertex p) := by
  change (F2.functorVertexCocone
    ((chosenColimitCoconeFamily T Y hT).app _ (functorVertex p))).vertex = _
  exact functorVertexCocone_apex _

/-- compact な行の余積閉性から、同期した全実像対象の余積閉性を組み立てる。 -/
lemma indArrowImage_coproduct_colimit_mem_of_compactRows
    (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    {B : Type u}
    (hrows : ∀ (q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
        (ihom (Δ[1] : SSet.{u + 1})).obj C) (cq : JoinCocone q), IsColimitCone cq →
      (∀ t, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ t)) →
      (∀ t, arrowVertexEdge (q.app _ t) ∈ generatedEdges edges) →
      IndArrowImageVertex edges G cq.vertex)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  let Y := (ihom (Δ[1] : SSet.{u + 1})).obj C
  let T := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B))
  let E := D ≫ indArrowImageInclusion edges G
  let f := fun b ↦ E.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk b)))
  obtain ⟨K, hK, hμK, d, a, hv, ha, hcomp⟩ :=
    indArrowImageFamily_hasCommonCompactPresentation edges hC G hG hcompact f
      (fun b ↦ fullSubcomplexOnVertices_vertex (D.app _ (ULift.up (nerveVertex (Discrete.mk b)))))
  have := hK
  have := hμK
  let dY := fun b ↦ d b ≫ generatedArrowInclusion edges
  let R := discreteArrowFamily dY
  let r := discreteArrowFamilyCocone dY a
  have hr : IsColimitCone r := discreteArrowFamilyCocone_isColimit dY a ha
  have hvR : (functorVertexEquiv T Y).symm r.vertex = E := by
    apply liftedDiscreteDiagram_hom_ext
    intro b
    have he := discreteArrowFamilyCocone_apex_evaluate dY a b
    rw [hv b] at he
    rw [← evaluateFunctorAt_functorVertex]
    change (evaluateFunctorAt _).app _
      ((functorVertexEquiv T Y) ((functorVertexEquiv T Y).symm r.vertex)) = _
    rw [Equiv.apply_symm_apply]
    exact he
  have hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y := functor_hasSmallColimits Δ[1] hC
  let hT := hY (nerve (Discrete B))
  let L := chosenColimitFunctor T Y hT
  have hLr : IsColimitCone (mapJoinCocone L r) :=
    mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
      (chosenColimitAdjunction T Y hT) r hr
  have hstage (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌) :
      IndArrowImageVertex edges G ((R ≫ L).app _ k) := by
    let q := (functorVertexEquiv T Y).symm (R.app _ k)
    let cq := chosenColimitCocone T Y hT q
    have hcq := chosenColimitCocone_isColimit T Y hT q
    have hq (b : B) : q.app _ (ULift.up (nerveVertex (Discrete.mk b))) = (dY b).app _ k := by
      rw [← evaluateFunctorAt_functorVertex]
      change (evaluateFunctorAt _).app _
        ((functorVertexEquiv T Y) ((functorVertexEquiv T Y).symm (R.app _ k))) = _
      rw [Equiv.apply_symm_apply]
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (discreteArrowFamily_evaluate dY b) (Opposite.op ⦋0⦌)) k
    have hqc : ∀ t, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ t) := by
      rintro ⟨t⟩
      obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective t
      cases b with
      | mk b =>
        change Compact.IsKappaCompact.{u, u + 1} μ
          (q.app _ (ULift.up (nerveVertex (Discrete.mk b))))
        rw [hq b]
        exact hcomp b k
    have hqs : ∀ t, arrowVertexEdge (q.app _ t) ∈ generatedEdges edges := by
      rintro ⟨t⟩
      obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective t
      cases b with
      | mk b =>
        change arrowVertexEdge (q.app _ (ULift.up (nerveVertex (Discrete.mk b)))) ∈
          generatedEdges edges
        rw [hq b]
        exact fullSubcomplexOnVertices_vertex ((d b).app _ k)
    have him := hrows q cq hcq hqc hqs
    have hval : cq.vertex = (R ≫ L).app _ k := by
      rw [chosenColimitVertex]
      change L.app _ ((functorVertexEquiv T Y)
        ((functorVertexEquiv T Y).symm (R.app _ k))) = L.app _ (R.app _ k)
      rw [Equiv.apply_symm_apply]
    exact hval ▸ him
  let Z := fullSubcomplexLift (IndArrowImageVertex edges G) (R ≫ L) hstage
  have hz : Z ≫ indArrowImageInclusion edges G = R ≫ L := fullSubcomplexLift_ι _ _ _
  have hm : IndArrowImageVertex edges G (mapJoinCocone L r).vertex := by
    apply indArrowImage_colimit_mem edges G hC hff hG Z
    simpa only [hz] using hLr
  have heq : L.app _ r.vertex = (chosenColimitCocone T Y hT E).vertex := by
    rw [chosenColimitVertex, ← hvR]
    change L.app _ r.vertex = L.app _ ((functorVertexEquiv T Y)
      ((functorVertexEquiv T Y).symm r.vertex))
    rw [Equiv.apply_symm_apply]
  rw [Ind.mapJoinCocone_vertex, heq] at hm
  have hi : VertexIso (chosenColimitCocone T Y hT E).vertex c.vertex :=
    VertexIso.map (colimitConeIso _ c (chosenColimitCocone_isColimit T Y hT E) hc)
      (sliceUnderProjection E)
  exact (indArrowImageVertex_iff_vertexIso edges G hi).mp hm

/-- 同じ濃度で小さい離散形状の元の指定余極限は、実 Ind 像に属する。 -/
lemma indArrowImage_smallCoproduct_colimit_mem
    (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hμ : Cardinal.aleph0 < μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    {B : Type u} (hB : IsKappaSmall μ (nerve (Discrete B)))
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  apply indArrowImage_coproduct_colimit_mem_of_compactRows edges hC G hff hG hcompact
    (B := B) ?_ D c hc
  intro q cq hcq hqc hqs
  apply hcover cq.vertex
  · exact isKappaCompact_smallQuasicategoryColimit_universe hμ
      (nerve (Discrete B)) hB cq hcq hqc
  · exact (stronglySaturatedClosure_stronglySaturated
      (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1
        (nerve (Discrete B)) q cq hcq hqs

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
