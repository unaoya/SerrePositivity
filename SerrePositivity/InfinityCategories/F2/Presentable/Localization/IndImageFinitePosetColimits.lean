module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactPartialColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CoconeFamilyVertices
public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetDiagramPresentation

/-!
概要：compact な全候補を含む実 Ind 像の、有限 poset 余極限閉性を構成する。
方針：元の全図式の単一 filtered 表示を全普遍余錐族へ延長し、余極限同士を交換する。
規約：有限交換の未証明入力は使わず、元の射圏の余完備性と濃度版 compact 閉性を使う。
使われ方：HTT 5.5.4.14 の Ind 像の pushout 閉性の工程。
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
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- Ind の有限 poset 全図式の元の射圏での指定余極限は、同じ実像に入る。 -/
lemma indArrowImage_finitePoset_colimit_mem (edges : I → C _⦋1⦌)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (h : IsCardinalChangeBound κ μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (P : Type u) [PartialOrder P] [Finite P]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ Ind.IndInfinity μ A)
    (c : JoinCocone (D ≫ G ≫ generatedArrowInclusion edges)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  have hP : HasCardinalLT P μ :=
    hasCardinalLT_of_finite P μ (Fact.out : μ.IsRegular).aleph0_le
  let Y := (ihom (Δ[1] : SSet.{u + 1})).obj C
  let T := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := G ≫ generatedArrowInclusion edges
  have hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y := functor_hasSmallColimits Δ[1] hC
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ H := hG.comp
    ((generatedArrowInclusion_preservesSmallColimits hC edges).isKappaAccessibleFunctor μ)
  obtain ⟨J, hJ, hμJ, a, d, hdv, hd⟩ :=
    Ind.indFinitePoset_has_singleFilteredDiagramPresentation μ D
  have := hJ
  have := hμJ
  let R := (SSet.uliftFunctor.{u + 1, u}).map a ≫ Ind.diagramYoneda μ (nerve P) A ≫
    (ihom T).map H
  have hdH : IsColimitCone (mapJoinCocone ((ihom T).map H) d) :=
    functorPostcomp_isKappaAccessible T (Ind.ind_hasSmallKappaFilteredColimits μ A) H hH J _ d hd
  obtain ⟨l, hl⟩ := exists_colimitCoconeFamily R (fun j ↦ hY (nerve P) _)
  let p := l ≫ (relativeInitialVertices (coconeRestriction T Y)).ι
  have hp : p ≫ coconeRestriction T Y = R := hl
  have hrows (j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌) :
      IsColimitCone (kanCoconeFamilyAt p j) := by
    have hj := fullSubcomplexOnVertices_vertex (l.app _ j)
    change InitialBoundaryLifting (coconeRestriction T Y) (p.app _ j) at hj
    rw [← kanCoconeFamilyAt_vertex p j] at hj
    exact isColimitCone_of_initialBoundaryLifting_coconeRestriction _ hj
  have hR (j : J _⦋0⦌) :
      (functorVertexEquiv T Y).symm (R.app _ (ULift.up j)) =
        (SSet.uliftFunctor.{u + 1, u}).map
          ((functorVertexEquiv (nerve P) A).symm (a.app _ j)) ≫ Ind.indYoneda μ A ≫ H := by
    let aj := (functorVertexEquiv (nerve P) A).symm (a.app _ j)
    have haj : functorVertex aj = a.app _ j := (functorVertexEquiv _ A).apply_symm_apply _
    have hvR : R.app _ (ULift.up j) =
        functorVertex ((SSet.uliftFunctor.{u + 1, u}).map aj ≫ Ind.indYoneda μ A ≫ H) := by
      change ((ihom T).map H).app _ ((Ind.diagramYoneda μ (nerve P) A).app _
        (ULift.up (a.app _ j))) = _
      rw [← haj, Ind.diagramYoneda_vertex]
      rfl
    rw [hvR]
    exact (functorVertexEquiv T Y).symm_apply_apply _
  have hterms (j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌) (k : T _⦋0⦌) :
      Compact.IsKappaCompact.{u, u + 1} μ
        ((joinInl T Δ[0] ≫ (kanCoconeFamilyAt p j).val).app _ k) := by
    rw [kanCoconeFamilyAt_diagram p R hp j]
    rcases j with ⟨j⟩
    rcases k with ⟨k⟩
    rw [hR j]
    exact hcompact (((functorVertexEquiv (nerve P) A).symm (a.app _ j)).app _ k)
  have hrowmem (j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌) :
      IndArrowImageVertex edges G (kanCoconeFamilyAt p j).vertex := by
    apply hcover _ (isMuCompact_smallPosetColimit h P hP _ (hrows j) (hterms j))
    apply (stronglySaturatedClosure_stronglySaturated
      (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1 (nerve P)
      (joinInl T Δ[0] ≫ (kanCoconeFamilyAt p j).val) _ (hrows j)
    intro k
    rw [kanCoconeFamilyAt_diagram p R hp j]
    rcases j with ⟨j⟩
    rcases k with ⟨k⟩
    rw [hR j]
    exact fullSubcomplexOnVertices_vertex
      (G.app _ ((Ind.indYoneda μ A).app _ (ULift.up
        (((functorVertexEquiv (nerve P) A).symm (a.app _ j)).app _ k))))
  obtain ⟨b, hb⟩ := exists_pointwiseColimitCocone (hY J) p
  have hbrow := F2.colimitCoconeFamily_completion_isColimit p b hb hrows
  let z := SSet.yonedaEquiv (joinInr T (Δ[0] : SSet.{u + 1}))
  let q := fullSubcomplexLift (IndArrowImageVertex edges G) (p ≫ evaluateFunctorAt z)
    (fun j ↦ (kanCoconeFamilyAt_apex p j) ▸ hrowmem j)
  have hbem : IndArrowImageVertex edges G (F2.functorVertexCocone b.vertex).vertex := by
    rw [functorVertexCocone_apex]
    exact indArrowImage_colimit_mem edges G hC hff hG q
      (F2.evaluateFunctorCocone b z) (hb z)
  let r := F2.reindexFunctorCocone b (joinInl T Δ[0])
  have hr := isColimitCone_functor_of_pointwise r (hb.reindex (joinInl T Δ[0]))
  let r' : JoinCocone R := ⟨r.val, r.property.trans hp⟩
  have hr' : IsColimitCone r' := (isColimitCone_iff_of_coconeMap_eq r' r rfl).mpr hr
  let e := colimitVertexIso r' (mapJoinCocone ((ihom T).map H) d) hr' hdH
  have hv : functorVertex (joinInl T Δ[0] ≫ (F2.functorVertexCocone b.vertex).val) =
      r'.vertex := by
    change functorVertex (joinInl T Δ[0] ≫ (functorVertexEquiv _ Y).symm b.vertex) =
      ((pre (joinInl T Δ[0])).app Y).app _ b.vertex
    apply (functorVertexEquiv _ Y).symm.injective
    change (functorVertexEquiv _ Y).symm ((functorVertexEquiv _ Y)
      (joinInl T Δ[0] ≫ (functorVertexEquiv _ Y).symm b.vertex)) = _
    rw [Equiv.symm_apply_apply, F2.functorVertexMap_precomp]
  have he : FunctorIso (joinInl T Δ[0] ≫ (F2.functorVertexCocone b.vertex).val) (D ≫ H) := by
    change VertexIso (functorVertex _) (functorVertex (D ≫ H))
    rw [hv]
    have hev := Ind.mapJoinCocone_vertex ((ihom T).map H) d
    rw [hdv] at hev
    exact e ≪≫ eqToIso (congrArg HomotopyCategory.mk hev)
  obtain ⟨b', hb', hvb⟩ := exists_colimitCocone_functorIso_sameVertex he
    (F2.functorVertexCocone b.vertex) hbrow
  apply (indArrowImageVertex_iff_vertexIso edges G
    (VertexIso.map (colimitConeIso b' c hb' hc) (sliceUnderProjection (D ≫ H)))).mp
  change IndArrowImageVertex edges G b'.vertex
  rw [hvb]
  exact hbem

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
