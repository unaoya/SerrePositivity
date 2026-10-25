module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactArrowCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPartialColimitPresentation

/-!
概要：compact な閉包内射の任意の小さい余積は、同じ実 Ind 像に属する。
方針：有限部分余積を μ-small 部分余極限の μ-filtered 全表示へ移す。
規約：小さい余積の元の指定全余錐を保ち、任意の像対象の余積閉性はまだ主張しない。
使われ方：共通 filtered 表示を用いた全小余積閉性。
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

/-- 全項が compact な閉包内射なら、元の任意の小さい余積は実像に属する。 -/
lemma indArrowImage_compactCoproduct_colimit_mem
    (edges : I → C _⦋1⦌) (hC : HasSmallColimits C)
    (hbound : IsCardinalChangeBound Cardinal.aleph0 μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    {B : Type u}
    (E : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hcompact : ∀ t, Compact.IsKappaCompact.{u, u + 1} μ (E.app _ t))
    (hmem : ∀ t, arrowVertexEdge (E.app _ t) ∈ generatedEdges edges)
    (c : JoinCocone E) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  classical
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  let Y := (ihom (Δ[1] : SSet.{u + 1})).obj C
  have hY : HasSmallColimits Y := functor_hasSmallColimits Δ[1] hC
  obtain ⟨F, d, hd, ⟨hi⟩, hFc, hFs⟩ :=
    compactArrowCoproduct_finitePartialDiagram edges hC hbound E hcompact hmem c hc
  have : IsCardinalFiltered (Finset B) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff (Finset B)).mpr inferInstance
  obtain ⟨P, β, hP, _, hparts, a, ha, hv⟩ :=
    exists_smallPartialColimitPresentation hbound
      (hY.hasSmallKappaFilteredColimits Cardinal.aleph0) d hd
  have := hP
  have himage (t : ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (SmallFilteredPieces Cardinal.aleph0 μ (Finset B)))) _⦋0⦌) :
      IndArrowImageVertex edges G (P.app _ t) := by
    rcases t with ⟨t⟩
    obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective t
    obtain ⟨b, hb, hvertex⟩ := hparts s
    have hbc : Compact.IsKappaCompact.{u, u + 1} μ b.vertex :=
      isMuCompact_smallPosetColimit hbound s.val s.property.2 b hb
        (fun k ↦ hFc (((SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (subsetInclusion s.val))).app _ k))
    have hbs : arrowVertexEdge b.vertex ∈ generatedEdges edges :=
      (stronglySaturatedClosure_stronglySaturated
        (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1
          (nerve s.val) _ b hb
          (fun k ↦ hFs (((SSet.uliftFunctor.{u + 1, u}).map
            (nerveMap (subsetInclusion s.val))).app _ k))
    rw [hvertex] at hbc hbs
    exact hcover _ hbc hbs
  let Q := fullSubcomplexLift (IndArrowImageVertex edges G) P himage
  have hQ : Q ≫ indArrowImageInclusion edges G = P := fullSubcomplexLift_ι _ _ _
  have hm : IndArrowImageVertex edges G a.vertex := by
    apply indArrowImage_colimit_mem edges G hC hff hG Q
    simpa only [hQ] using ha
  rw [hv] at hm
  exact (indArrowImageVertex_iff_vertexIso edges G hi).mp hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
