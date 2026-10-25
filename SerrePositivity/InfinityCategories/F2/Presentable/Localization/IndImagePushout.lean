module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSpanColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageIdentities
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowPushoutFamily
public import SerrePositivity.InfinityCategories.Stable.PushoutComparisonCorners
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingPiZero
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns

/-!
概要：同じ実 Ind 像の元の辺クラスは、元の任意の pushout で保存される。
方針：恒等射二本と元の下辺からなる全 span を実像へ持ち上げ、射圏内の pushout を使う。
規約：元の四角形と上下の指定辺を保持し、局所置換の存在を入力しない。
使われ方：HTT 5.5.4.14 の Ind 像の強飽和性の pushout 条件。
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
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の pushout の下辺が実像に属すれば、元の指定上辺も同じ実像に属す。 -/
lemma indArrowImage_pushout_bottom_top (edges : I → C _⦋1⦌)
    (hC : HasSmallColimits C) (hCμ : IsKappaAccessible μ C)
    (h : IsCardinalChangeBound κ μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hidentity : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
      Compact.IsKappaCompact.{u, u + 1} μ
        ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C) (hR : IsPushoutSquare R)
    (hbottom : IndArrowImageVertex edges G (functorVertex (squareBottomEdge ≫ R))) :
    IndArrowImageVertex edges G (functorVertex (squareTopEdge ≫ R)) := by
  have hid (x : C _⦋0⦌) := indArrowImage_identityArrow edges hC hCμ G hff hG hidentity hcover x
  let e := uliftHornIso.{u, u + 1} 2 0
  let F := e.hom ≫ spanSquareBoundary ≫ arrowPushoutFamily R
  have hF : ∀ v, IndArrowImageVertex edges G (F.app _ v) := by
    intro v
    change IndArrowImageVertex edges G ((arrowPushoutFamily R).app _
      (spanSquareBoundary.app _ (e.hom.app _ v)))
    rcases spanSquareBoundary_vertex_cases (e.hom.app _ v) with hv | hv | hv
    · rw [hv]
      change IndArrowImageVertex edges G ((arrowPushoutFamily R).app _
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0))
      rw [arrowPushoutFamily_vertex_zero]
      simpa only [constantFunctorMap_vertex] using hid (R.app _
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0))
    · rw [hv]
      change IndArrowImageVertex edges G ((arrowPushoutFamily R).app _
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0))
      rw [arrowPushoutFamily_vertex_bottom]
      exact hbottom
    · rw [hv]
      change IndArrowImageVertex edges G ((arrowPushoutFamily R).app _
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1))
      rw [arrowPushoutFamily_vertex_left]
      simpa only [constantFunctorMap_vertex] using hid (R.app _
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1))
  let D := fullSubcomplexLift (IndArrowImageVertex edges G) F hF
  let c := (pushoutCocone (arrowPushoutFamily R)).restrict e.hom
  have hc : IsColimitCone c :=
    (Ind.isColimitCone_iff_restrict_of_precompositionEquivalence e.hom
      (isPrecompositionEquivalence_of_iso e) (pushoutCocone (arrowPushoutFamily R))).mp
        (arrowPushoutFamily_isPushout R hR)
  have hm := indArrowImage_span_colimit_mem edges hC h G hff hG hcompact hcover D c hc
  rw [JoinCocone.vertex_restrict, pushoutCocone_vertex] at hm
  change IndArrowImageVertex edges G ((arrowPushoutFamily R).app _
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)) at hm
  rwa [arrowPushoutFamily_vertex_top] at hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
