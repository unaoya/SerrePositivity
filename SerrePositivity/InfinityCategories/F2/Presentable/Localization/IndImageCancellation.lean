module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowCancellationFamily
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImagePushout

/-!
概要：元の指定合成三角形で、最初の辺と合成辺が実像に入れば最後の辺も入る。
方針：二本の辺と元の恒等射を頂点とする、射圏内の指定 pushout を使う。
規約：二対三則全体は未証明のままとし、この向きの消去だけを結論する。
使われ方：HTT 5.5.4.14 の実像の強飽和性。
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

/-- 元の最初の辺と合成辺の実像への所属から、元の最後の辺の所属を得る。 -/
lemma indArrowImage_cancel_left (edges : I → C _⦋1⦌)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hCμ : IsKappaAccessible μ C)
    (h : IsCardinalChangeBound κ μ)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hidentity : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
      Compact.IsKappaCompact.{u, u + 1} μ
        ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x))
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (σ : (Δ[2] : SSet.{u + 1}) ⟶ C)
    (hfirst : IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (2 : Fin 3) ≫ σ)))
    (hcomp : IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (1 : Fin 3) ≫ σ))) :
    IndArrowImageVertex edges G (functorVertex (stdSimplex.δ (0 : Fin 3) ≫ σ)) := by
  have hid (x : C _⦋0⦌) := indArrowImage_identityArrow edges hC hCμ G hff hG hidentity hcover x
  let e := uliftHornIso.{u, u + 1} 2 0
  let F := e.hom ≫ spanSquareBoundary ≫ arrowCancellationFamily σ
  have hF : ∀ v, IndArrowImageVertex edges G (F.app _ v) := by
    intro v
    change IndArrowImageVertex edges G ((arrowCancellationFamily σ).app _
      (spanSquareBoundary.app _ (e.hom.app _ v)))
    rcases spanSquareBoundary_vertex_cases (e.hom.app _ v) with hv | hv | hv
    · rw [hv]
      change IndArrowImageVertex edges G ((arrowCancellationFamily σ).app _
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0))
      rw [arrowCancellationFamily_vertex_first]
      exact hfirst
    · rw [hv]
      change IndArrowImageVertex edges G ((arrowCancellationFamily σ).app _
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0))
      rw [arrowCancellationFamily_vertex_identity]
      simpa only [constantFunctorMap_vertex] using
        hid (σ.app _ (stdSimplex.obj₀Equiv.symm (1 : Fin 3)))
    · rw [hv]
      change IndArrowImageVertex edges G ((arrowCancellationFamily σ).app _
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1))
      rw [arrowCancellationFamily_vertex_composite]
      exact hcomp
  let D := fullSubcomplexLift (IndArrowImageVertex edges G) F hF
  let c := (pushoutCocone (arrowCancellationFamily σ)).restrict e.hom
  have hc : IsColimitCone c :=
    (Ind.isColimitCone_iff_restrict_of_precompositionEquivalence e.hom
      (isPrecompositionEquivalence_of_iso e) (pushoutCocone (arrowCancellationFamily σ))).mp
        (arrowCancellationFamily_isPushout σ)
  have hm := indArrowImage_span_colimit_mem edges hC h G hff hG hcompact hcover D c hc
  rw [JoinCocone.vertex_restrict, pushoutCocone_vertex] at hm
  change IndArrowImageVertex edges G ((arrowCancellationFamily σ).app _
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)) at hm
  rwa [arrowCancellationFamily_vertex_last] at hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
