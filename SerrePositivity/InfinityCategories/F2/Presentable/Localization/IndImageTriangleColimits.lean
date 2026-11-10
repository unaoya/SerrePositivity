module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleFaces
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCompactTriangles
public import SerrePositivity.InfinityCategories.F2.Presentable.FilteredPartialPresentation

/-!
概要：元の全三角形の filtered 表示に沿い、段階ごとの辺の所属を元の辺へ戻す。
方針：元の指定辺余錐を使い、全部分圏への持ち上げと既証の filtered 閉性を適用する。
規約：段階の所属を揃える同時細分の存在はここでは主張しない。
使われ方：HTT 5.5.4.14 の二対三則の filtered 余極限段。
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
variable {κ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
  (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
  (G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges)
  (hff : IsFullyFaithful G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
include hC hff hG

/-- 元の周囲の図式が全頂点で実像に属すれば、同じ filtered 余極限も実像に属する。 -/
lemma indArrowImage_ambientFiltered_colimit_mem
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hD : ∀ k, IndArrowImageVertex edges G (D.app _ k))
    (c : JoinCocone D) (hc : IsColimitCone c) : IndArrowImageVertex edges G c.vertex := by
  let L := fullSubcomplexLift (IndArrowImageVertex edges G) D hD
  have hL : L ≫ indArrowImageInclusion edges G = D := fullSubcomplexLift_ι _ _ _
  let d := coherentCoconeOfDiagramEq hL.symm c
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff hL.symm c).mp hc
  have hm := indArrowImage_colimit_mem edges G hC hff hG L d hd
  rwa [coherentCoconeOfDiagramEq_vertex] at hm

/-- 三角形のある辺が各段階で実像に属すれば、元の同じ辺も属する。 -/
lemma indArrowImage_triangleFace_colimit_mem
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj C)
    (c : JoinCocone D) (hc : IsColimitCone c) (τ : (Δ[2] : SSet.{u + 1}) ⟶ C)
    (hv : c.vertex = functorVertex τ) (j : Fin 3)
    (hD : ∀ k, IndArrowImageVertex edges G
      (((pre (stdSimplex.δ j)).app C).app _ (D.app _ k))) :
    IndArrowImageVertex edges G (functorVertex (stdSimplex.δ j ≫ τ)) := by
  have hm := indArrowImage_ambientFiltered_colimit_mem edges hC G hff hG
    (D ≫ (pre (stdSimplex.δ j)).app C) hD
    (mapJoinCocone ((pre (stdSimplex.δ j)).app C) c)
    (triangleFace_preservesSmallColimits hC j _ _ c hc)
  rw [Ind.mapJoinCocone_vertex, hv] at hm
  exact hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
