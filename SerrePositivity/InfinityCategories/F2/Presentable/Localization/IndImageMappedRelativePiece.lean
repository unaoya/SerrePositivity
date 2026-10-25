module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageRelativePiece

/-!
概要：余極限保存関手の像が実像に属すなら、元の図式の実部分余極限も同じ条件に揃う。
方針：像側の小部分余極限を構成し、元の部分余極限を写して指定余錐と比較する。
規約：元の全図式の部分余錐を返す。使われ方：三角形の辺への制限での相対細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 保存関手の像の所属条件を満たす、元の図式の小部分余極限を実際に構成する。 -/
lemma indArrowImage_exists_mappedSmallPartialPiece
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : HasSmallColimits (indArrowImageCategory edges G))
    (hpres : PreservesSmallColimits (indArrowImageInclusion edges G))
    {T : SSet.{u + 1}} [Quasicategory T] (hT : HasSmallColimits T)
    (H : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C) (hH : PreservesSmallColimits H)
    {J : Type u} [PartialOrder J] [IsCardinalFiltered J μ] [IsKappaFiltered μ (nerve J)]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H).app _ (ULift.up j)))
    (hf : IndArrowImageVertex edges G (H.app _ c.vertex))
    (seed : Set J) (hs : HasCardinalLT seed μ) :
    ∃ P : Set J, seed ⊆ P ∧ HasCardinalLT P μ ∧ IsFiltered P ∧
      ∃ a : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (subsetInclusion P)) ≫ D),
        IsColimitCone a ∧ IndArrowImageVertex edges G (H.app _ a.vertex) := by
  have hfc : IndArrowImageVertex edges G (mapJoinCocone H c).vertex := by
    rw [Ind.mapJoinCocone_vertex]
    exact hf
  obtain ⟨P, hseed, hsmall, hfiltered, b, hb, hm⟩ :=
    indArrowImage_exists_smallPartialPiece hμ edges hC G hG hcompact hcol hpres
      (mapJoinCocone H c) (hH (nerve J) D c hc) hD hfc seed hs
  let E := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (subsetInclusion P)) ≫ D
  obtain ⟨a, ha⟩ := hT (nerve P) E
  have hHa := hH (nerve P) E a ha
  have he : (E ≫ H) = (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (subsetInclusion P)) ≫ (D ≫ H) := Category.assoc _ _ _
  let d := coherentCoconeOfDiagramEq he (mapJoinCocone H a)
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff he _).mp hHa
  have hdv : d.vertex = H.app _ a.vertex :=
    (coherentCoconeOfDiagramEq_vertex he _).trans (Ind.mapJoinCocone_vertex H a)
  have hm' := (indArrowImageVertex_iff_vertexIso edges G (colimitVertexIso b d hb hd)).mp hm
  rw [hdv] at hm'
  exact ⟨P, hseed, hsmall, hfiltered, a, ha, hm'⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
