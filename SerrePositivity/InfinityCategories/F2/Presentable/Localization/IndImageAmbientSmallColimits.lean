module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSmallColimits

/-!
概要：保存包含を持つ実像の全小余極限閉性を、周囲の全図式で使用する。
方針：全部分圏へ持ち上げ、像で選んだ余極限と元の指定余錐を比較する。
規約：元の指定余錐の頂点を保持。使われ方：部分表示の実像への所属。
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

/-- 保存包含を持つ実像に全段が属すれば、元の任意の小余極限も属する。 -/
lemma indArrowImage_ambientSmall_colimit_mem
    {μ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G))
    (K : SSet.{u})
    (E : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hE : ∀ k, IndArrowImageVertex edges G (E.app _ k))
    (c : JoinCocone E) (hc : IsColimitCone c) : IndArrowImageVertex edges G c.vertex := by
  let L := fullSubcomplexLift (IndArrowImageVertex edges G) E hE
  have hL : L ≫ indArrowImageInclusion edges G = E := fullSubcomplexLift_ι _ _ _
  let b := coherentCoconeOfDiagramEq hL.symm c
  have hb : IsColimitCone b := (coherentCoconeOfDiagramEq_isColimit_iff hL.symm c).mp hc
  obtain ⟨d, hd⟩ := hcol K L
  have hUd := hpres K L d hd
  have hm : IndArrowImageVertex edges G
      (mapJoinCocone (indArrowImageInclusion edges G) d).vertex := by
    rw [Ind.mapJoinCocone_vertex]
    exact fullSubcomplexOnVertices_vertex d.vertex
  have e := colimitVertexIso (mapJoinCocone (indArrowImageInclusion edges G) d) b hUd hb
  have hv : b.vertex = c.vertex := coherentCoconeOfDiagramEq_vertex hL.symm c
  rw [hv] at e
  exact (indArrowImageVertex_iff_vertexIso edges G e).mp hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
