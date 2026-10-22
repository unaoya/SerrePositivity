module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeTotalPrism
public import SerrePositivity.InfinityCategories.F1.VertexFiberPointIso
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberTransport

/-!
概要：元の指定頂点の包含を、同じ全余錐の頂点 fiber の同型として回収する。
方針：unstraightening の引き戻し fiber 同型と、元の頂点の厳密な等式を合成する。
規約：同型から全空間へ戻す射は元の指定頂点の包含そのもの。
使われ方：宇宙変更後の同じ終点の fiber 比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 指定頂点の元の pointed fiber は、全余錐の右包含上の fiber と同型。 -/
def coconeVertexFiberIso (c : JoinCocone F) :
    vertexFiber pointedSpaceProjection c.vertex ≅
      vertexFiber (leftUnstraighteningProjection c.val)
        (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1}))) :=
  vertexFiberPointIso pointedSpaceProjection (coconeFiberVertex_value c).symm ≪≫
    (leftUnstraighteningFiberIso c.val _).symm

/-- 同型を全空間へ含めると、元の指定頂点の包含を厳密に回収する。 -/
lemma coconeVertexFiberIso_hom_ι (c : JoinCocone F) :
    (coconeVertexFiberIso c).hom ≫ vertexFiberι (leftUnstraighteningProjection c.val)
      (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1}))) =
        coconeFiberVertexInclusion c := by
  apply pullback.hom_ext
  · simp only [coconeVertexFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      leftUnstraighteningFiberIso_inv_ι_fst, vertexFiberPointIso_hom_ι,
      coconeFiberVertexInclusion_pointed]
  · change ((coconeVertexFiberIso c).hom ≫ vertexFiberι _ _) ≫
      leftUnstraighteningProjection c.val =
      coconeFiberVertexInclusion c ≫ leftUnstraighteningProjection c.val
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const,
      coconeFiberVertexInclusion_projection]

end SerrePositivity.InfinityCategories.F2.Compact
