module
public import SerrePositivity.InfinityCategories.Core.CatInfinity.EdgeSquareTransport

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeWholeEdgeNaturality

/-!
概要：元の全余錐間の変換を、元の底図式・余錐頂点・余錐変換の可換正方形へ移す。
方針：前合成自然性の四頂点と全一単体を、元の全余錐の厳密な端点式で揃える。
規約：元の代表辺・全余錐・変換頂点を保持し、quasicategory 性は不要。
使われ方：実際の前層余極限頂点の全脚と標準 Kan 脚の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {K X : SSet.{u}} {p r : K ⟶ X} (q : JoinCocone p) (d : JoinCocone r)
  (e : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X))
    (functorVertex q.val) (functorVertex d.val))

/-- 元の全余錐の辺を底へ制限し、元の二つの底図式の端点表示で保持する。 -/
def coconeWholeEdgeBottom :
    SSet.Edge (X := (ihom K).obj X) (functorVertex p) (functorVertex r) :=
  (SSet.Edge.ofTruncated (e.map ((truncation 2).map ((pre (joinInl K Δ[0])).app X)))).ofEq
    (congrArg functorVertex q.property) (congrArg functorVertex d.property)

/-- 元の全余錐の頂点変換を、元の二つの定値頂点図式の端点表示で保持する。 -/
def coconeWholeEdgeTop : SSet.Edge (X := (ihom K).obj X)
    (functorVertex (SSet.const q.vertex)) (functorVertex (SSet.const d.vertex)) :=
  (SSet.Edge.ofTruncated (e.map ((truncation 2).map
    ((pre (SSet.const (coconeRightApexVertex K) : K ⟶ join K Δ[0])).app X)))).ofEq
      (congrArg functorVertex (cocone_const_rightApex q))
      (congrArg functorVertex (cocone_const_rightApex d))

/-- 元の底変換・頂点変換・両余錐変換は、同じ全一単体で可換な正方形を成す。 -/
lemma coconeWholeEdge_square :
    homMk (coconeWholeEdgeBottom q d e).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex d)).toTruncated =
    homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q)).toTruncated ≫
      homMk (coconeWholeEdgeTop q d e).toTruncated := by
  exact F2.homMk_square_transport _ _ _ _
    (coconeWholeEdgeBottom q d e).toTruncated
    (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex d)).toTruncated
    (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q)).toTruncated
    (coconeWholeEdgeTop q d e).toTruncated
    (coconeWholeEdge_domain_naturality q d e)
    (congrArg functorVertex q.property) (congrArg functorVertex d.property)
    (congrArg functorVertex (cocone_const_rightApex q))
    (congrArg functorVertex (cocone_const_rightApex d))
    rfl (coconeDomainHomotopy_postcomp_edge d) (coconeDomainHomotopy_postcomp_edge q) rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
