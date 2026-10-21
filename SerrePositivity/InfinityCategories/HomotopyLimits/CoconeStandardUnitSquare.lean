module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeCoconeTopIso

/-!
概要：元の全余錐の脚の正方形を、両端で選んだ標準余錐の変換へ移す。
方針：同じ coslice 比較の頂点同型を使い、元の頂点脚を共役する。
規約：底脚・頂点脚・両端の比較代表を固定し、比較の自然性を仮定しない。
使われ方：実際の前層余極限の脚と標準全空間余極限の脚の照合。
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
variable {K X : SSet.{u}} [Quasicategory X] {p r : K ⟶ X}
  {q q' : JoinCocone p} {d d' : JoinCocone r}
  (i : VertexIso (X := sliceUnder p) q q') (j : VertexIso (X := sliceUnder r) d d')
  (e : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X))
    (functorVertex q.val) (functorVertex d.val))

/-- 元の全余錐の頂点脚を、同じ両端比較の頂点同型で標準頂点間へ移す。 -/
def coconeStandardApexHom :
    HomotopyCategory.mk (X := (ihom K).obj X)
      (functorVertex (SSet.const q'.vertex)) ⟶
    HomotopyCategory.mk (X := (ihom K).obj X)
      (functorVertex (SSet.const d'.vertex)) :=
  (nativeCoconeIsoTopIso i).inv ≫
    homMk (coconeWholeEdgeTop q d e).toTruncated ≫ (nativeCoconeIsoTopIso j).hom

/-- 元の底脚と両端の標準余錐変換は、同じ共役された頂点脚について可換。 -/
lemma coconeStandardUnit_square :
    homMk (coconeWholeEdgeBottom q d e).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex d')).toTruncated =
    homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q')).toTruncated ≫
      coconeStandardApexHom i j e := by
  have hi := nativeCoconeFunctorEdge_unit_square (nativeCoconeIsoRepresentative i)
  have hj := nativeCoconeFunctorEdge_unit_square (nativeCoconeIsoRepresentative j)
  change _ = _ ≫ (nativeCoconeIsoTopIso i).hom at hi
  change _ = _ ≫ (nativeCoconeIsoTopIso j).hom at hj
  rw [hj, hi]
  simpa only [coconeStandardApexHom, Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun a => a ≫ (nativeCoconeIsoTopIso j).hom) (coconeWholeEdge_square q d e)

end SerrePositivity.InfinityCategories.HomotopyLimits
