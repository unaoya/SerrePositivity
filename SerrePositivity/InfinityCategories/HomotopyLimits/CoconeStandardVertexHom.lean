module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeCoconeApexIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeStandardUnitSquare

/-!
概要：元の全余錐脚を頂点圏内で共役し、その定値像を同じ関手圏内の共役射へ照合する。
方針：同じ coslice 比較の頂点同型・元の頂点評価辺・定値 Hom の合成互換を使う。
規約：元の両端比較と全余錐の辺を保持し、自然な比較族を仮定しない。
使われ方：元の実際の余極限脚を標準全空間 Kan 脚と比較する。
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

/-- 元の右頂点評価脚を、同じ元の頂点同型で標準頂点間へ共役した射。 -/
def coconeStandardVertexHom :
    HomotopyCategory.mk (X := X) q'.vertex ⟶ HomotopyCategory.mk (X := X) d'.vertex :=
  (nativeCoconeApexIso i).inv ≫ homMk (coconeWholeEdgeApex q d e).toTruncated ≫
    (nativeCoconeApexIso j).hom

/-- 元の頂点圏内の共役射の定値像は、元の関手圏内の共役射そのもの。 -/
lemma coconeStandardVertexHom_constant :
    constantFunctorHomMap K (coconeStandardVertexHom i j e) = coconeStandardApexHom i j e := by
  rw [coconeStandardVertexHom, constantFunctorHomMap_comp, constantFunctorHomMap_comp,
    nativeCoconeApexIso_constant_inv, nativeCoconeApexIso_constant_hom,
    coconeWholeEdgeApex_constant_hom]
  rfl

/-- 元の頂点圏内の同じ共役射を表す、標準頂点間の一つの辺。 -/
def coconeStandardVertexEdge : SSet.Edge q'.vertex d'.vertex :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective _ _
    (coconeStandardVertexHom i j e)))

/-- 同じ標準頂点間の辺の類は、元の同じ頂点比較で共役した射。 -/
lemma coconeStandardVertexEdge_homMk :
    homMk (coconeStandardVertexEdge i j e).toTruncated = coconeStandardVertexHom i j e :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ (coconeStandardVertexHom i j e))

/-- 元の頂点共役辺の定値辺の類は、元の関手圏内の共役射そのもの。 -/
lemma coconeStandardVertexEdge_constant_hom :
    homMk (constantFunctorEdge (A := K) (coconeStandardVertexEdge i j e).toTruncated) =
      coconeStandardApexHom i j e := by
  rw [← constantFunctorHomMap_homMk, coconeStandardVertexEdge_homMk,
    coconeStandardVertexHom_constant]

/-- 元の頂点圏内の共役辺と、元の底脚・両標準余錐変換の正方形は可換。 -/
lemma coconeStandardVertexUnit_square :
    homMk (coconeWholeEdgeBottom q d e).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex d')).toTruncated =
    homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q')).toTruncated ≫
      homMk (constantFunctorEdge (A := K) (coconeStandardVertexEdge i j e).toTruncated) := by
  rw [coconeStandardVertexEdge_constant_hom]
  exact coconeStandardUnit_square i j e

end SerrePositivity.InfinityCategories.HomotopyLimits
