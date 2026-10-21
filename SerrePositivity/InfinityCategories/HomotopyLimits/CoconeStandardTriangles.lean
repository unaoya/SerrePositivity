module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeStandardUnitSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalVertexHomotopy

/-!
概要：標準余錐の単位正方形を、元の合成三角形の長辺の区間同型へ移す。
方針：同じ共役された頂点射の代表を一つ取り、両三角形の類の等式を使う。
規約：入力された合成三角形と両長辺の全一単体を保持する。
使われ方：元の全変換三角形と全余錐作用の比較。
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

/-- 同じ標準頂点間の共役された射を表す、一つの元の辺。 -/
def coconeStandardApexEdge :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (functorVertex (SSet.const q'.vertex)) (functorVertex (SSet.const d'.vertex)) :=
  Classical.choose (homotopyCategory_homMk_surjective _ _ (coconeStandardApexHom i j e))

/-- 同じ選択済み頂点辺の類は、元の両端比較で共役した同じ射。 -/
lemma coconeStandardApexEdge_homMk :
    homMk (coconeStandardApexEdge i j e) = coconeStandardApexHom i j e :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ (coconeStandardApexHom i j e))

/-- 同じ標準単位の正方形の両合成を表す元の三角形の長辺は、区間内で同型。 -/
def coconeStandardUnitCompositeIso
    (l m : SSet.Edge (X := (ihom K).obj X) (functorVertex p)
      (functorVertex (SSet.const d'.vertex)))
    (L : SSet.Truncated.Edge.CompStruct (coconeWholeEdgeBottom q d e).toTruncated
      (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex d')).toTruncated l.toTruncated)
    (M : SSet.Truncated.Edge.CompStruct
      (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q')).toTruncated
      (coconeStandardApexEdge i j e) m.toTruncated) :
    VertexIso (intervalMappingVertexOfEdge l) (intervalMappingVertexOfEdge m) := by
  apply intervalVertexIsoOfHomMkEq
  calc
    homMk l.toTruncated = _ := (homMk_comp_homMk L).symm
    _ = _ := coconeStandardUnit_square i j e
    _ = homMk m.toTruncated := by
      rw [← coconeStandardApexEdge_homMk i j e]
      exact homMk_comp_homMk M

end SerrePositivity.InfinityCategories.HomotopyLimits
