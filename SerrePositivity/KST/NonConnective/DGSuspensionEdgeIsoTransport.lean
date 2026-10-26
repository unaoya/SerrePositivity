module
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices

/-!
概要：B1 懸垂比較の端点固定性を保つ、後合成と辺表示の輸送。
方針：元の区間写像空間の後合成へ指定同型を送り、厳密頂点表示だけを正規化する。
規約：指定比較の像を使い、比較の存在を選び直さない。
使われ方：K-7 c4 の反復比較と K・loop の比較に共通する輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective

/-- 同じ端点固定辺比較を、任意の全単体射と指定した厳密端点表示で後合成する。 -/
def suspensionEdgeIso_post {X Y : SSet.{u}} {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    {e f : X.Edge x y}
    (i : VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f))
    (g : X ⟶ Y) (hx : g.app _ x = x') (hy : g.app _ y = y') :
    VertexIso (intervalMappingVertexOfEdge ((e.map g).ofEq hx hy))
      (intervalMappingVertexOfEdge ((f.map g).ofEq hx hy)) := by
  have h := VertexIso.map i (intervalMappingPostOfEq g x y hx hy)
  rw [intervalMappingPostOfEq_vertex, intervalMappingPostOfEq_vertex] at h
  exact h

/-- 同じ辺の厳密な表示変更だけを指定比較へ輸送する。 -/
def suspensionEdgeIso_ofEq {X : SSet.{u}} {x y : X _⦋0⦌} {e f e' f' : X.Edge x y}
    (i : VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f))
    (he : e = e') (hf : f = f') :
    VertexIso (intervalMappingVertexOfEdge e') (intervalMappingVertexOfEdge f') := by
  subst e' f'
  exact i

/-- 同じ辺成分の厳密等号は、端点固定の恒等比較へ入る。 -/
def suspensionEdgeIso_ofEdgeEq {X : SSet.{u}} {x y : X _⦋0⦌} {e f : X.Edge x y}
    (h : e.edge = f.edge) :
    VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f) := by
  have he : e = f := SSet.Edge.ext h
  subst f
  exact Iso.refl _

/-- 辺成分の表示変更も、同じ指定比較の端点固定性を保つ。 -/
def suspensionEdgeIso_ofEdgeComponents {X : SSet.{u}} {x y : X _⦋0⦌}
    {e f e' f' : X.Edge x y}
    (i : VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f))
    (he : e.edge = e'.edge) (hf : f.edge = f'.edge) :
    VertexIso (intervalMappingVertexOfEdge e') (intervalMappingVertexOfEdge f') :=
  suspensionEdgeIso_ofEq i (SSet.Edge.ext he) (SSet.Edge.ext hf)

end SerrePositivity.KST.NonConnective
