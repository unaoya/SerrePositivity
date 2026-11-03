module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.InvertibleEdgeIsoEquality

/-!
概要：元の二つの指定同型が同じ実辺の類なら、端点の表示によらず値まで一致する。
方針：指定同型の射で元の辺の可逆性を与え、同じ辺の類の同型へ厳密に戻す。
規約：実辺の等式と両端を保持し、新しい代表を選ばない。
使われ方：共通解像上の同型を元の指定精密化の区間像の同型へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 二つの指定同型の元の実辺の代表が等しければ同型の値も型を含めて一致する。 -/
lemma vertexIso_heq_of_edge_representatives {Y : SSet.{u}} {a b a' b' : Y _⦋0⦌}
    (c : VertexIso a b) (d : VertexIso a' b') (e : Y.Edge a b) (f : Y.Edge a' b')
    (hc : c.hom = SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
    (hd : d.hom = SSet.Truncated.HomotopyCategory.homMk f.toTruncated)
    (h : e.edge = f.edge) : HEq c d := by
  have : IsInvertibleEdge (X := Y) e.toTruncated := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
    rw [← hc]
    infer_instance
  have : IsInvertibleEdge (X := Y) f.toTruncated := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk f.toTruncated)
    rw [← hd]
    infer_instance
  have he : c = asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := Iso.ext hc
  have hf : d = asIso (SSet.Truncated.HomotopyCategory.homMk f.toTruncated) := Iso.ext hd
  exact (heq_of_eq he).trans
    ((invertibleEdgeIso_heq_of_edge_eq e f h).trans (heq_of_eq hf).symm)

end SerrePositivity.InfinityCategories.F2
