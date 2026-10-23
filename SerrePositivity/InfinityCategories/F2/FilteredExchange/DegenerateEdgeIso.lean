module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.InvertibleEdgeIsoEquality

/-!
概要：元の実退化辺の類は、同じ実端点の表示を保持して恒等同型へ戻る。
方針：実辺の二面から両端の等式を回収し、同じ退化辺の類の恒等則を使う。
規約：HEq から端点の等式を推測せず、辺の代表から証明する。
使われ方：左右区間比較の消去式に残る二つの定値辺の除去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実辺が元の点の退化なら、その実始点と実終点は等しい。 -/
lemma degenerateEdge_source_eq_target {Y : SSet.{u}} {a b : Y _⦋0⦌}
    (e : Y.Edge a b) (x : Y _⦋0⦌) (h : e.edge = Y.σ 0 x) : a = b := by
  have ha : a = x := e.src_eq.symm.trans ((congrArg (Y.δ 1) h).trans
    (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) x).src_eq)
  have hb : b = x := e.tgt_eq.symm.trans ((congrArg (Y.δ 0) h).trans
    (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) x).tgt_eq)
  exact ha.trans hb.symm

/-- 元の指定同型の射が実退化辺の類なら、同じ実終点の恒等同型と値まで一致。 -/
lemma vertexIso_heq_refl_of_degenerate_edge {Y : SSet.{u}} {a b : Y _⦋0⦌}
    (c : VertexIso a b) (e : Y.Edge a b)
    (hc : c.hom = SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
    (x : Y _⦋0⦌) (h : e.edge = Y.σ 0 x) :
    HEq c (Iso.refl (SSet.HomotopyCategory.mk b)) := by
  have hb : b = x := e.tgt_eq.symm.trans ((congrArg (Y.δ 0) h).trans
    (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) x).tgt_eq)
  have ha : a = b := degenerateEdge_source_eq_target e x h
  subst a
  subst b
  apply heq_of_eq
  apply Iso.ext
  have he : e = SSet.Edge.ofTruncated
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) x) := by
    apply SSet.Edge.ext
    exact h
  rw [hc, he]
  exact SSet.Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj Y) x

end SerrePositivity.InfinityCategories.F2
