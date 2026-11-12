module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyDiagonalEdge

/-!
概要：図式側の指定円柱の対角辺。
方針：形状の指定辺を join の右包含で写して円柱に適用する。
規約：図式の射と比較の一次単体を変更しない。
使われ方：中央と最後の比較三単体の指定同型の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：元の図式の始域から比較先の図式の終域への対角辺。
方針：指定円柱の面と錐の図式上の固定条件を使う。
規約：元の一次・二次単体を保持する。
使われ方：三つの比較三単体で同じ図式側の対角射を使う。 -/
def coneDiagramDiagonalEdge {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) {x y : K _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj K) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (p.app (Opposite.op ⦋0⦌) x) (q.app (Opposite.op ⦋0⦌) y) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyDiagonalEdge G (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)))).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyDiagonalEdge G _).src_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) x)
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyDiagonalEdge G _).tgt_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app d.property (Opposite.op ⦋0⦌)) y)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
