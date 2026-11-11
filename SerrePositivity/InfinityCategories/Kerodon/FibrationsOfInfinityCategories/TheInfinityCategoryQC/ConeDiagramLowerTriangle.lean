module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeDiagramUpperTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyLowerTriangle

/-!
概要：図式側の比較正方形の下側の三角形と三辺。
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

/-- 概要：元の始域・終域と比較先の終域が張る指定三角形。
方針：指定円柱の面と錐の図式上の固定条件を使う。
規約：元の一次・二次単体を保持する。
使われ方：三つの比較三単体で同じ図式側の対角射を使う。 -/
def coneDiagramLowerTriangle {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) {x y : K _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj K) x y) : X _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower G.h ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app (Opposite.op ⦋1⦌) e.edge)
/-- 概要：最後の辺は終域の比較辺。
方針：指定円柱の面と錐の図式上の固定条件を使う。
規約：元の一次・二次単体を保持する。
使われ方：三つの比較三単体で同じ図式側の対角射を使う。 -/
lemma coneDiagramLowerTriangle_zero {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) {x y : K _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj K) x y) :
    X.δ 0 (coneDiagramLowerTriangle G e) = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge G y).edge := by
  let a := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K))
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower_zero G a.edge
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K).δ 0 a.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app (Opposite.op ⦋0⦌) y := a.tgt_eq
  rw [ht] at h
  exact h
/-- 概要：長辺は同じ対角辺。
方針：指定円柱の面と錐の図式上の固定条件を使う。
規約：元の一次・二次単体を保持する。
使われ方：三つの比較三単体で同じ図式側の対角射を使う。 -/
lemma coneDiagramLowerTriangle_one {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) {x y : K _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj K) x y) :
    X.δ 1 (coneDiagramLowerTriangle G e) = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDiagramDiagonalEdge G e).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower_one G.h _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyDiagonalEdge_simplex G (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)))).symm
/-- 概要：最初の辺は元の図式の指定射。
方針：指定円柱の面と錐の図式上の固定条件を使う。
規約：元の一次・二次単体を保持する。
使われ方：三つの比較三単体で同じ図式側の対角射を使う。 -/
lemma coneDiagramLowerTriangle_two {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (G : SSet.Homotopy c.val d.val) {x y : K _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj K) x y) :
    X.δ 2 (coneDiagramLowerTriangle G e) = p.app (Opposite.op ⦋1⦌) e.edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower_two G _).trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋1⦌)) e.edge)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
