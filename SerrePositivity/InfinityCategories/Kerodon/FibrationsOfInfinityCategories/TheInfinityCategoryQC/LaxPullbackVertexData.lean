module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxPullbackProjections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPathSpace

/-!
概要：lax pullback の頂点を二対象と指定矢印の三つ組へ読む。
方針：矢印圏の頂点を一次単体へ戻して両端の評価式を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：lax pullback の頂点を二対象と指定矢印の三つ組へ読む。
方針：矢印圏の頂点を一次単体へ戻して両端の評価式を使う。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
def intervalFunctorVertexEdgeEquiv (C : SSet.{u}) :
    ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌ ≃ C _⦋1⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C).symm.trans SSet.yonedaEquiv
/-- 概要：lax pullback の頂点を二対象と指定矢印の三つ組へ読む。
方針：矢印圏の頂点を一次単体へ戻して両端の評価式を使う。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
structure LaxPullbackVertexData {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) where
  left : A _⦋0⦌
  right : B _⦋0⦌
  arrow : C _⦋1⦌
  source : C.δ 1 arrow = p.app (Opposite.op ⦋0⦌) left
  target : C.δ 0 arrow = q.app (Opposite.op ⦋0⦌) right
/-- 概要：lax pullback の頂点を二対象と指定矢印の三つ組へ読む。
方針：矢印圏の頂点を一次単体へ戻して両端の評価式を使う。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
lemma LaxPullbackVertexData.ext {A B C : SSet.{u}} {p : A ⟶ C} {q : B ⟶ C}
    {x y : LaxPullbackVertexData p q} (hl : x.left = y.left) (hr : x.right = y.right)
    (ha : x.arrow = y.arrow) : x = y := by
  cases x
  cases y
  cases hl
  cases hr
  cases ha
  rfl
/-- 概要：lax pullback の頂点を二対象と指定矢印の三つ組へ読む。
方針：矢印圏の頂点を一次単体へ戻して両端の評価式を使う。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
def laxPullbackVertexData {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌) : LaxPullbackVertexData p q where
  left := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x
  right := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x
  arrow := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)
  source := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge _).src_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_source p q)
      (Opposite.op ⦋0⦌)) x)
  target := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge _).tgt_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_target p q)
      (Opposite.op ⦋0⦌)) x)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
