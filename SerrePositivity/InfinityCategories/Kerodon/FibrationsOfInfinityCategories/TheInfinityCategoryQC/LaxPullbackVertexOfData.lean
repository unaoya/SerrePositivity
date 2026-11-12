module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PullbackSimplex

/-!
概要：二対象と指定矢印の三つ組から lax pullback の頂点を作る。
方針：矢印を関手の頂点へ戻し引き戻しの零単体に持ち上げる。
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

/-- 概要：二対象と指定矢印の三つ組から lax pullback の頂点を作る。
方針：矢印を関手の頂点へ戻し引き戻しの零単体に持ち上げる。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
def laxPullbackVertexOfData {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData p q) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.intervalFunctorVertexEdgeEquiv C).symm x.arrow) (x.left, x.right) (by
      apply Prod.ext
      · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge _).src_eq.symm.trans
          ((congrArg (C.δ 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.intervalFunctorVertexEdgeEquiv C).apply_symm_apply x.arrow)).trans
            x.source)
      · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge _).tgt_eq.symm.trans
          ((congrArg (C.δ 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.intervalFunctorVertexEdgeEquiv C).apply_symm_apply x.arrow)).trans
            x.target))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
