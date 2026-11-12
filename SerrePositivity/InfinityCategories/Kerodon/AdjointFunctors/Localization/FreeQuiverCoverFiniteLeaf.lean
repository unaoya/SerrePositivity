module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverTreeHeight
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf

/-!
# 元の根付き被覆の有限頂点集合の葉

概要：元の被覆の有限集合に葉が存在し、根以外があれば根以外を選べる。
方針：元の高さの最大値と証明済みの木の一意性を使う。
規約：元の根と元の対称生成辺の全データを保持する。
使われ方：全指定 hammock の有限部分木に対する帰納。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiniteLeaf
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma spanningTree_root :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
    Quiver.root (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) = (show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A from _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A) := rfl

lemma treeHeight_root : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverTreeHeight.treeHeight A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A) = 0 := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height_root (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A)

lemma exists_finite_leaf (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) (hS : S.Nonempty) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∃ z ∈ S, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf.IsLeafIn S z := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf.exists_finite_leaf (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) S hS

lemma exists_nonroot_finite_leaf (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) (hS : ∃ x ∈ S, x ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∃ z ∈ S, z ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf.IsLeafIn S z := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf.exists_nonroot_finite_leaf (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) S hS

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiniteLeaf
