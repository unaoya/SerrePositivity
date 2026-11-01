module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverTreeHeight
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeFiniteLeaf

/-!
# 元の根付き被覆の有限頂点集合の葉

概要：元の被覆の有限集合に葉が存在し、根以外があれば根以外を選べる。
方針：元の高さの最大値と証明済みの木の一意性を使う。
規約：元の根と元の対称生成辺の全データを保持する。
使われ方：全指定 hammock の有限部分木に対する帰納。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma spanningTree_root :
    letI := quiver A
    letI := spanningTreeArborescence A
    Quiver.root (spanningTree A) = (show spanningTree A from root A) := rfl

lemma treeHeight_root : treeHeight A (root A) = 0 := by
  let := quiver A
  let := spanningTreeArborescence A
  exact QuiverTree.height_root (spanningTree A)

lemma exists_finite_leaf (S : Finset (Vertex A)) (hS : S.Nonempty) :
    letI := quiver A
    ∃ z ∈ S, QuiverTree.IsLeafIn S z := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  exact QuiverTree.exists_finite_leaf (spanningTree A) S hS

lemma exists_nonroot_finite_leaf (S : Finset (Vertex A)) (hS : ∃ x ∈ S, x ≠ root A) :
    letI := quiver A
    ∃ z ∈ S, z ≠ root A ∧ QuiverTree.IsLeafIn S z := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  exact QuiverTree.exists_nonroot_finite_leaf (spanningTree A) S hS

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
