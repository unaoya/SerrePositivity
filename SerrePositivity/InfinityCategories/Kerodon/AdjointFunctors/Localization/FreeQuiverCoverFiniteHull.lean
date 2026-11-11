module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiniteLeaf
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeafDeletion

/-!
# 元の根付き被覆の有限包と葉の除去

概要：元の被覆の任意の有限頂点集合を根に閉じた有限部分木で包む。
方針：証明済みの測地木の根からの有限射列の和を使う。
規約：根・元の頂点・元の親の接続辺を保持する。
使われ方：元の被覆の hammock の有限部分木による可縮性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def finiteHull (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) S

lemma subset_finiteHull (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) : S ⊆ finiteHull A S := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subset_rootHull (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) S

lemma finiteHull_root (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A ∈ finiteHull A S := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull_root (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) S

lemma finiteHull_empty : finiteHull A ∅ = {_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A} := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull_empty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A)

lemma finiteHull_closed (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) (finiteHull A S) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull_closed (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) S

lemma finiteHull_mono {S R : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)} (h : S ⊆ R) : finiteHull A S ⊆ finiteHull A R := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) h

def finiteHullLeafDeletion (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) (hne : ∃ x ∈ S, x ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) (finiteHull A S) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  have hn : ∃ x ∈ finiteHull A S, x ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A := by
    obtain ⟨x, hx, hxr⟩ := hne
    exact ⟨x, subset_finiteHull A S hx, hxr⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chooseLeafDeletion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) (finiteHull_closed A S) hn

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
