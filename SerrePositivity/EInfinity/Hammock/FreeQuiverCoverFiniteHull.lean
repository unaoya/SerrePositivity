module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverFiniteLeaf
public import SerrePositivity.EInfinity.Hammock.QuiverTreeLeafDeletion

/-!
# 元の根付き被覆の有限包と葉の除去

概要：元の被覆の任意の有限頂点集合を根に閉じた有限部分木で包む。
方針：証明済みの測地木の根からの有限射列の和を使う。
規約：根・元の頂点・元の親の接続辺を保持する。
使われ方：元の被覆の hammock の有限部分木による可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def finiteHull (S : Finset (Vertex A)) : Finset (Vertex A) := by
  letI := quiver A
  letI := spanningTreeArborescence A
  exact QuiverTree.rootHull (spanningTree A) S

lemma subset_finiteHull (S : Finset (Vertex A)) : S ⊆ finiteHull A S := by
  let := quiver A
  let := spanningTreeArborescence A
  exact QuiverTree.subset_rootHull (spanningTree A) S

lemma finiteHull_root (S : Finset (Vertex A)) : root A ∈ finiteHull A S := by
  let := quiver A
  let := spanningTreeArborescence A
  exact QuiverTree.rootHull_root (spanningTree A) S

lemma finiteHull_empty : finiteHull A ∅ = {root A} := by
  let := quiver A
  let := spanningTreeArborescence A
  exact QuiverTree.rootHull_empty (spanningTree A)

lemma finiteHull_closed (S : Finset (Vertex A)) :
    letI := quiver A
    letI := spanningTreeArborescence A
    QuiverTree.RootClosed (spanningTree A) (finiteHull A S) := by
  let := quiver A
  let := spanningTreeArborescence A
  exact QuiverTree.rootHull_closed (spanningTree A) S

lemma finiteHull_mono {S R : Finset (Vertex A)} (h : S ⊆ R) : finiteHull A S ⊆ finiteHull A R := by
  let := quiver A
  let := spanningTreeArborescence A
  exact QuiverTree.rootHull_mono (spanningTree A) h

def finiteHullLeafDeletion (S : Finset (Vertex A)) (hne : ∃ x ∈ S, x ≠ root A) :
    letI := quiver A
    letI := spanningTreeArborescence A
    QuiverTree.LeafDeletion (spanningTree A) (finiteHull A S) := by
  letI := quiver A
  letI := spanningTreeArborescence A
  letI := groupoid_isThin A
  have hn : ∃ x ∈ finiteHull A S, x ≠ root A := by
    obtain ⟨x, hx, hxr⟩ := hne
    exact ⟨x, subset_finiteHull A S hx, hxr⟩
  exact QuiverTree.chooseLeafDeletion (spanningTree A) (finiteHull_closed A S) hn

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
