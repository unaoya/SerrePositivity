module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverSpanningTree
public import SerrePositivity.EInfinity.Hammock.QuiverTreeLeaf

/-!
# 元の被覆の高さと最大高さでの入る辺の一意性

概要：元の被覆の辺は高さが一つ違う頂点を結ぶ。
方針：証明済みの全域木と薄さを一般の木の補題へ代入する。
規約：元の生成辺と対称生成辺を保持する。
使われ方：有限部分木の葉と元の hammock の変形。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def treeHeight (x : Vertex A) : ℕ := by
  letI := quiver A
  letI := spanningTreeArborescence A
  exact QuiverTree.height (spanningTree A) x

lemma edge_treeHeight :
    letI := quiver A
    ∀ {x y : Vertex A} (_ : x ⟶ y),
      treeHeight A y = treeHeight A x + 1 ∨ treeHeight A x = treeHeight A y + 1 := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  intro x y f
  exact QuiverTree.edge_height (spanningTree A) f

lemma higher_incoming_unique :
    letI := quiver A
    ∀ {x y z : Quiver.Symmetrify (Vertex A)} (e : x ⟶ z) (f : y ⟶ z),
      treeHeight A x ≤ treeHeight A z → treeHeight A y ≤ treeHeight A z →
        x = y ∧ HEq e f := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  intro x y z e f he hf
  exact QuiverTree.higher_incoming_unique (spanningTree A) e f he hf

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
