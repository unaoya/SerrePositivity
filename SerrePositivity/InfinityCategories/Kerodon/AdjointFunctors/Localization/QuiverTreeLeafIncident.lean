module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeafDeletion

/-!
# 元の葉に接する全生成辺の親の回収

概要：元の葉へ入る辺も出る辺も、他端は元の親に一致する。
方針：元の対称生成辺の一意性を元の接続辺に対して使う。
規約：元の生成辺の向きのデータも保持する。
使われ方：葉に接する生成辺を恒等射へ送る関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S)

lemma LeafDeletion.parent_mem_original : D.parent ∈ S := (Finset.mem_erase.mp D.parent_mem).2

lemma LeafDeletion.parent_ne_leaf : D.parent ≠ D.leaf := (Finset.mem_erase.mp D.parent_mem).1

lemma LeafDeletion.incoming_parent {x : Q} (hx : x ∈ S) (f : x ⟶ D.leaf) :
    x = D.parent ∧ HEq f.toPos D.edge.val :=
  D.leaf_property hx D.parent_mem_original f.toPos D.edge.val

lemma LeafDeletion.outgoing_parent {x : Q} (hx : x ∈ S) (f : D.leaf ⟶ x) :
    x = D.parent ∧ HEq f.toNeg D.edge.val :=
  D.leaf_property hx D.parent_mem_original f.toNeg D.edge.val

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
