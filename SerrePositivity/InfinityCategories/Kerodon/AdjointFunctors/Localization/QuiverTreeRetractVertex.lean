module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeafIncident
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver

/-!
# 元の葉を親へ送る有限頂点の写像

概要：元の有限部分木の葉だけを元の親へ送り、残りの頂点を保つ。
方針：葉の除去データに含まれる親の所属を使う。
規約：葉に接する元の全生成辺の両端は同じ頂点へ写る。
使われ方：元の葉の除去による自由圏の関手。

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

def LeafDeletion.retractVertex (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) :=
  if hx : x.val = D.leaf then ⟨D.parent, D.parent_mem⟩
    else ⟨x.val, Finset.mem_erase.mpr ⟨hx, x.property⟩⟩

lemma LeafDeletion.retractVertex_leaf (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (h : x.val = D.leaf) :
    D.retractVertex x = ⟨D.parent, D.parent_mem⟩ := dite_eq_left h

lemma LeafDeletion.retractVertex_of_ne (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (h : x.val ≠ D.leaf) :
    D.retractVertex x = ⟨x.val, Finset.mem_erase.mpr ⟨h, x.property⟩⟩ := dite_eq_right h

lemma LeafDeletion.incident_retract_eq (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (f : x.val ⟶ y.val)
    (h : x.val = D.leaf ∨ y.val = D.leaf) : D.retractVertex x = D.retractVertex y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change x ⟶ y at f
  change x = D.leaf ∨ y = D.leaf at h
  rcases h with h | h
  · subst x
    have he : y = D.parent := (D.outgoing_parent hy f).1
    subst y
    apply Subtype.ext
    simp [LeafDeletion.retractVertex, D.parent_ne_leaf]
  · subst y
    have he : x = D.parent := (D.incoming_parent hx f).1
    subst x
    apply Subtype.ext
    simp [LeafDeletion.retractVertex, D.parent_ne_leaf]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
