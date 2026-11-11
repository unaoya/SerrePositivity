module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeEraseLeaf

/-!
# 元の有限部分木の葉の除去データ

概要：除く葉・残る親・元の接続辺と除去後の閉性をまとめる。
方針：最大高さの葉と元の根からの親の存在を使う。
規約：接続辺の元の向きのデータを保持する。
使われ方：元の葉を親へ送る自由圏の関手。

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

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T]

structure LeafDeletion (S : Finset Q) where
  leaf : Q
  parent : Q
  leaf_mem : leaf ∈ S
  not_root : (show T from leaf) ≠ Quiver.root T
  parent_mem : parent ∈ S.erase leaf
  edge : (show T from parent) ⟶ (show T from leaf)
  maximum : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsMaximumIn T S leaf
  leaf_property : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf.IsLeafIn S leaf
  remaining_closed : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T (S.erase leaf)

lemma LeafDeletion.card_lt {S : Finset Q} (D : LeafDeletion T S) :
    (S.erase D.leaf).card < S.card := by
  have h := Finset.card_erase_add_one D.leaf_mem
  omega

variable [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma exists_leafDeletion {S : Finset Q} (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S)
    (hne : ∃ x ∈ S, (show T from x) ≠ Quiver.root T) : Nonempty (LeafDeletion T S) := by
  obtain ⟨z, hz, hzr, hm⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_nonroot_maximum T S hne
  obtain ⟨p, e, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.parent_exists T (show T from z) hzr
  exact ⟨
    { leaf := z
      parent := p
      leaf_mem := hz
      not_root := hzr
      parent_mem := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.parent_mem_of_closed T hS hz e
      edge := e
      maximum := hm
      leaf_property := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf.leaf_of_max_height T S z hm
      remaining_closed := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed.erase_max T hS hzr hm }⟩

def chooseLeafDeletion {S : Finset Q} (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S)
    (hne : ∃ x ∈ S, (show T from x) ≠ Quiver.root T) : LeafDeletion T S :=
  Classical.choice (exists_leafDeletion T hS hne)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
