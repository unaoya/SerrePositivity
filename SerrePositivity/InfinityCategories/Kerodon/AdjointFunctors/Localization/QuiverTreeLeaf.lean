module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeHeight

/-!
# 最大高さの頂点に接する木の辺の一意性

概要：低い頂点から高い頂点へ向かう対称生成辺は必ず木の辺である。
方針：逆向きの木への所属を高さの式で排除し、入る辺の一意性を使う。
規約：元の対称化 quiver の辺そのものの一意性を回収する。
使われ方：有限頂点集合の最大高さの葉の除去。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeaf
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma edge_toward_higher {x y : Quiver.Symmetrify Q} (e : x ⟶ y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from y)) : e ∈ T x y := by
  rcases e with f | f
  · rcases _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.every_edge_in_tree T f with hf | hf
    · exact hf
    · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.negative_height T f hf
      omega
  · rcases _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.every_edge_in_tree T f with hf | hf
    · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positive_height T f hf
      omega
    · exact hf

lemma higher_incoming_unique {x y z : Quiver.Symmetrify Q} (e : x ⟶ z) (f : y ⟶ z)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from z))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from y) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from z)) : x = y ∧ HEq e f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.incoming_unique T
    (⟨e, edge_toward_higher T e he⟩ : (show T from x) ⟶ (show T from z))
    (⟨f, edge_toward_higher T f hf⟩ : (show T from y) ⟶ (show T from z))
  obtain ⟨hxy, hhom⟩ := h
  change x = y at hxy
  subst y
  exact ⟨rfl, heq_of_eq (congrArg Subtype.val (eq_of_heq hhom))⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeaf
