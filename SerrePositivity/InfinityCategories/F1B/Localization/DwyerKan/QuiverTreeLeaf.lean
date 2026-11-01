module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeHeight

/-!
# 最大高さの頂点に接する木の辺の一意性

概要：低い頂点から高い頂点へ向かう対称生成辺は必ず木の辺である。
方針：逆向きの木への所属を高さの式で排除し、入る辺の一意性を使う。
規約：元の対称化 quiver の辺そのものの一意性を回収する。
使われ方：有限頂点集合の最大高さの葉の除去。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma edge_toward_higher {x y : Quiver.Symmetrify Q} (e : x ⟶ y)
    (h : height T (show T from x) ≤ height T (show T from y)) : e ∈ T x y := by
  rcases e with f | f
  · rcases every_edge_in_tree T f with hf | hf
    · exact hf
    · have he := negative_height T f hf
      omega
  · rcases every_edge_in_tree T f with hf | hf
    · have he := positive_height T f hf
      omega
    · exact hf

lemma higher_incoming_unique {x y z : Quiver.Symmetrify Q} (e : x ⟶ z) (f : y ⟶ z)
    (he : height T (show T from x) ≤ height T (show T from z))
    (hf : height T (show T from y) ≤ height T (show T from z)) : x = y ∧ HEq e f := by
  have h := incoming_unique T
    (⟨e, edge_toward_higher T e he⟩ : (show T from x) ⟶ (show T from z))
    (⟨f, edge_toward_higher T f hf⟩ : (show T from y) ⟶ (show T from z))
  obtain ⟨hxy, hhom⟩ := h
  change x = y at hxy
  subst y
  exact ⟨rfl, heq_of_eq (congrArg Subtype.val (eq_of_heq hhom))⟩

end SerrePositivity.EInfinity.Hammock.QuiverTree
