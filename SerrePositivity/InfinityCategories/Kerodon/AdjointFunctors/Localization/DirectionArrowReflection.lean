module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowComparison

/-!
# 向きに応じた射の比較から元の列の比較を回収

概要：向きに応じた圏での列の比較を、元の圏での列の比較へ戻す。
方針：前向きでは端点移送を取り除き、後ろ向きでは反対射の単射性を使う。
規約：元の両端の等式を保持し、同型類や局所化へ落とさない。
使われ方：区間合成の比較から全列の自然性を回収する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

lemma raw_heq_of_op_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f.op g.op) : HEq f g := by
  cases hA
  cases hB
  exact heq_of_eq (Quiver.Hom.op_inj (eq_of_heq h))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (raw_heq_of_op_heq)


/-- 向きを移した二つの列の比較は、元の同じ列の比較を回収する。 -/
lemma raw_arrow_heq_of {w w' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y X' Y' : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w' X' Y') (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i : Fin w.length) (j : Fin w'.length)
    (hi : w.direction i = d) (hj : w'.direction j = d)
    (hs : S.vertex (w.source i) = T.vertex (w'.source j))
    (ht : S.vertex (w.target i) = T.vertex (w'.target j))
    (h : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d T j hj)) : HEq (S.arrow i) (T.arrow j) := by
  cases d
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S i hi).symm.trans (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq T j hj))
  · exact raw_heq_of_op_heq hs ht
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_arrow_heq S i hi).symm.trans (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_arrow_heq T j hj)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (raw_arrow_heq_of)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
