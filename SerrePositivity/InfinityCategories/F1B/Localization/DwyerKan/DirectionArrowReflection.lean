module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DirectionArrowComparison

/-!
# 向きに応じた射の比較から元の列の比較を回収

概要：向きに応じた圏での列の比較を、元の圏での列の比較へ戻す。
方針：前向きでは端点移送を取り除き、後ろ向きでは反対射の単射性を使う。
規約：元の両端の等式を保持し、同型類や局所化へ落とさない。
使われ方：区間合成の比較から全列の自然性を回収する。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Direction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

lemma raw_heq_of_op_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f.op g.op) : HEq f g := by
  cases hA
  cases hB
  exact heq_of_eq (Quiver.Hom.op_inj (eq_of_heq h))

/-- 向きを移した二つの列の比較は、元の同じ列の比較を回収する。 -/
lemma raw_arrow_heq_of {w w' : Word} {X Y X' Y' : C} (S : Zigzag W w X Y)
    (T : Zigzag W w' X' Y') (d : Direction) (i : Fin w.length) (j : Fin w'.length)
    (hi : w.direction i = d) (hj : w'.direction j = d)
    (hs : S.vertex (w.source i) = T.vertex (w'.source j))
    (ht : S.vertex (w.target i) = T.vertex (w'.target j))
    (h : HEq (arrow d S i hi) (arrow d T j hj)) : HEq (S.arrow i) (T.arrow j) := by
  cases d
  · exact (forward_arrow_heq S i hi).symm.trans (h.trans (forward_arrow_heq T j hj))
  · exact raw_heq_of_op_heq hs ht
      ((backward_arrow_heq S i hi).symm.trans (h.trans (backward_arrow_heq T j hj)))

end SerrePositivity.EInfinity.Hammock.Direction
