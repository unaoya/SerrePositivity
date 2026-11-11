module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory

/-!
# 元の列の比較を向きに応じた射の比較へ移す

概要：元の列と両端の比較から、元の圏または反対圏での列の比較を得る。
方針：等式だけの端点移送を異種等式で取り除き、後ろ向きでは反対射を取る。
規約：対象や射の類の性質を追加仮定しない。
使われ方：連結の左右の同方向区間の合成の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

lemma op_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq f.op g.op := by
  cases hA
  cases hB
  have h' := eq_of_heq h
  cases h'
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (op_heq)


lemma forward_arrow_heq {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = .forward) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi) (S.arrow i) := by
  change HEq (eqToHom _ ≫ S.arrow i ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forward_arrow_heq)


lemma backward_arrow_heq {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = .backward) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi) (S.arrow i).op := by
  change HEq (eqToHom _ ≫ S.arrow i ≫ eqToHom _).op _
  simp only [op_comp, eqToHom_op, Category.assoc,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backward_arrow_heq)


/-- 元の列とその両端の比較は、向きを移した後も同じ比較を与える。 -/
lemma arrow_heq_of {w w' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y X' Y' : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w' X' Y') (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i : Fin w.length) (j : Fin w'.length)
    (hi : w.direction i = d) (hj : w'.direction j = d)
    (hs : S.vertex (w.source i) = T.vertex (w'.source j))
    (ht : S.vertex (w.target i) = T.vertex (w'.target j)) (h : HEq (S.arrow i) (T.arrow j)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d T j hj) := by
  cases d
  · exact (forward_arrow_heq S i hi).trans (h.trans (forward_arrow_heq T j hj).symm)
  · exact (backward_arrow_heq S i hi).trans
      ((op_heq hs ht h).trans (backward_arrow_heq T j hj).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (arrow_heq_of)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
