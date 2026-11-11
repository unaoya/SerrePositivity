module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedPrefixLength

/-!
# 元の最初の非指定生成矢による切断の一意性

概要：指定接頭列・最初の非指定矢・残りの射列は、元の射列から一意に回収できる。
方針：消去後の先頭 Total 矢と初期指定長を回収し、元の射列の連結の単射性を使う。
規約：端点の異なる表示は Total の等式と射列の HEq で照合する。
使われ方：元の全縦射に沿う切断の正方形の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

lemma first_split_total {X Y A B A' B' : C} (e : A ⟶ B) (e' : A' ⟶ B')
    (left : Quiver.Path X A) (right : Quiver.Path B Y)
    (left' : Quiver.Path X A') (right' : Quiver.Path B' Y)
    (hl : W.paths left) (hl' : W.paths left') (he : ¬ W e) (he' : ¬ W e')
    (h : left.comp (e.toPath.comp right) = left'.comp (e'.toPath.comp right')) :
    (⟨A, B, e⟩ : Quiver.Total C) = ⟨A', B', e'⟩ := by
  have hw := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W) h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_first_split W left e right hl he,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_first_split W left' e' right' hl' he'] at hw
  exact (List.cons.inj hw).1

lemma first_split_same_arrow {X Y A B : C} (e : A ⟶ B)
    (left left' : Quiver.Path X A) (right right' : Quiver.Path B Y)
    (hl : W.paths left) (hl' : W.paths left') (he : ¬ W e)
    (h : left.comp (e.toPath.comp right) = left'.comp (e.toPath.comp right')) :
    left = left' ∧ right = right' := by
  have hn := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLength W) h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLength_first_split W left e right hl he,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLength_first_split W left' e right' hl' he] at hn
  obtain ⟨hleft, hright⟩ := (Quiver.Path.comp_inj' hn).1 h
  exact ⟨hleft, (Quiver.Path.comp_injective_right e.toPath) hright⟩

lemma first_split_unique {X Y A B A' B' : C} (e : A ⟶ B) (e' : A' ⟶ B')
    (left : Quiver.Path X A) (right : Quiver.Path B Y)
    (left' : Quiver.Path X A') (right' : Quiver.Path B' Y)
    (hl : W.paths left) (hl' : W.paths left') (he : ¬ W e) (he' : ¬ W e')
    (h : left.comp (e.toPath.comp right) = left'.comp (e'.toPath.comp right')) :
    (⟨A, B, e⟩ : Quiver.Total C) = ⟨A', B', e'⟩ ∧ HEq left left' ∧ HEq right right' := by
  have ht := first_split_total W e e' left right left' right' hl hl' he he' h
  refine ⟨ht, ?_⟩
  obtain ⟨hA, hB, heq⟩ := Quiver.Total.mk.inj ht
  subst A'
  subst B'
  have hea : e = e' := eq_of_heq heq
  subst e'
  obtain ⟨hlr, hrr⟩ := first_split_same_arrow W e left left' right right' hl hl' he h
  exact ⟨heq_of_eq hlr, heq_of_eq hrr⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
